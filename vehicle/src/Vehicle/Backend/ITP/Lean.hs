module Vehicle.Backend.ITP.Lean
  ( LeanOptions (..),
    compileProgToLean,
    writeLeanFile,
  )
where

import Control.Monad.Except (MonadError (..))
import Control.Monad.IO.Class (MonadIO)
import Data.Bifunctor (Bifunctor (..))
import Data.List.NonEmpty (NonEmpty ((:|)))
import Data.List.NonEmpty qualified as NonEmpty
import Data.Maybe (catMaybes)
import Data.Text (Text)
import Data.Text qualified as Text
import Data.Text.Internal.Read qualified as Text.Read
import GHC.Real (denominator, numerator)
import Prettyprinter hiding (hcat, hsep, vcat, vsep)
import Vehicle.Backend.ITP.Core (ComparisonType (..), builtinAppArgs, decideIfPointwiseOrReductionComparison)
import Vehicle.Backend.Prelude
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Compile.Print
import Vehicle.Compile.Sugar.Binders
import Vehicle.Data.AST.Expr.Scoped ()
import Vehicle.Data.Builtin.Core
import Vehicle.Data.Builtin.Decidability
import Vehicle.Data.Builtin.Interface (Accessor (..))
import Vehicle.Data.Code.Interface (ConstTensorArgs (..), IsArgs (..), TensorTypeArgs (..), VectorLitArgs (..), pattern ICons, pattern INatLiteral, pattern INil)
import Vehicle.Data.Real (ExtendedRational (..))
import Vehicle.Data.Tensor
  ( Tensor (..),
    TensorShape,
    foldMapTensor,
    shapeOf,
    toList,
  )
import Vehicle.Data.Universe (UniverseLevel (..))
import Vehicle.Data.Variable.Bound.Context.Name

--------------------------------------------------------------------------------
-- Lean-specific options

data LeanOptions = LeanOptions
  { output :: Maybe FilePath,
    moduleName :: Maybe String
  }

currentPhase :: Doc ()
currentPhase = "compilation to Lean"

compileProgToLean :: (MonadCompile m) => Prog DecidabilityBuiltin -> LeanOptions -> m (Doc a)
compileProgToLean prog options =
  logCompilerSection2 MinDetail currentPhase $ do
    programDoc <- runFreshNameBoundContextT $ compileProg options prog

    let leanProgram =
          unAnnotate
            ( (vsep2 :: [Code] -> Code)
                [ "import Mathlib",
                  "noncomputable section",
                  programDoc
                ]
            )

    return leanProgram

writeLeanFile ::
  (MonadLogger m, MonadIO m, MonadStdIO m) =>
  Maybe FilePath ->
  Doc a ->
  m ()
writeLeanFile = writeResultToFile (Just leanOutputFormat)

leanOutputFormat :: ExternalOutputFormat
leanOutputFormat =
  ExternalOutputFormat
    { formatName = "Lean",
      formatVersion = Nothing,
      commentStyle = Line "--",
      emptyLines = True
    }

--------------------------------------------------------------------------------
-- Debug functions

logEntry :: (MonadLeanCompile m) => Expr DecidabilityBuiltin -> m ()
logEntry e = do
  incrCallDepth
  ctx <- getNameContext
  logDebug MaxDetail $ "compile-entry" <+> prettyExternal (WithContext e ctx)

logExit :: (MonadLeanCompile m) => Code -> m ()
logExit e = do
  logDebug MaxDetail $ "compile-exit " <+> e
  decrCallDepth

--------------------------------------------------------------------------------


type Precedence = Int

-- | Converts a Lean precedence level (e.g. 65 for `+`) into our looseness scale.
leanPrec :: Int -> Maybe Precedence
leanPrec p = Just (1000 - p)

-- | Precedence of constructs that extend as far right as possible
-- (e.g. `fun`, `∀`, `let`, `if`).
loosest :: Maybe Precedence
loosest = Just 1000

functionApplicationPrecedence :: Maybe Precedence
functionApplicationPrecedence = Just 0

data Associativity
  = LeftAssociative
  | RightAssociative
  | NotAssociative

type Code = Doc (Maybe Precedence)

getPrecedence :: Code -> Maybe Precedence
getPrecedence e = maybe (developerError $ "missing annotation for" <+> e) id (docAnn e)

atom :: Code -> Code
atom = annotate Nothing

compileApplication :: (MonadLeanCompile m) => Code -> [Arg DecidabilityBuiltin] -> m Code
compileApplication fun args = do
  (precedence, annDoc) <-
    if null args
      then return (getPrecedence fun, fun)
      else do
        compiledArgs <- traverseArgs compileExpr args
        bracketedArgs <- bracketArgs (replicate (length compiledArgs) functionApplicationPrecedence) compiledArgs
        return (functionApplicationPrecedence, hsep (fun : bracketedArgs))

  return $ annotate precedence annDoc

compileNotationAndArgs ::
  (MonadLeanCompile m) =>
  Associativity ->
  Maybe Precedence ->
  Text ->
  Maybe Text ->
  [Arg DecidabilityBuiltin] ->
  m Code
compileNotationAndArgs associativity precedence op mFn args
  | not (all isExplicit args) = fallback
  | otherwise = do
      compiledArgs <- traverseArgs compileExpr args
      bracketedArgs <- bracketArgs (operandLevels associativity precedence (length compiledArgs)) compiledArgs
      let doc = insertNotationArgs op bracketedArgs
      maybe fallback (return . annotate precedence) doc
  where
    fallback = case mFn of
      Just fn -> compileApplication (pretty fn) args
      Nothing ->
        developerError $
          "Failed to process notation:"
            <+> pretty op
            <+> "with"
            <+> pretty (length args)
            <+> "arguments"

-- | Inserts arguments to a notation
-- e.g. insertNotationArgs "decide ($0 ≤ $1)" [a, b] = Just "decide (a ≤ b)"
-- supports placeholders $0 .. $9, 10 arguments
insertNotationArgs :: Text -> [Code] -> Maybe Code
insertNotationArgs rawOp as = concatWith (<>) <$> go rawOp
  where
    go :: Text -> Maybe [Code]
    go opText = case Text.break (== '$') opText of
      (_, t) | Text.null t -> Just [pretty opText]
      (prefix, t) -> do
        (_, t') <- Text.uncons t
        (nText, maybeSuffix) <- Text.uncons t'
        let n = Text.Read.digitToInt nText
        arg <- atMaybe as n
        suffix <- go maybeSuffix
        return $ pretty prefix : arg : suffix

    atMaybe :: [a] -> Int -> Maybe a
    atMaybe [] _ = Nothing
    atMaybe (x : _) 0 = Just x
    atMaybe (_ : xs) n = atMaybe xs (n - 1)

--------------------------------------------------------------------------------
-- Monad stack

type MonadLeanCompile m =
  ( MonadCompile m,
    MonadNameContext m
  )

--------------------------------------------------------------------------------
-- Program Compilation

compileProg :: (MonadLeanCompile m) => LeanOptions -> Prog DecidabilityBuiltin -> m Code
compileProg opts (Main ds) = do
  decls <- catMaybes <$> traverse (compileDecl opts) ds
  return $ vsep2 decls

compileDecl :: (MonadLeanCompile m) => LeanOptions -> Decl DecidabilityBuiltin -> m (Maybe Code)
compileDecl _opts = \case
  DefAbstract _ n _ t ->
    Just <$> compilePostulate n t
  DefFunction p n funSort t e -> case funSort of
    -- Types are emitted as 'abbrev' so that Lean can see through them during
    -- typeclass resolution (e.g. to find pointwise `+` on `Fin 2 → ℝ`).
    TypeDecl binderCount -> Just <$> compileFunctionDecl "abbrev" n binderCount t e
    FunctionDecl binderCount Nothing -> Just <$> compileFunctionDecl "def" n binderCount t e
    FunctionDecl _ (Just AnnProperty) -> Just <$> compileProperty n e
    FunctionDecl _ (Just AnnInstance {}) -> throwError $ UnimplementedFeature p "Compiling instances to Lean"
    ProjectionDecl {} -> return Nothing
    TensorCoercionDecl binderCount -> Just <$> compileFunctionDecl "def" n binderCount t e
  DefRecord p n _ telescope fields _supports ->
    Just <$> compileRecordDecl p n telescope fields

compileFunctionDecl ::
  (MonadLeanCompile m) =>
  Code ->
  Identifier ->
  LHSBinderCount ->
  Type DecidabilityBuiltin ->
  Expr DecidabilityBuiltin ->
  m Code
compileFunctionDecl keyword ident binderCount t e = do
  let (binders, body) = extractDeclBinders binderCount t e
  binders' <- compileTopLevelBinders binders
  (_, cbody) <- compileBinders binders (compileExpr body)
  defType <- resolveReturnType binders' t
  return $ compileFunDef keyword (compileIdentifier ident) defType binders' cbody

compileRecordDecl ::
  (MonadLeanCompile m) =>
  Provenance ->
  Identifier ->
  Telescope DecidabilityBuiltin ->
  RecordFields DecidabilityBuiltin ->
  m Code
compileRecordDecl p ident telescope fields = do
  if null telescope
    then return ()
    else throwError $ UnimplementedFeature p "Compiling parameterised records to Lean"
  fs' <- traverseRecordFields compileExpr fields
  return $
    "structure"
      <+> compileIdentifier ident
      <+> "where"
      <> line
      <> indent 2 (vsep $ fmap (\(field, fieldType) -> pretty field <+> ":" <+> fieldType) fs')

extractDeclBinders ::
  LHSBinderCount ->
  Type DecidabilityBuiltin ->
  Expr DecidabilityBuiltin ->
  ([Binder DecidabilityBuiltin], Expr DecidabilityBuiltin)
extractDeclBinders binderCount typ expr
  | binderCount == 0 = ([], expr)
  | otherwise = case (typ, expr) of
      (Pi _ piBinder piBody, Lam _ lamBinder lamBody) -> do
        -- We want the name from the lambda binder and the type from the
        -- pi binder as this is usually what the user will write.
        let compositeBinder = replaceBinderType (typeOf piBinder) lamBinder
        first (compositeBinder :) (extractDeclBinders (binderCount - 1) piBody lamBody)
      (_, _) -> ([], expr)

-- | Compile a 'network', 'dataset' or 'parameter' declaration
compilePostulate ::
  (MonadLeanCompile m) =>
  Identifier ->
  Type DecidabilityBuiltin ->
  m Code
compilePostulate ident t = do
  let name = compileIdentifier ident
  typ <- compileExpr t
  return $ "axiom" <+> name <+> ":" <+> align typ

compileExpr :: (MonadLeanCompile m) => Expr DecidabilityBuiltin -> m Code
compileExpr expr = do
  logEntry expr
  result <- case expr of
    Hole {} -> resolutionError currentPhase "Hole"
    Meta {} -> resolutionError currentPhase "Meta"
    Universe _ l -> return $ compileType l
    FreeVar _ n -> return $ atom (pretty (nameOf n))
    BoundVar p ix -> do
      n <- ixToProperName p ix
      return $ atom (pretty n)
    Pi _ binder result -> case binderNamingForm binder of
      OnlyType -> compileFunctionType [argFromBinder binder (typeOf binder), explicit result]
      _ -> do
        let (binders, body) = foldPiBinders binder result
        compileTypeLevelQuantifier Forall (binder :| binders) body
    Let _ bound binder body -> do
      cBoundExpr <- compileLetBinder (binder, bound)
      cBody <- addNameToContext binder $ compileExpr body
      return $ annotate loosest ("let" <+> cBoundExpr <> ";" <+> cBody)
    Lam _ binder body -> compileLam binder body
    Builtin _p b -> compileBuiltin b []
    App fun args -> compileApp fun args
    Record _p _i fs -> do
      fs' <- traverse compileRecordField fs
      return $ atom $ encloseSep (lbrace <> space) (space <> rbrace) (comma <> space) fs'
    RecordProj _p _t r field ->
      compileNotationAndArgs NotAssociative Nothing ("$0." <> nameOf field) (Just $ nameOf field) [explicit r]
  logExit result
  return result

compileType :: UniverseLevel -> Code
compileType (UniverseLevel l)
  | l == 0 = atom "Type"
  | otherwise =
      developerError
        "compilation of higher-level universes to Lean unsupported"

compileLetBinder ::
  (MonadLeanCompile m) =>
  LetBinder (Expr DecidabilityBuiltin) ->
  m Code
compileLetBinder (binder, expr) = do
  let binderName = pretty (getBinderName binder)
  cExpr <- compileExpr expr
  return $ binderName <+> ":=" <+> cExpr

compileIdentifier :: Identifier -> Code
compileIdentifier ident = atom $ pretty (nameOf ident :: Name)

-- | Properties are emitted as axioms (there is no verification cache yet).
compileProperty :: (MonadLeanCompile m) => Identifier -> Expr DecidabilityBuiltin -> m Code
compileProperty ident expr = do
  let propertyName = compileIdentifier ident
  propertyBody <- compileExpr expr
  return $ "axiom" <+> propertyName <+> ":" <+> propertyBody

compileTopLevelBinders :: (MonadLeanCompile m) => [Binder DecidabilityBuiltin] -> m [Code]
compileTopLevelBinders [] = return []
compileTopLevelBinders (b : bs) = do
  b' <- compileTopLevelBinder b
  addNameToContext b $ case b' of
    Nothing -> compileTopLevelBinders bs
    Just bc -> do
      bsc <- compileTopLevelBinders bs
      return $ bc : bsc

compileTopLevelBinder :: (MonadLeanCompile m) => Binder DecidabilityBuiltin -> m (Maybe Code)
compileTopLevelBinder binder
  | visibilityOf binder /= Explicit = pure Nothing
  | otherwise = do
      let binderName = pretty (getBinderName binder)
      binderType <- compileExpr (typeOf binder)
      pure . Just . parens $ binderName <+> ":" <+> binderType

compileBinders :: (MonadLeanCompile m) => [Binder DecidabilityBuiltin] -> m Code -> m ([Code], Code)
compileBinders [] c = ([],) <$> c
compileBinders (b : bs) c = do
  (cbs, cc) <- addNameToContext b $ compileBinders bs c
  cb <- compileBinder b
  return (cb : cbs, cc)

compileBinder :: (MonadLeanCompile m) => Binder DecidabilityBuiltin -> m Code
compileBinder binder = do
  binderType <- compileExpr (typeOf binder)
  (binderDoc, noExplicitBrackets) <- case binderNamingForm binder of
    OnlyName name _ -> return (pretty name, True)
    OnlyType -> return (binderType, True)
    NameAndType name _ -> return (pretty name <+> ":" <+> binderType, False)

  return $ binderBrackets noExplicitBrackets (visibilityOf binder) binderDoc

binderBrackets :: Bool -> Visibility -> Code -> Code
binderBrackets True Explicit {} = id
binderBrackets False Explicit {} = parens
binderBrackets _topLevel Implicit {} = braces
binderBrackets _topLevel Instance {} = brackets

resolveReturnType :: (MonadLeanCompile m) => [Code] -> Expr DecidabilityBuiltin -> m Code
resolveReturnType (_ : bs) (Pi _ binder r) = addNameToContext binder $ resolveReturnType bs r
resolveReturnType _ e = compileExpr e

compileRecordField :: (MonadLeanCompile m) => GenericRecordField (Expr DecidabilityBuiltin) -> m Code
compileRecordField (field, fieldValue) = do
  fieldValue' <- compileExpr fieldValue
  return $ pretty field <+> ":=" <+> fieldValue'

compileFunDef :: Code -> Code -> Code -> [Code] -> Code -> Code
compileFunDef keyword name t bindings e =
  keyword
    <+> name
    <+> (if null bindings then mempty else hsep bindings <> " ")
    <> ":"
    <+> align t
    <+> ":="
    <+> e

compileBuiltin :: (MonadLeanCompile m) => DecidabilityBuiltin -> [Arg DecidabilityBuiltin] -> m Code
compileBuiltin b args = case b of
  StandardBuiltinType t -> case t of
    BoolType -> return $ atom "Bool"
    -- For the Lean backend, rationals are promoted to reals
    RatType -> return $ atom "ℝ"
    UnitType -> return $ atom "Unit"
    NatType -> return $ atom "ℕ"
    ListType -> compileApplication "List" args
    TensorType -> compileTensorType args
    IndexType -> compileApplication "Fin" args
    VectorType -> compileVectorType args
  StandardBuiltinConstructor c -> case c of
    Nil -> return $ atom "[]"
    Cons -> compileNotationAndArgs RightAssociative (leanPrec 67) "$0 :: $1" (Just "List.cons") args
    UnitLiteral -> return $ atom "()"
    IndexLiteral n -> return $ atom (pretty n)
    NatLiteral n -> return $ atom (pretty n)
    NatTensorLiteral t -> return $ compileTensorLiteral compileNatLiteral t
    BoolTensorLiteral t -> return $ compileTensorLiteral compileBoolLiteral t
    RatTensorLiteral t -> return $ compileTensorLiteral compileRealLiteral t
    VectorLiteral -> compileVecLiteral args
  StandardBuiltinFunction f -> case f of
    And -> compileNotationAndArgs LeftAssociative (leanPrec 35) "$0 && $1" (Just "and") args
    Or -> compileNotationAndArgs LeftAssociative (leanPrec 30) "$0 || $1" (Just "or") args
    Not -> compileNotationAndArgs NotAssociative (leanPrec 40) "!$0" (Just "not") args
    Implies -> compileNotationAndArgs NotAssociative Nothing "(!($0) || $1)" Nothing args
    Add AddNat -> compileNotationAndArgs LeftAssociative (leanPrec 65) "$0 + $1" Nothing args
    Mul MulNat -> compileNotationAndArgs LeftAssociative (leanPrec 70) "$0 * $1" Nothing args
    Add AddRatTensor -> compileNotationAndArgs LeftAssociative (leanPrec 65) "$0 + $1" Nothing args
    Sub SubRatTensor -> compileNotationAndArgs LeftAssociative (leanPrec 65) "$0 - $1" Nothing args
    Mul MulRatTensor -> compileNotationAndArgs LeftAssociative (leanPrec 70) "$0 * $1" Nothing args
    Div DivRatTensor -> compileNotationAndArgs LeftAssociative (leanPrec 70) "$0 / $1" Nothing args
    Neg NegRatTensor -> compileNotationAndArgs NotAssociative (leanPrec 75) "-$0" Nothing args
    Min MinRatTensor -> compileApplication "min" args
    Max MaxRatTensor -> compileApplication "max" args
    CompareIndex op -> compileComparison True op args
    CompareNat op -> compileComparison True op args
    CompareRatTensor op -> case decideIfPointwiseOrReductionComparison args of
      Pointwise as -> compileComparison True op as
      Reduced {} -> unsupportedError
    FoldList -> compileApplication "List.foldr" args
    MapList -> compileApplication "List.map" args
    ReverseList -> compileApplication "List.reverse" args
    AppendList {} -> unsupportedError
    ReduceAndTensor -> unsupportedError
    ReduceOrTensor -> unsupportedError
    ReduceAddRatTensor -> unsupportedError
    ReduceMinRatTensor -> unsupportedError
    ReduceMaxRatTensor -> unsupportedError
    ReduceMulRatTensor -> unsupportedError
    ConstTensor -> compileConstTensor args
    QuantifyRatTensor q -> compileQuantifierFunction q args
    AtTensor -> compileAt args
    If -> compileNotationAndArgs NotAssociative loosest "if $0 then $1 else $2" Nothing args
    ForeachTensor -> compileForeach args
    StackTensor -> compileStack args
    Transpose -> unsupportedError
    AtVector -> compileAt args
    ForeachVector -> compileForeach args
    QuantifyRecord q -> compileQuantifierFunction q args
    SearchRatTensor {} -> unsupportedError
    WhereTensor {} -> unsupportedError
    Iterate -> unsupportedError
    Pow {} -> unsupportedError
    Log {} -> unsupportedError
    Exp {} -> unsupportedError
  DecidabilityBuiltinFunction f -> case f of
    PropType -> return $ atom "Prop"
    PropTrue -> return $ atom "True"
    PropFalse -> return $ atom "False"
    PropNot -> compileNotationAndArgs NotAssociative (leanPrec 40) "¬$0" (Just "Not") args
    PropAnd -> compileNotationAndArgs RightAssociative (leanPrec 35) "$0 ∧ $1" (Just "And") args
    PropOr -> compileNotationAndArgs RightAssociative (leanPrec 30) "$0 ∨ $1" (Just "Or") args
    PropImplies -> compileFunctionType args
    PropCompareIndex op -> compileComparison False op args
    PropCompareNat op -> compileComparison False op args
    PropCompareRatTensor op -> compileComparison False op args
    BoolTensorToProp -> monoError
    BoolVectorToProp -> monoError
    PropQuantifyIndex q -> compileQuantifierFunction q args
    PropQuantifyInList {} -> unsupportedError
    PropNaryProduct -> unsupportedError
    PropNaryProductForeach -> unsupportedError
    PropNaryProductAt -> unsupportedError
  DecidabilityBuiltinTypeClass {} -> monoError
  DecidabilityBuiltinTypeClassOp {} -> monoError
  StandardBuiltinDerivedFunction f -> compileDerivedFunction f args
  where
    unsupportedError :: a
    unsupportedError =
      developerError $
        "compilation of builtin" <+> quotePretty b <+> "to Lean unsupported"

    monoError :: a
    monoError =
      developerError $
        "Monomorphisation should have got rid of"
          <+> quotePretty (show b)

compileFunctionType :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileFunctionType = compileNotationAndArgs RightAssociative (leanPrec 25) "$0 → $1" (Just "implies")

compileApp :: (MonadLeanCompile m) => Expr DecidabilityBuiltin -> NonEmpty (Arg DecidabilityBuiltin) -> m Code
compileApp fun args = case fun of
  Builtin _p b -> do
    let userArgs = builtinAppArgs b args
    compileBuiltin b userArgs
  _ -> do
    let userArgs = NonEmpty.filter (not . wasInsertedByCompiler) args
    cFun <- compileExpr fun
    cFun' <- bracketFunction cFun
    compileApplication cFun' userArgs

-- | Brackets an expression in function position, unless it is an atom or
-- is itself an application.
bracketFunction :: (MonadLeanCompile m) => Code -> m Code
bracketFunction = bracketOne (Just 1)

-- | Brackets a single expression relative to the given parent precedence.
bracketOne :: (MonadLeanCompile m) => Maybe Precedence -> Code -> m Code
bracketOne level c = do
  bracketed <- bracketArgs [level] [explicit c]
  return $ case bracketed of
    [c'] -> c'
    _ -> c

compileDerivedFunction :: (MonadLeanCompile m) => DerivedFunction -> [Arg DecidabilityBuiltin] -> m Code
compileDerivedFunction fn args = case fn of
  QuantifyIndex q -> compileQuantifierFunction q args
  QuantifyInList {} -> unsupported
  TypeAnn -> compileNotationAndArgs NotAssociative Nothing "($1 : $0)" Nothing args
  where
    unsupported = developerError $ "Compilation of stdlib function" <+> quotePretty fn <+> "not implemented"

-- | Quantifiers are compiled to Lean's native `∀ x : T, ...` / `∃ x : T, ...`
compileQuantifierFunction :: (MonadLeanCompile m) => Quantifier -> [Arg DecidabilityBuiltin] -> m Code
compileQuantifierFunction q args = case reverse args of
  (ExplicitArg _ (Lam _ binder body)) : _ -> compileTypeLevelQuantifier q [binder] body
  _ ->
    compilerDeveloperError $
      "compilation of quantifier" <+> quotePretty q <+> "with args" <+> prettyVerbose args <+> "to Lean unsupported"

compileTypeLevelQuantifier ::
  (MonadLeanCompile m) =>
  Quantifier ->
  NonEmpty (Binder DecidabilityBuiltin) ->
  Expr DecidabilityBuiltin ->
  m Code
compileTypeLevelQuantifier q binders body = do
  (cBinders, cBody) <- compileBinders (NonEmpty.toList binders) (compileExpr body)
  let quant = case q of
        Forall -> "∀"
        Exists -> "∃"
  return $ annotate loosest (quant <+> hsep cBinders <> "," <+> cBody)

operandLevels :: Associativity -> Maybe Precedence -> Int -> [Maybe Precedence]
operandLevels associativity precedence numArgs =
  [if onAssociativeSide index then fmap (+ 1) precedence else precedence | index <- [0 .. numArgs - 1]]
  where
    onAssociativeSide index = case associativity of
      LeftAssociative -> index == 0
      RightAssociative -> index == numArgs - 1
      NotAssociative -> False

bracketArgs :: (MonadLeanCompile m) => [Maybe Precedence] -> [GenericArg Code] -> m [Code]
bracketArgs argLevels args = traverse bracketArg (zip argLevels args)
  where
    bracketArg :: (MonadLeanCompile m) => (Maybe Precedence, GenericArg Code) -> m Code
    bracketArg (maybeParentPrecedence, arg) = do
      let body = argExpr arg
      return $ case visibilityOf arg of
        Instance {} -> atom $ brackets body
        Implicit {} -> atom $ braces body
        Explicit {} -> case (getPrecedence body, maybeParentPrecedence) of
          (Just argPrecedence, Just parentPrecedence)
            | argPrecedence >= parentPrecedence -> atom $ parens body
            | otherwise -> body
          _ -> body

compileNatLiteral :: Int -> Code
compileNatLiteral i = atom $ pretty i

-- | Compile a tensor type to nested functions out of Fin:

compileTensorType :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileTensorType args = case getExpr accessSpine args of
  Just (TensorTypeArgs elemTypeArg dimsArg) -> do
    elemType <- compileExpr elemTypeArg
    dims <- compileDimList dimsArg
    dims' <- bracketArgs (replicate (length dims) functionApplicationPrecedence) (fmap explicit dims)
    let finTypes = fmap (\d -> "Fin" <+> d) dims'
    case finTypes of
      [] -> return elemType
      _ -> do
        elemType' <- bracketOne (leanPrec 26) elemType
        return $ annotate (leanPrec 25) (concatWith (surround " → ") (finTypes <> [elemType']))
  Nothing -> developerError "compileTensorType: expected element type and dimension list"

-- | Compiles `Vector A n` as `Fin n → A`.
compileVectorType :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileVectorType = compileNotationAndArgs RightAssociative (leanPrec 25) "Fin $0 → $1" Nothing

-- | Walk a Nat-Cons/Nil dimension list expression and compile each element.
compileDimList :: (MonadLeanCompile m) => Expr DecidabilityBuiltin -> m [Code]
compileDimList = go []
  where
    go :: (MonadLeanCompile m) => [Code] -> Expr DecidabilityBuiltin -> m [Code]
    go acc = \case
      INil _ -> return (reverse acc)
      ICons _ x xs -> do
        x' <- compileDimElem x
        go (x' : acc) xs
      _ -> developerError "compileDimList: dimension list is not a Cons/Nil chain"
    compileDimElem :: (MonadLeanCompile m) => Expr DecidabilityBuiltin -> m Code
    compileDimElem (INatLiteral n) = return $ atom (pretty n)
    compileDimElem e = compileExpr e

-- | Tensor literals are nested `![a, b, c]` vectors (scalars are just the element).
compileTensorLiteral :: (a -> Code) -> Tensor a -> Code
compileTensorLiteral compileElement t = case (shapeOf t, toList t) of
  ([], [x]) -> compileElement x
  _ -> foldMapTensor compileElement toTensor t
  where
    toTensor :: TensorShape -> [Code] -> Code
    toTensor _shape values = atom $ "![" <> concatWith (surround ", ") values <> "]"

compileBoolLiteral :: Bool -> Code
compileBoolLiteral = \case
  True -> atom "true"
  False -> atom "false"

compileRealLiteral :: ExtendedRational -> Code
compileRealLiteral = \case
  Finite r -> do
    let num = pretty $ numerator r
    let denom = pretty $ denominator r
    let rat = (if denominator r == 1 then num else num <+> "/" <+> denom) <+> ":" <+> "ℝ"
    atom $ parens rat
  _ -> developerError "Compiling infinite values to Lean not supported"

compileLam :: (MonadLeanCompile m) => Binder DecidabilityBuiltin -> Expr DecidabilityBuiltin -> m Code
compileLam binder expr = do
  let (binders, body) = foldLamBinders binder expr
  (cBinders, cBody) <- compileBinders (binder : binders) (compileExpr body)
  return $ annotate loosest ("fun" <+> hsep cBinders <+> "=>" <+> cBody)

-- | Comparisons. The 'Bool' flag says whether the result is a Lean `Bool`
-- (in which case the proposition is wrapped in `decide`) or a `Prop`.
compileComparison :: (MonadLeanCompile m) => Bool -> ComparisonOp -> [Arg DecidabilityBuiltin] -> m Code
compileComparison isBool op =
  compileNotationAndArgs NotAssociative (leanPrec 50) template Nothing
  where
    opDoc :: Text
    opDoc = case op of
      Le -> "≤"
      Lt -> "<"
      Ge -> "≥"
      Gt -> ">"
      Eq -> "="
      Ne -> "≠"
    template :: Text
    template
      | isBool = "decide ($0 " <> opDoc <> " $1)"
      | otherwise = "$0 " <> opDoc <> " $1"

-- | Indexing into a tensor or vector is just function application: `x i`.
compileAt :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileAt = \case
  [tensorArg, indexArg] -> do
    tensor <- compileExpr (argExpr tensorArg)
    tensor' <- bracketFunction tensor
    compileApplication tensor' [indexArg]
  _ -> developerError "compileAt: expected a tensor and an index"

-- | `foreach i . e` is just the function `fun i => e`.
compileForeach :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileForeach args = case reverse args of
  (lamArg : _) -> compileExpr (argExpr lamArg)
  [] -> developerError "compileForeach: missing function argument"

-- | Constant tensors are constant functions, nested once per dimension.
compileConstTensor :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileConstTensor args = case getExpr accessSpine args of
  Just (ConstTensorArgs _t v ds) -> do
    value <- compileExpr v
    dims <- compileDimList ds
    value' <- bracketOne functionApplicationPrecedence value
    let wrap inner = "Function.const _" <+> inner
    let nested = foldr (\_ inner -> annotate functionApplicationPrecedence (wrap (parensIfNeeded inner))) value' dims
    return nested
  Nothing -> developerError "Malformed constant tensor"
  where
    parensIfNeeded :: Code -> Code
    parensIfNeeded c = case getPrecedence c of
      Just _ -> parens c
      Nothing -> c

compileStack :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileStack args = toVec args

compileVecLiteral :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
compileVecLiteral xs = case getExpr accessSpine xs of
  Just (VectorLitArgs _t _d ds) -> toVec (fmap explicit ds)
  Nothing -> developerError "Malformed type-checked vector literal"

-- | Compiles a list of expressions to Lean's `![a, b, c]` vector notation.
toVec :: (MonadLeanCompile m) => [Arg DecidabilityBuiltin] -> m Code
toVec xs = do
  compiled <- traverseArgs compileExpr xs
  return $ atom $ "![" <> concatWith (surround ", ") (fmap argExpr compiled) <> "]"
