module Vehicle.Backend.ITP.Lean
  ( LeanOptions (..),
    compileProgToLean,
    writeLeanFile,
  )
where

import Control.Monad.IO.Class (MonadIO)
import Data.Version (makeVersion)
import Vehicle.Backend.Prelude
import Vehicle.Compile.Error
import Vehicle.Compile.Prelude
import Vehicle.Data.Builtin.Decidability
import Vehicle.Data.Variable.Bound.Context.Name

--------------------------------------------------------------------------------
-- Lean-specific options

data LeanOptions = LeanOptions
  { verificationCache :: Maybe FilePath,
    output :: Maybe FilePath,
    moduleName :: Maybe String,
    constructiveReals :: Bool
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
      formatVersion = Just $ makeVersion [4],
      commentStyle = Line "--",
      emptyLines = True
    }

type Code = Doc ()

type MonadLeanCompile m =
  ( MonadCompile m,
    MonadNameContext m
  )

compileProg :: (MonadLeanCompile m) => LeanOptions -> Prog DecidabilityBuiltin -> m Code
compileProg _options (Main _decls) = return ""
