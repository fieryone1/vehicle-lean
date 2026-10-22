module Vehicle.Backend.ITP.Lean
  ( LeanOptions (..),
    compileProgToLean,
    writeLeanFile,
  )
where

--------------------------------------------------------------------------------
-- Rocq-specific options

data LeanOptions = LeanOptions
  { verificationCache :: Maybe FilePath,
    output :: Maybe FilePath,
    moduleName :: Maybe String,
    constructiveReals :: Bool
  }

currentPhase :: Doc ()
currentPhase = "compilation to Lean"
