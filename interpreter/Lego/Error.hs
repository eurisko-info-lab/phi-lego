{-# LANGUAGE DeriveFunctor #-}
-- | Error types for Lego
--
-- Provides structured error types with source locations
-- for better error messages and programmatic error handling.
module Lego.Error
  ( -- * Source locations
    SrcSpan(..)
  , noSpan
  , mkSpan
  , spanFile
  , spanLine
  , spanCol
  , spanUnion
    -- * Located values
  , Located(..)
  , unLoc
  , getLoc
  , noLoc
  , withLoc
  , mapLoc
    -- * Error types
  , LegoError(..)
  , formatError
  , formatErrors
    -- * Result type
  , LegoResult
  ) where

-- | Source span: location in source file
data SrcSpan = SrcSpan
  { ssFile    :: FilePath
  , ssLine    :: Int
  , ssCol     :: Int
  , ssEndLine :: Int
  , ssEndCol  :: Int
  } deriving (Eq)

instance Show SrcSpan where
  show s = ssFile s ++ ":" ++ show (ssLine s) ++ ":" ++ show (ssCol s)

-- | No source location available
noSpan :: SrcSpan
noSpan = SrcSpan "" 0 0 0 0

-- | Create a single-point span
mkSpan :: FilePath -> Int -> Int -> SrcSpan
mkSpan file line col = SrcSpan file line col line col

-- | Union of two spans (smallest enclosing span)
spanUnion :: SrcSpan -> SrcSpan -> SrcSpan
spanUnion s1 s2
  | ssFile s1 == "" = s2
  | ssFile s2 == "" = s1
  | ssFile s1 /= ssFile s2 = s1  -- Different files, take first
  | otherwise = SrcSpan
      { ssFile = ssFile s1
      , ssLine = min (ssLine s1) (ssLine s2)
      , ssCol = if ssLine s1 <= ssLine s2 then ssCol s1 else ssCol s2
      , ssEndLine = max (ssEndLine s1) (ssEndLine s2)
      , ssEndCol = if ssEndLine s1 >= ssEndLine s2 then ssEndCol s1 else ssEndCol s2
      }

-- | Convenience accessors
spanFile :: SrcSpan -> FilePath
spanFile = ssFile

spanLine :: SrcSpan -> Int
spanLine = ssLine

spanCol :: SrcSpan -> Int
spanCol = ssCol

--------------------------------------------------------------------------------
-- Located values
--------------------------------------------------------------------------------

-- | A value with optional source location
data Located a = Located
  { locSpan :: Maybe SrcSpan
  , locVal  :: a
  } deriving (Eq, Functor)

instance Show a => Show (Located a) where
  show (Located Nothing v) = show v
  show (Located (Just s) v) = show s ++ ": " ++ show v

-- | Extract the value, discarding location
unLoc :: Located a -> a
unLoc = locVal

-- | Get the location (if any)
getLoc :: Located a -> Maybe SrcSpan
getLoc = locSpan

-- | Wrap a value with no location
noLoc :: a -> Located a
noLoc x = Located Nothing x

-- | Wrap a value with a location
withLoc :: SrcSpan -> a -> Located a
withLoc s x = Located (Just s) x

-- | Map over the value, preserving location
mapLoc :: (a -> b) -> Located a -> Located b
mapLoc f (Located s v) = Located s (f v)

-- | Structured error type for Lego
data LegoError
  = ParseError 
    { peSpan     :: SrcSpan
    , peMessage  :: String
    , peExpected :: [String]    -- What was expected
    }
  | GrammarError
    { geSpan    :: SrcSpan
    , geName    :: String       -- Grammar name
    , geMessage :: String
    }
  | RuleError
    { reSpan    :: SrcSpan
    , reName    :: String       -- Rule name
    , reMessage :: String
    }
  | UnboundVar
    { uvSpan :: SrcSpan
    , uvName :: String
    }
  | TypeError
    { teSpan     :: SrcSpan
    , teExpected :: String
    , teActual   :: String
    , teContext  :: String
    }
  | FileError
    { feFile    :: FilePath
    , feMessage :: String
    }
  | InternalError
    { ieMessage :: String
    }
  deriving (Eq)

instance Show LegoError where
  show = formatError

-- | Format a single error for display
formatError :: LegoError -> String
formatError err = case err of
  ParseError sp message expected ->
    showSpan sp ++ "Parse error: " ++ message
    ++ if null expected then ""
       else "\n  Expected: " ++ unwords expected
  
  GrammarError sp nm message ->
    showSpan sp ++ "Grammar error in '" ++ nm ++ "': " ++ message
  
  RuleError sp nm message ->
    showSpan sp ++ "Rule error in '" ++ nm ++ "': " ++ message
  
  UnboundVar sp nm ->
    showSpan sp ++ "Unbound variable: " ++ nm
  
  TypeError sp expected actual ctx ->
    showSpan sp ++ "Type error: expected " ++ expected
    ++ ", got " ++ actual
    ++ if null ctx then "" else "\n  in: " ++ ctx
  
  FileError file message ->
    file ++ ": " ++ message
  
  InternalError message ->
    "Internal error: " ++ message
  where
    showSpan s
      | ssFile s == "" = ""
      | otherwise = show s ++ ": "

-- | Format multiple errors
formatErrors :: [LegoError] -> String
formatErrors = unlines . map formatError

-- | Common result type for operations that can fail
type LegoResult a = Either LegoError a
