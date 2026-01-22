{-# LANGUAGE LambdaCase #-}
-- | Lego Registry: Package and language name resolution
--
-- == Package System
--
-- A package is identified by a path relative to known roots:
--   - prelude/  : .lego files that Lego itself depends on
--   - examples/ : example Lego files
--
-- Package naming: path/to/File.lego → package "path.to.File"
--   - prelude/lego/Grammar.lego → "prelude.lego.Grammar"
--   - examples/Nat.lego → "examples.Nat"
--   - examples/basics/Bool.lego → "examples.basics.Bool"
--
-- == Language Registry
--
-- A .lego file can define multiple pieces and languages.
-- They are registered with qualified names:
--   - pieces in prelude/lego/Grammar.lego:
--       prelude.lego.Grammar.Term, prelude.lego.Grammar.Pattern, ...
--   - lang in examples/Nat.lego:
--       examples.Nat, examples.Nat.NatRules, ...
--
-- == Import Resolution
--
-- When importing, we check:
--   1. Current package's local definitions (same file)
--   2. Registry (qualified or unqualified lookup)
--   3. File system search from known roots
--
module Lego.Registry
  ( -- * Package Types
    PackageName
  , QualifiedName
  , Registry
  , emptyRegistry
    -- * Package Operations
  , pathToPackage
  , packageToPath
  , qualifyName
  , unqualifyName
    -- * Registry Operations
  , registerPackage
  , registerLang
  , lookupLang
  , lookupByShortName
    -- * Import Resolution
  , ResolveContext(..)
  , resolveImport
  , findPackageFile
    -- * Root Paths
  , legoRoots
  , findLegoRoot
  ) where

import qualified Data.Map as M
import qualified Data.Set as S
import System.FilePath ((</>), takeDirectory, takeBaseName,
                        splitDirectories, joinPath, normalise)
import System.Directory (doesFileExist, doesDirectoryExist, getCurrentDirectory, listDirectory)
import Data.List (isPrefixOf, intercalate)
import Data.Char (toLower)
import Control.Monad (filterM)

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

-- | Package name: "prelude.lego.Grammar" or "examples.basics.Bool"
type PackageName = String

-- | Qualified name: "prelude.lego.Grammar.Term" or "examples.Nat.succ"
type QualifiedName = String

-- | Registry maps qualified names to compiled language info
-- We store both the full qualified name and short name for lookup
data Registry = Registry
  { regByQualified :: M.Map QualifiedName RegistryEntry
  , regByShort     :: M.Map String [QualifiedName]  -- short name → all qualified names
  , regPackages    :: S.Set PackageName             -- known packages
  } deriving (Show)

data RegistryEntry = RegistryEntry
  { rePkgName   :: PackageName
  , reShortName :: String
  , rePath      :: Maybe FilePath  -- source file path if known
  } deriving (Show)

emptyRegistry :: Registry
emptyRegistry = Registry M.empty M.empty S.empty

--------------------------------------------------------------------------------
-- Package Naming
--------------------------------------------------------------------------------

-- | Known Lego root directories (relative to workspace)
legoRoots :: [FilePath]
legoRoots = ["prelude", "examples", "phi"]

-- | Convert file path to package name
-- "prelude/lego/Grammar.lego" → "prelude.lego.Grammar"
-- "examples/basics/Bool.lego" → "examples.basics.Bool"
pathToPackage :: FilePath -> PackageName
pathToPackage path = 
  let normalized = normalise path
      dirs = splitDirectories normalized
      -- Find where a known root starts
      (root, rest) = findRootPrefix dirs
      -- Remove .lego extension from filename
      withoutExt = case rest of
        [] -> []
        xs -> init xs ++ [takeBaseName (last xs)]
  in intercalate "." (root ++ withoutExt)
  where
    findRootPrefix dirs = go [] dirs
      where
        go _ [] = ([], [])
        go seen (d:ds)
          | d == "prelude" = (["prelude"], ds)
          | d == "examples" = (["examples"], ds)
          | d == "phi" = (["phi"], ds)
          | otherwise = go (seen ++ [d]) ds

-- | Convert package name to file path (relative to lego/)
-- "prelude.lego.Grammar" → "prelude/lego/Grammar.lego"
-- "examples.basics.Bool" → "examples/basics/Bool.lego"
packageToPath :: PackageName -> FilePath
packageToPath pkg = 
  let parts = splitOn '.' pkg
  in joinPath parts ++ ".lego"
  where
    splitOn _ [] = []
    splitOn c s = case break (== c) s of
      (part, []) -> [part]
      (part, _:rest) -> part : splitOn c rest

-- | Make a qualified name from package and local name
-- "prelude.lego.Grammar" + "Term" → "prelude.lego.Grammar.Term"
qualifyName :: PackageName -> String -> QualifiedName
qualifyName pkg name = pkg ++ "." ++ name

-- | Extract the short (unqualified) name
-- "prelude.lego.Grammar.Term" → "Term"
unqualifyName :: QualifiedName -> String
unqualifyName qname = 
  case reverse (splitOn '.' qname) of
    (short:_) -> short
    [] -> qname
  where
    splitOn _ [] = []
    splitOn c s = case break (== c) s of
      (part, []) -> [part]
      (part, _:rest) -> part : splitOn c rest

--------------------------------------------------------------------------------
-- Registry Operations
--------------------------------------------------------------------------------

-- | Register a package in the registry
registerPackage :: PackageName -> FilePath -> Registry -> Registry
registerPackage pkg _path reg = reg
  { regPackages = S.insert pkg (regPackages reg) }

-- | Register a language or piece with qualified name
registerLang :: PackageName -> String -> Maybe FilePath -> Registry -> Registry
registerLang pkg shortName mPath reg = 
  let qname = qualifyName pkg shortName
      entry = RegistryEntry pkg shortName mPath
      -- Add to qualified map
      byQ = M.insert qname entry (regByQualified reg)
      -- Add to short name map (may have multiple qualifications)
      byS = M.insertWith (++) shortName [qname] (regByShort reg)
  in reg { regByQualified = byQ, regByShort = byS }

-- | Look up by qualified name
lookupLang :: QualifiedName -> Registry -> Maybe RegistryEntry
lookupLang qname reg = M.lookup qname (regByQualified reg)

-- | Look up by short name, optionally within a package context
-- Returns list of matching qualified names
lookupByShortName :: String -> Maybe PackageName -> Registry -> [QualifiedName]
lookupByShortName shortName mPkg reg = 
  case M.lookup shortName (regByShort reg) of
    Nothing -> []
    Just qnames -> case mPkg of
      -- No context: return all matches
      Nothing -> qnames
      -- With context: prefer same-package matches
      Just pkg -> 
        let inPkg = filter ((pkg ++ ".") `isPrefixOf`) qnames
        in if null inPkg then qnames else inPkg

--------------------------------------------------------------------------------
-- Import Resolution
--------------------------------------------------------------------------------

-- | Context for resolving imports
data ResolveContext = ResolveContext
  { rcCurrentPkg  :: PackageName       -- current package being compiled
  , rcCurrentDir  :: FilePath          -- directory of current file
  , rcRegistry    :: Registry          -- global registry
  , rcVisited     :: S.Set PackageName -- visited packages (cycle detection)
  , rcLocalLangs  :: S.Set String      -- locally defined lang names in current file
  } deriving (Show)

-- | Resolve an import name to a file path
-- 
-- Resolution order:
--   1. Local definitions in current file (rcLocalLangs)
--   2. Qualified name lookup in registry
--   3. Short name lookup in registry (prefer same package)
--   4. File system search from known roots
--   5. File system search from current directory
resolveImport :: ResolveContext -> String -> IO (Either String (Maybe FilePath, QualifiedName))
resolveImport ctx name
  -- Check for cycles
  | name `S.member` rcVisited ctx = 
      return $ Left $ "Circular import detected: " ++ name
  -- Local definition
  | name `S.member` rcLocalLangs ctx = 
      return $ Right (Nothing, qualifyName (rcCurrentPkg ctx) name)
  -- Qualified lookup
  | '.' `elem` name = case lookupLang name (rcRegistry ctx) of
      Just entry -> return $ Right (rePath entry, name)
      Nothing -> findByPath name
  -- Short name lookup
  | otherwise = case lookupByShortName name (Just $ rcCurrentPkg ctx) (rcRegistry ctx) of
      (qname:_) -> case lookupLang qname (rcRegistry ctx) of
        Just entry -> return $ Right (rePath entry, qname)
        Nothing -> findByPath name
      [] -> findByPath name
  where
    findByPath importName = do
      mPath <- findPackageFile (rcCurrentDir ctx) importName
      case mPath of
        Just path -> return $ Right (Just path, pathToPackage path)
        Nothing -> return $ Left $ 
          "Could not resolve import: " ++ importName ++ 
          " (from package " ++ rcCurrentPkg ctx ++ ")"

-- | Find a .lego file for a package/import name
-- 
-- Search order:
--   1. Current directory: dir/Name.lego
--   2. Parent directory: parent/Name.lego
--   3. Sibling directories: parent/*/Name.lego (for examples/advanced → examples/types)
--   4. Known roots: prelude/, examples/, phi/
--   5. Working directory
findPackageFile :: FilePath -> String -> IO (Maybe FilePath)
findPackageFile currentDir name = do
  -- Build candidate paths
  let lowerName = map toLower name
  -- If name has dots, treat as package path
  let nameParts = splitOn '.' name
      nameAsPath = joinPath nameParts ++ ".lego"
      nameAsPathLower = joinPath (map (map toLower) nameParts) ++ ".lego"
  
  -- Candidates from current directory and parent
  let parent = takeDirectory currentDir
  let localCandidates =
        [ currentDir </> name ++ ".lego"
        , currentDir </> lowerName ++ ".lego"
        , parent </> name ++ ".lego"
        , parent </> lowerName ++ ".lego"
        ]
  
  -- Sibling directories (e.g., examples/advanced → examples/basics, examples/types)
  siblingCandidates <- findSiblingCandidates parent name
  
  -- Candidates from known roots
  workDir <- getCurrentDirectory
  let rootCandidates = 
        [ workDir </> root </> nameAsPath
        | root <- ["prelude", "examples", "phi"]
        ] ++
        [ workDir </> root </> nameAsPathLower
        | root <- ["prelude", "examples", "phi"]
        ] ++
        -- Also search subdirectories of known roots
        [ workDir </> root </> subdir </> name ++ ".lego"
        | root <- ["examples"]
        , subdir <- ["basics", "types", "advanced", "meta"]
        ] ++
        [ workDir </> root </> subdir </> lowerName ++ ".lego"
        | root <- ["examples"]
        , subdir <- ["basics", "types", "advanced", "meta"]
        ]
  
  -- Working directory fallback
  let fallbackCandidates =
        [ name ++ ".lego"
        , lowerName ++ ".lego"
        ]
  
  -- Try all candidates in order
  let allCandidates = localCandidates ++ siblingCandidates ++ rootCandidates ++ fallbackCandidates
  findFirst doesFileExist allCandidates
  where
    splitOn _ [] = []
    splitOn c s = case break (== c) s of
      (part, []) -> [part]
      (part, _:rest) -> part : splitOn c rest

-- | Find import candidates in sibling directories
findSiblingCandidates :: FilePath -> String -> IO [FilePath]
findSiblingCandidates parent name = do
  let lowerName = map toLower name
  parentExists <- doesDirectoryExist parent
  if not parentExists
    then return []
    else do
      entries <- listDirectory parent
      dirs <- filterM (doesDirectoryExist . (parent </>)) entries
      return $ concatMap (\d -> [ parent </> d </> name ++ ".lego"
                                , parent </> d </> lowerName ++ ".lego"
                                ]) dirs

-- | Find the lego root directory from a file path
findLegoRoot :: FilePath -> Maybe FilePath
findLegoRoot path = 
  let dirs = splitDirectories (normalise path)
  in go [] dirs
  where
    go _ [] = Nothing
    go acc (d:ds)
      | d == "lego" = Just (joinPath (reverse acc ++ ["lego"]))
      | otherwise = go (d:acc) ds

--------------------------------------------------------------------------------
-- Helpers
--------------------------------------------------------------------------------

findFirst :: (a -> IO Bool) -> [a] -> IO (Maybe a)
findFirst _ [] = return Nothing
findFirst p (x:xs) = do
  ok <- p x
  if ok then return (Just x) else findFirst p xs
