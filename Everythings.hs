import System.Environment ( getArgs )
import System.Directory   ( getDirectoryContents )
import System.Exit        ( exitFailure )
import Control.Monad      ( forM, forM_ )
import Data.Maybe         ( listToMaybe, maybeToList, mapMaybe )
import Data.List          ( (\\), delete, find, intercalate, sort, stripPrefix, isSuffixOf )

stripSuffix :: (Eq a) => [a] -> [a] -> Maybe [a]
stripSuffix sfx = fmap reverse . stripPrefix (reverse sfx) . reverse

splitOn :: Char -> String -> [String]
splitOn d = foldr go []
  where go :: Char -> [String] -> [String]
        go x acc | d == x = []:acc
        go x (a:acc) = (x:a):acc
        go x [] = [[x]]


type SplitFilePath = [String]

showFP :: Char -> SplitFilePath -> String
showFP c fp = intercalate [c] (reverse fp)

addToFP :: SplitFilePath -> String -> SplitFilePath
addToFP fp dir = dir : fp

-- Given a path to a directory, returns a pair containing the list of all its
--  subdirectories and the list of all agda files it contains
getSubDirsFiles :: SplitFilePath -> IO ([String], [String])
getSubDirsFiles fp = do
  ls <- getDirectoryContents ("./" ++ showFP '/' fp)
  let sub_dirs = filter ('.' `notElem`) ls
      files    = mapMaybe (stripSuffix ".agda") ls
  pure (sub_dirs, files)

-- Given a path to an agda file, returns the list of all files it imports
getImported :: SplitFilePath -> IO [SplitFilePath]
getImported fp = do
  ls <- fmap words . lines <$> readFile ("./" ++ showFP '/' fp ++ ".agda")
  pure $ fmap (reverse . splitOn '.') (mapMaybe f ls)
  where f :: [String] -> Maybe String
        f ("open":"import":x:_) = Just x
        f ("import":x:_) = Just x
        f _ = Nothing

-- Given a path to a directory $fp and a path to an agda file $fileToCheck.agda,
--  returns the list of all files in* $fp not imported in $fileToCheck.agda
-- * recursively
getMissingFiles :: SplitFilePath -> Maybe SplitFilePath -> IO [SplitFilePath]
getMissingFiles fp fpToCheck = do
  (sub_dirs, sub_files) <- getSubDirsFiles fp
  -- recursively get all files in $fp/X not imported in $fp/X.agda (if it exists)
  missing_files <- concat <$> forM sub_dirs (\sub_dir ->
    getMissingFiles
      (addToFP fp sub_dir)
      (addToFP fp <$> find (== sub_dir) sub_files))
  -- return all of these files, plus all agda files in the current directory,
  --  except for those which are imported in $fpToCheck.agda (if it exists) or
  --  which are $fpToCheck.agda itself
  imported <- maybe (pure []) getImported fpToCheck
  pure $ ((addToFP fp <$> sub_files) ++ missing_files)
         \\ (maybeToList fpToCheck ++ imported)


checkEverythings :: [SplitFilePath] -> [String] -> IO ()
checkEverythings excludes dirs = do
  missing_files <- concat <$> forM dirs (\dir -> do
    let ex = map reverse excludes
    miss <- getMissingFiles [dir] (Just ["Everything",dir])
    pure $ filter (\l -> not $ any (`isSuffixOf` l) ex) miss
    )
  if null missing_files then pure ()
  else do putStrLn "Found some files which are not imported in any Everything.agda:"
          forM_ missing_files (putStrLn . (" " ++) . showFP '.')
          exitFailure

checkRoot :: IO ()
checkRoot = do
  (sub_dirs', _) <- getSubDirsFiles ["."]
  let sub_dirs = filter (\d -> d `notElem` ["Everything.hs",
                                            "_build",
                                            "README.org",
                                            ".gitignore",
                                            ".github",
                                            "env",
                                            "LICENSE",
                                            "Notes",
                                            "check-line-lengths.sh",
                                            "cubical-categorical-logic.agda-lib",
                                            "fix-whitespace.yaml",
                                            "Makefile"]) sub_dirs'
  imported <- getImported ["TestEverything"]
  let missing_files = fmap (\dir -> ["Everything",dir]) sub_dirs \\ imported
  if null missing_files then pure ()
  else do putStrLn "Found some Everything.agda's which are not imported in README.agda:"
          forM_ missing_files (putStrLn . (" " ++) . showFP '.')
          exitFailure

genEverythings :: [SplitFilePath] -> [String] -> IO ()
genEverythings excludes =
  mapM_ $ \ dir -> do
    let fp = [dir]
    files' <- getMissingFiles fp Nothing
    let ex = map reverse excludes
    let files = filter (\l -> not $ any (`isSuffixOf` l) ex) files'
    let ls = ["module " ++ showFP '.' (addToFP fp "Everything") ++ " where",[]]
             ++ sort (fmap (\file -> do
                              "import " ++ showFP '.' file
                           )
                           (delete (addToFP fp "Everything") files))
    writeFile ("./" ++ showFP '/' (addToFP fp "Everything") ++ ".agda")
              (unlines ls)

helpText :: String
helpText = unlines [
  "Accepted arguments: ",
  " check d1 d2 ... dn         checks imports in the Everything files in the",
  "                            given directories",
  " check-except d1 d2 ... dn  checks imports in all Everything files except those",
  "                            in the given directories",
  " gen d1 d2 ... dn           generates Everything files in the given directories",
  " gen-except d1 d2 ... dn    generates Everything files in all directories",
  "                            except in those given",
  " check-Root               checks all Everything files are imported in README"]

main :: IO ()
main = do
  all_dirs' <- filter ('.' `notElem`) <$> getDirectoryContents "."
  let all_dirs = filter (\d -> d `notElem` ["Everything.hs",
                                            "_build",
                                            "README.org",
                                            ".gitignore",
                                            ".github",
                                            "env",
                                            "LICENSE",
                                            "Notes",
                                            "check-line-lengths.sh",
                                            "cubical-categorical-logic.agda-lib",
                                            "fix-whitespace.yaml",
                                            "Makefile"]) all_dirs'
  args <- getArgs
  case args of
    "check":dirs -> checkEverythings [] dirs
    "gen"  :dirs -> genEverythings   [] dirs
    "check-except":ex_dirs ->
        checkEverythings
          (map (\f -> splitOn '/' f) ex_dirs)
          (all_dirs \\ ex_dirs)
    "gen-except"  :ex_dirs ->
        genEverythings
          (map (\f -> splitOn '/' f) ex_dirs)
          (all_dirs \\ ex_dirs)
    ["check-Root"] -> checkRoot
    "help":_ -> putStrLn helpText
    _ -> putStrLn "argument(s) not recognized, try 'help'"
