module Agda2Hs.Compile where

import Prelude hiding (null)

import Control.Monad ( forM, forM_ )
import Control.Monad.IO.Class
import qualified Data.ByteString as BS
import Control.Monad.Trans.RWS.CPS ( evalRWST )
import Control.Monad.State ( gets )
import Control.Arrow ((>>>))
import Data.IORef
import Data.List ( isPrefixOf, group, sort )

import qualified Data.Map as M
import qualified Data.Set as S

import Agda.Compiler.Backend
import Agda.Compiler.Common ( curIF, curDefs, sortDefs )
import Agda.Utils.Hash ( hashByteString, hashString, combineHashes )
import Agda.Syntax.Common.Pretty ( prettyShow )
import Agda.TypeChecking.Pretty
import Agda.Utils.Impossible
import Agda.Utils.List
import Agda.Utils.Null
import Agda.Utils.Monad ( whenM, anyM, when, unless )

import Agda2Hs.AgdaUtils ( publicQNames )
import Agda2Hs.Compile.ClassInstance ( compileInstance )
import Agda2Hs.Compile.Data ( compileData, checkCompileToDataPragma )
import Agda2Hs.Compile.Function ( compileFun, checkTransparentPragma, checkInlinePragma, checkCompileToFunctionPragma )
import Agda2Hs.Compile.Name ( hsTopLevelModuleName )
import Agda2Hs.Compile.Postulate ( compilePostulate )
import Agda2Hs.Compile.Record ( compileRecord, checkUnboxPragma )
import Agda2Hs.Compile.Types
import Agda2Hs.Compile.Utils
import Agda2Hs.Config
import Agda2Hs.Pragma

import qualified Agda2Hs.Language.Haskell as Hs

import System.Directory ( doesFileExist )
import System.Environment ( getExecutablePath )
import System.IO ( readFile' )

globalSetup :: Options -> TCM GlobalEnv
globalSetup opts = do
  opts <- checkConfig opts
  ctMap <- liftIO $ newIORef M.empty
  ilMap <- liftIO $ newIORef S.empty
  -- the executable itself rather than its version: a rebuilt agda2hs of the same version may print differently
  exe <- liftIO $ hashByteString <$> (BS.readFile =<< getExecutablePath)
  config <- liftIO $ maybe (pure 0) (fmap hashByteString . BS.readFile) (optConfigFile opts)
  let key = hashHex $ combineHashes [exe, config, hashString (show (optExtensions opts))]
  tlMap <- liftIO $ newIORef M.empty
  return $ GlobalEnv opts ctMap ilMap key tlMap

-- | The module environment of the current module ('curIF'), read from the scope as it is now: call it after
-- 'enterScope'.
moduleEnv :: TopLevelModuleName -> TCM ModuleEnv
moduleEnv m = do
  scope <- getScope
  defs  <- curDefs
  ModuleEnv m (publicQNames scope) (sortDefs defs) <$> liftIO (newIORef M.empty)

initCompileEnv :: GlobalEnv -> ModuleEnv -> SpecialRules -> CompileEnv
initCompileEnv genv menv rewrites = CompileEnv
  { globalEnv         = genv
  , currModule        = menvName menv
  , currModuleEnv     = menv
  , minRecordName     = Nothing
  , isNestedInType    = False
  , locals            = []
  , compilingLocal    = False
  , whereModules      = []
  , copatternsEnabled = False
  , rewrites          = rewrites
  , writeImports      = True
  , writeExports      = True
  , checkNames        = True
  }

initCompileState :: CompileState
initCompileState = CompileState { lcaseUsed = 0 }

runC :: GlobalEnv -> ModuleEnv -> SpecialRules -> C a -> TCM (a, CompileOutput)
runC genv menv rewrites c = evalRWST c (initCompileEnv genv menv rewrites) initCompileState

moduleSetup :: GlobalEnv -> IsMain -> TopLevelModuleName -> Maybe FilePath -> TCM (Recompile ModuleEnv ModuleRes)
moduleSetup genv _ m _ = do
  let opts = globalOptions genv
  -- we never compile primitive modules
  if any (`isPrefixOf` prettyShow m) primModules then pure $ Skip ()
  else do
    -- up to date when the key recorded beside the Haskell is the module's key now (moduleSourceFile), and the
    -- Haskell it says exists does
    key <- moduleKey genv
    src <- moduleSourceFile opts m
    hs <- moduleFileName opts m
    uptodate <- liftIO $ do
      recorded <- doesFileExist src >>= \case
        True  -> lines <$> readFile' src
        False -> pure []
      case recorded of
        [k, "hs"]   | k == key -> doesFileExist hs
        [k, "none"] | k == key -> pure True
        _                      -> pure False
    if uptodate then do
      reportSDoc "agda2hs.compile" 3 $ text "Module " <+> prettyTCM m <+> text " is already up-to-date"
      registerRules genv m
      return $ Skip ()
    else do
      reportSDoc "agda2hs.compile" 3 $ text "Compiling module: " <+> prettyTCM m
      enterScope
      Recompile <$> moduleEnv m

-- | Make the current module's scope the one names are resolved in, as compiling its definitions needs.
enterScope :: TCM ()
enterScope = do
  setScope . iInsideScope =<< curIF
  -- Agda 2.9 no longer recomputes inverse-scope maps in setScope.
  recomputeInverseScope

-- | Record the inline and compile-to rules of a module that is not compiled because it is up to date. Modules
-- compiled after it in the run read them ('isInlinedFunction', 'getCompileToName'); compiling it would have
-- recorded them, so without this a module's Haskell would depend on which of its imports this run compiled.
registerRules :: GlobalEnv -> TopLevelModuleName -> TCM ()
registerRules genv m = do
  -- reading the pragmas needs no scope; its environment's lazy fields are never read
  menv0 <- moduleEnv m
  ruled <- fmap concat $ forM (map snd (menvSortedDefs menv0)) $ \def -> do
    (p, _) <- runC genv menv0 (optRewrites (globalOptions genv)) $ processPragma (defName def)
    return [(def, p) | isRule p (theDef def)]
  unless (null ruled) $ do
    enterScope
    menv <- moduleEnv m
    forM_ ruled $ \(def, p) ->
      withCurrentModule (qnameModule (defName def)) $
        runC genv menv (optRewrites (globalOptions genv)) $ setCurrentRangeQ (defName def) $ case (p, theDef def) of
          (InlinePragma     , _         ) -> checkInlinePragma def
          (CompileToPragma s, Datatype{}) -> checkCompileToDataPragma def s
          (CompileToPragma s, _         ) -> checkCompileToFunctionPragma def s
          _                               -> __IMPOSSIBLE__
  where
    isRule InlinePragma        Function{} = True
    isRule (CompileToPragma _) Datatype{} = True
    isRule (CompileToPragma _) Function{} = True
    isRule _                   _          = False

-- Main compile function
------------------------

compile
  :: GlobalEnv -> ModuleEnv -> IsMain -> Definition
  -> TCM (CompiledDef, CompileOutput)
compile genv menv _ def =
  withCurrentModule (qnameModule qname)
    $ runC genv menv (optRewrites opts)
    $ setCurrentRangeQ qname
    $ compileAndTag <* postCompile
  where
    opts = globalOptions genv
    qname = defName def

    tag []   = []
    tag code = [(nameBindingSite $ qnameName qname, code)]

    compileAndTag :: C CompiledDef
    compileAndTag = tag <$> do
      p <- processPragma qname

      reportSDoc "agda2hs.compile" 5  $ text "Compiling definition:" <+> prettyTCM qname
      reportSDoc "agda2hs.compile" 45 $ text "Pragma:" <+> text (show p)
      reportSDoc "agda2hs.compile" 65 $ text "Compiling definition:" <+> pretty (theDef def)

      isInstance <- anyM (isClassName . instanceClass) $ defInstance def

      reportSDoc "agda2hs.compile" 15  $ text "Is instance?" <+> prettyTCM isInstance

      case (p , theDef def) of
        (NoPragma            , _         ) -> return []
        (ExistingClassPragma , _         ) -> return []
        (UnboxPragma s       , Record{}  ) -> [] <$ checkUnboxPragma def
        (TransparentPragma   , Function{}) -> [] <$ checkTransparentPragma def
        (InlinePragma        , Function{}) -> [] <$ checkInlinePragma def
        (TuplePragma b       , Record{}  ) -> return []
        (CompileToPragma s   , Datatype{}) -> [] <$ checkCompileToDataPragma def s
        (CompileToPragma s   , Function{}) -> [] <$ checkCompileToFunctionPragma def s

        (ClassPragma ms      , Record{}  ) -> pure <$> compileRecord (ToClass ms) def
        (NewTypePragma ds    , Record{}  ) -> pure <$> compileRecord (ToRecord True ds) def
        (NewTypePragma ds    , Datatype{}) -> compileData True ds def
        (DefaultPragma ds    , Datatype{}) -> compileData False ds def
        (DerivePragma s      , _         ) | isInstance -> pure <$> compileInstance (ToDerivation s) def
        (DefaultPragma _     , Axiom{}   ) | isInstance -> pure <$> compileInstance (ToDerivation Nothing) def
        (DefaultPragma _     , _         ) | isInstance -> pure <$> compileInstance ToDefinition def
        (DefaultPragma _     , Axiom{}   ) -> compilePostulate def
        (DefaultPragma _     , Function{}) -> compileFun True def
        (DefaultPragma ds    , Record{}  ) -> pure <$> compileRecord (ToRecord False ds) def

        _ -> agda2hsErrorM $ text "Don't know how to compile" <+> prettyTCM (defName def)

    postCompile :: C ()
    postCompile = whenM (gets $ lcaseUsed >>> (> 0)) $ tellExtension Hs.LambdaCase

verifyOutput ::
  GlobalEnv -> ModuleEnv -> IsMain -> TopLevelModuleName
  -> [(CompiledDef, CompileOutput)] -> TCM ()
verifyOutput _ _ _ m ls = do
  reportSDoc "agda2hs.compile" 5 $ text "Checking generated output before rendering: " <+> prettyTCM m
  ensureUniqueConstructors
  ensureNoOutputFromHsModules
  where
    ensureUniqueConstructors = do
      let allCons = do
            (r, _) <- ls
            (_, a) <- r
            Hs.DataDecl _ _ _ _ cons _ <- a
            Hs.QualConDecl _ _ _ con <- cons
            return $ case con of
              Hs.ConDecl _ n _ -> n
              Hs.InfixConDecl _ _ n _ -> n
              Hs.RecDecl _ n _ -> n
          duplicateCons = filter ((> 1) . length) . group . sort  $ allCons
      when (length duplicateCons > 0) $
        agda2hsErrorM $ vcat (map (\x -> text $ "Cannot generate multiple constructors with the same identifier: " <> Hs.prettyPrint (headWithDefault __IMPOSSIBLE__ x)) duplicateCons)

    ensureNoOutputFromHsModules = unless (null $ concat $ map fst ls) $ do
      let hsModName = hsTopLevelModuleName m
      case hsModuleKind hsModName of
        HsModule -> do
          reportSDoc "agda2hs.compile" 10 $ text "Haskell module" <+> prettyTCM m <+> text "has non-null output."
          agda2hsErrorM $ hsep
            (  pwords "The `Haskell.` namespace are reserved for binding existing Haskell modules, so the module"
            ++ [text "`" <> prettyTCM m <> text "`"]
            ++ pwords "should not contain any"
            ++ [text "`{-# COMPILE AGDA2HS ... #-}`"]
            ++ pwords "pragmas that produce Haskell code."
            )
        PrimModule -> __IMPOSSIBLE__
        AgdaModule -> return ()
