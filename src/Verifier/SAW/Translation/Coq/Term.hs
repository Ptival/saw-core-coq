{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE ViewPatterns #-}

{- |
Module      : Verifier.SAW.Translation.Coq
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Verifier.SAW.Translation.Coq.Term where

import           Control.Lens                                  (makeLenses, over, set, to, view)
import qualified Control.Monad.Except                          as Except
import qualified Control.Monad.Fail                            as Fail
import           Control.Monad.Reader                          hiding (fail, fix)
import           Control.Monad.State                           hiding (fail, fix, state)
import           Data.List                                     (intersperse)
import           Data.Maybe                                    (fromMaybe)
import           Prelude                                       hiding (fail)
import           Text.PrettyPrint.ANSI.Leijen                  hiding ((<$>))

import qualified Data.Vector                                   as Vector (reverse)
import qualified Language.Coq.AST                              as Coq
import qualified Language.Coq.Pretty                           as Coq
import           Verifier.SAW.Recognizer
import           Verifier.SAW.SharedTerm
import           Verifier.SAW.Term.Functor
import           Verifier.SAW.Translation.Coq.Monad
import           Verifier.SAW.Translation.Coq.SpecialTreatment

data TranslationState = TranslationState

  { _globalDeclarations :: [String]
  -- ^ Some Cryptol terms seem to capture the name and body of some functions
  -- they use (whether from the Cryptol prelude, or previously defined in the
  -- same file).  We want to translate those exactly once, so we need to keep
  -- track of which ones have already been translated.

  , _localDeclarations :: [Coq.Decl]
  -- ^ Because some terms capture their dependencies, translating one term may
  -- result in multiple declarations: one for the term itself, but also zero or
  -- many for its dependencies.  We store all of those in this, so that a caller
  -- of the translation may retrieve all the declarations needed to translate
  -- the term.  The translation function itself will return only the declaration
  -- for the term being translated.

  , _localEnvironment  :: [String]
  -- ^ TODO: describe me

  }
  deriving (Show)

makeLenses ''TranslationState

-- | Extract the list of names from a list of Coq declarations.  Not all
-- declarations have names, e.g. comments and code snippets come without names.
namedDecls :: [Coq.Decl] -> [String]
namedDecls = concatMap filterNamed
  where
    filterNamed :: Coq.Decl -> [String]
    filterNamed (Coq.Axiom n _)                               = [n]
    filterNamed (Coq.Comment _)                               = []
    filterNamed (Coq.Definition n _ _ _)                      = [n]
    filterNamed (Coq.InductiveDecl (Coq.Inductive n _ _ _ _)) = [n]
    filterNamed (Coq.Snippet _)                               = []

-- | Retrieve the names of all local and global declarations from the
-- translation state.
getNamesOfAllDeclarations ::
  TermTranslationMonad m =>
  m [String]
getNamesOfAllDeclarations = view allDeclarations <$> get
  where
    allDeclarations =
      to (\ (TranslationState {..}) -> namedDecls _localDeclarations ++ _globalDeclarations)

type TermTranslationMonad m = TranslationMonad TranslationState m

runTermTranslationMonad ::
  TranslationConfiguration ->
  [String] ->
  [String] ->
  (forall m. TermTranslationMonad m => m a) ->
  Either (TranslationError Term) (a, TranslationState)
runTermTranslationMonad configuration globalDecls localEnv =
  runTranslationMonad configuration
  (TranslationState { _globalDeclarations = globalDecls
                    , _localDeclarations  = []
                    , _localEnvironment   = localEnv
                    })

findIdentTranslation ::
  TranslationConfigurationMonad m =>
  Ident -> m Ident
findIdentTranslation i =
  atUseSite <$> findSpecialTreatment i >>= \case
    UsePreserve                         -> pure $ mkIdent translatedModuleName (identName i)
    UseRename   targetModule targetName -> pure $ mkIdent (fromMaybe translatedModuleName targetModule) targetName
    UseReplace  _                       -> error $ "This identifier should have been replaced already: " ++ show i
  where
    translatedModuleName = translateModuleName (identModule i)

translateIdent ::
  TranslationConfigurationMonad m =>
  Ident -> m Coq.Ident
translateIdent = (show <$>) <$> findIdentTranslation

translateIdentUnqualified ::
  TranslationConfigurationMonad m =>
  Ident -> m Coq.Ident
translateIdentUnqualified = (identName <$>) <$> findIdentTranslation

translateSort :: Sort -> Coq.Sort
translateSort s = if s == propSort then Coq.Prop else Coq.Type

flatTermFToExpr ::
  TermTranslationMonad m =>
  (Term -> m Coq.Term) ->
  FlatTermF Term ->
  m Coq.Term
flatTermFToExpr go tf = -- traceFTermF "flatTermFToExpr" tf $
  case tf of
    GlobalDef i   -> Coq.Var <$> (("@" ++) <$> translateIdent i)
    UnitValue     -> pure (Coq.Var "tt")
    UnitType      -> pure (Coq.Var "unit")
    PairValue x y -> Coq.App (Coq.Var "pair") <$> traverse go [x, y]
    PairType x y  -> Coq.App (Coq.Var "prod") <$> traverse go [x, y]
    PairLeft t    -> Coq.App <$> pure (Coq.Var "SAWCoreScaffolding.fst") <*> traverse go [t]
    PairRight t   -> Coq.App <$> pure (Coq.Var "SAWCoreScaffolding.snd") <*> traverse go [t]
    -- TODO: maybe have more customizable translation of data types
    DataTypeApp n is as ->
      Coq.App
        <$> (Coq.Var <$> (("@" ++) <$> translateIdentUnqualified n))
        <*> traverse go (is ++ as)
    -- TODO: maybe have more customizable translation of data constructors
    CtorApp n is as ->
      Coq.App
        <$> (Coq.Var <$> (("@" ++) <$> translateIdentUnqualified n))
        <*> traverse go (is ++ as)
    -- TODO: support this next!
    RecursorApp typeEliminated parameters motive eliminators indices termEliminated ->
      Coq.App
      <$> (Coq.Var <$> ((\ i -> "@" ++ i ++ "_rect") <$> translateIdentUnqualified typeEliminated))
      <*> (
      traverse go $
      parameters ++ [motive] ++ map snd eliminators ++ indices ++ [termEliminated]
      )
    Sort s -> pure (Coq.Sort (translateSort s))
    NatLit i -> pure (Coq.NatLit i)
    ArrayValue _ vec -> do
      let addElement accum element = do
            elementTerm <- go element
            return (Coq.App (Coq.Var "Vector.cons")
                    [Coq.Var "_", elementTerm, Coq.Var "_", accum]
                   )
        in
        foldM addElement (Coq.App (Coq.Var "Vector.nil") [Coq.Var "_"]) (Vector.reverse vec)
    StringLit s -> pure (Coq.Scope (Coq.StringLit s) "string")
    ExtCns (EC _ _ _) -> notSupported

    -- NOTE: The following requires the coq-extensible-records library, because
    -- Coq records are nominal rather than structural
    -- In this library, record types are represented as:
    -- (record (Fields FSNil))                         is the type of the empty record
    -- (record (Fields (FSCons ("x" %e nat) FSNil)))   has one field "x" of type "nat"
    RecordType fs ->
      let makeField name typ = do
            typTerm <- go typ
            return (Coq.App (Coq.Var "@pair")
              [ Coq.Var "field"
              , Coq.Var "_"
              , Coq.Scope (Coq.StringLit name) "string"
              , typTerm
              ])
      in
      let addField accum (name, typ) = do
            fieldTerm <- makeField name typ
            return (Coq.App (Coq.Var "FScons") [fieldTerm, accum])
      in
      do
        fields <- foldM addField (Coq.Var "FSnil") fs
        return $ Coq.App (Coq.Var "record") [ Coq.App (Coq.Var "Fields") [fields] ]

    RecordValue fs ->
      let makeField name val = do
            valTerm <- go val
            return (Coq.App (Coq.Var "@record_singleton")
              [ Coq.Var "_"
              , Coq.Scope (Coq.StringLit name) "string"
              , valTerm
              ])
      in
      let addField accum (name, typ) = do
            fieldTerm <- makeField name typ
            return (Coq.App (Coq.Var "@Rjoin") [Coq.Var "_", Coq.Var "_", fieldTerm, accum])
      in
      foldM addField (Coq.Var "record_empty") fs
    RecordProj r f -> do
      rTerm <- go r
      return (Coq.App (Coq.Var "@Rget")
              [ Coq.Var "_"
              , rTerm
              , Coq.Scope (Coq.StringLit f) "string"
              , Coq.Var "_"
              , Coq.Ltac "simpl; exact eq_refl"
              ])
  where
    notSupported = Except.throwError $ NotSupported errorTerm
    --badTerm = throwError $ BadTerm errorTerm
    errorTerm = Unshared $ FTermF tf
    --asString (asFTermF -> Just (StringLit s)) = pure s
    --asString _ = badTerm

-- | Recognizes an $App (App "Cryptol.seq" n) x$ and returns ($n$, $x$).
asSeq :: Fail.MonadFail f => Recognizer f Term (Term, Term)
asSeq t = do (f, args) <- asApplyAllRecognizer t
             fid <- asGlobalDef f
             case (fid, args) of
               ("Cryptol.seq", [n, x]) -> return (n,x)
               _ -> Fail.fail "not a seq"

asApplyAllRecognizer :: Fail.MonadFail f => Recognizer f Term (Term, [Term])
asApplyAllRecognizer t = do _ <- asApp t
                            return $ asApplyAll t

-- | Run a translation, but keep changes to the environment local to it,
-- restoring the current environment before returning.
withLocalLocalEnvironment :: TermTranslationMonad m => m a -> m a
withLocalLocalEnvironment action = do
  env <- view localEnvironment <$> get
  result <- action
  modify $ set localEnvironment env
  return result

mkDefinition :: Coq.Ident -> Coq.Term -> Coq.Decl
mkDefinition name (Coq.Lambda bs t) = Coq.Definition name bs Nothing t
mkDefinition name t = Coq.Definition name [] Nothing t

translateParams ::
  TermTranslationMonad m =>
  [(String, Term)] -> m [Coq.Binder]
translateParams [] = return []
translateParams ((n, ty):ps) = do
  ty' <- translateTerm ty
  modify $ over localEnvironment (n :)
  ps' <- translateParams ps
  return (Coq.Binder n (Just ty') : ps')

translatePi :: TermTranslationMonad m => [(String, Term)] -> Term -> m Coq.Term
translatePi binders body = withLocalLocalEnvironment $ do
  bindersT <- forM binders $ \ (b, bType) -> do
    bTypeT <- translateTerm bType
    modify $ over localEnvironment (b :)
    let n = if b == "_" then Nothing else Just b
    return (Coq.PiBinder n bTypeT)
  bodyT <- translateTerm body
  return $ Coq.Pi bindersT bodyT

translateTerm :: TermTranslationMonad m => Term -> m Coq.Term
translateTerm t = withLocalLocalEnvironment $ do
  -- traceTerm "translateTerm" t $
  -- NOTE: env is in innermost-first order
  env <- view localEnvironment <$> get
  case t of

    (asFTermF -> Just tf)  -> flatTermFToExpr (go env) tf

    (asPi -> Just _) -> translatePi params e
      where
        (params, e) = asPiList t

    (asLambda -> Just _) -> do
      paramTerms <- translateParams params
      Coq.Lambda <$> pure paramTerms
                 -- env is in innermost first (reverse) binder order
                 <*> go ((reverse paramNames) ++ env) e
        where
          -- params are in normal, outermost first, order
          (params, e) = asLambdaList t
          -- param names are in normal, outermost first, order
          paramNames = map fst $ params

    (asApp -> Just _) ->
      -- asApplyAll: innermost argument first
      let (f, args) = asApplyAll t
      in
      case f of
      (asGlobalDef -> Just i) ->
        case i of
        "Prelude.ite" ->
          case args of
          -- `rest` can be non-empty in examples like:
          -- (if b then f else g) arg1 arg2
          _ty : c : tt : ft : rest -> do
            ite <- Coq.If <$> go env c <*> go env tt <*> go env ft
            case rest of
              [] -> return ite
              _  -> Coq.App ite <$> mapM (go env) rest
          _ -> badTerm
        -- NOTE: the following works for something like CBC, because computing
        -- the n-th block only requires n steps of recursion
        -- FIXME: (pun not intended) better conditions for when this is safe to do
        "Prelude.fix" ->
          case args of
          []  -> notSupported "call to Prelude.fix with no argument"
          [_] -> notSupported "call to Prelude.fix with 1 argument"
          resultType : lambda : rest ->
            case resultType of
            -- TODO: check that 'n' is finite
            (asSeq -> Just (n, _)) ->
              case lambda of

              (asLambda -> Just (x, seqType, body)) | seqType == resultType ->
                  do
                    len <- go env n
                    expr <- go (x:env) body
                    seqTypeT <- go env seqType
                    defaultValueT <- defaultTermForType resultType
                    let iter =
                          Coq.App (Coq.Var "iter")
                          [ len
                          , Coq.Lambda [Coq.Binder x (Just seqTypeT)] expr
                          , defaultValueT
                          ]
                    case rest of
                      [] -> return iter
                      _  -> Coq.App iter <$> mapM (go env) rest
              _ -> badTerm
            -- NOTE: there is currently one instance of `fix` that will trigger
            -- `notSupported`.  It is used in `Cryptol.cry` when translating
            -- `iterate`, which generates an infinite stream of nested
            -- applications of a given function.

            (asPiList -> (pis, afterPis)) ->
              -- NOTE: this will output some code, but it is likely that Coq
              -- will reject it for not being structurally recursive.
              case lambda of
              (asLambdaList -> ((recFn, _) : binders, body)) -> do
                let (_binderPis, otherPis) = splitAt (length binders) pis
                (bindersT, typeT, bodyT) <- withLocalLocalEnvironment $ do
                  -- this is very ugly...
                  modify $ over localEnvironment (recFn :)
                  bindersT <- mapM
                    (\ (b, bType) -> do
                      env' <- view localEnvironment <$> get
                      bTypeT <- go env' bType
                      modify $ over localEnvironment (b :)
                      return $ Coq.Binder b (Just bTypeT)
                    )
                    binders
                  typeT <- translatePi otherPis afterPis
                  env' <- view localEnvironment <$> get
                  bodyT <- go env' body
                  return (bindersT, typeT, bodyT)
                let fix = Coq.Fix recFn bindersT typeT bodyT
                case rest of
                  [] -> return fix
                  _  -> notSupported "THAT" -- Coq.App fix <$> mapM (go env) rest
              _ -> notSupported "call to Prelude.fix without lambda"

        _ ->
          atUseSite <$> findSpecialTreatment i >>= \case
          UseReplace replacement -> return replacement
          _                      -> Coq.App <$> go env f <*> traverse (go env) args
      _ -> Coq.App <$> go env f <*> traverse (go env) args

    (asLocalVar -> Just n)
      | n < length env -> Coq.Var <$> pure (env !! n)
      | otherwise -> Except.throwError $ LocalVarOutOfBounds t

  -- Constants come with a body
    (unwrapTermF -> Constant n body) -> do
      configuration <- ask
      let renamed = translateConstant (notations configuration) n
      alreadyTranslatedDecls <- getNamesOfAllDeclarations
      let definitionsToSkip = skipDefinitions configuration
      if elem renamed alreadyTranslatedDecls || elem renamed definitionsToSkip
        then Coq.Var <$> pure renamed
        else do
        b <- go env body
        modify $ over localDeclarations $ (mkDefinition renamed b :)
        Coq.Var <$> pure renamed

    _ -> {- trace "translateTerm fallthrough" -} notSupported "fallthrough"

  where
    badTerm          = Except.throwError $ BadTerm t
    notSupported lbl = return (Coq.App (Coq.Var "error") [Coq.StringLit ("Not supported: " ++ lbl)])
    go env term      = do
      modify $ set localEnvironment env
      translateTerm term

-- | In order to turn fixpoint computations into iterative computations, we need
-- to be able to create "dummy" values at the type of the computation.  For now,
-- we will support arbitrary nesting of vectors of boolean values.
defaultTermForType ::
  TermTranslationMonad m =>
  Term -> m Coq.Term
defaultTermForType typ = do
  case typ of

    (asSeq -> Just (n, typ')) -> do
      seqConst <- translateIdent (mkIdent (mkModuleName ["Cryptol"]) "seqConst")
      nT       <- translateTerm n
      typ'T    <- translateTerm typ'
      defaultT <- defaultTermForType typ'
      return $ Coq.App (Coq.Var seqConst) [ nT, typ'T, defaultT ]

    (asBoolType -> Just ()) -> do
      falseT <- translateIdent (mkIdent preludeName "False")
      return $ Coq.Var falseT

    _ ->
      return $ Coq.App (Coq.Var "error")
      [Coq.StringLit ("Could not generate default value of type " ++ showTerm typ)]

    -- _ -> Except.throwError $ CannotCreateDefaultValue typ

translateTermToDocWith ::
  TranslationConfiguration ->
  [String] ->
  [String] ->
  (Coq.Term -> Doc) ->
  Term ->
  Either (TranslationError Term) Doc
translateTermToDocWith configuration globalDecls localEnv f t = do
  (term, state) <- runTermTranslationMonad configuration globalDecls localEnv (translateTerm t)
  let decls = view localDeclarations state
  return
    $ ((vcat . intersperse hardline . map Coq.ppDecl . reverse) decls)
    <$$> (if null decls then empty else hardline)
    <$$> f term

translateDefDoc ::
  TranslationConfiguration ->
  [String] ->
  Coq.Ident -> Term ->
  Either (TranslationError Term) Doc
translateDefDoc configuration globalDecls name =
  translateTermToDocWith configuration globalDecls [name] (\ term -> Coq.ppDecl (mkDefinition name term))
