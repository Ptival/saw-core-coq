{- |
Module      : Language.Coq.Pretty
Copyright   : Galois, Inc. 2018
License     : BSD3
Maintainer  : atomb@galois.com
Stability   : experimental
Portability : portable
-}

module Language.Coq.Pretty where

import Data.List (intersperse)
import Text.PrettyPrint.ANSI.Leijen
import Language.Coq.AST
import Prelude hiding ((<$>), (<>))

-- TODO: import SAWCore pretty-printer?
tightSepList :: Doc -> [Doc] -> Doc
tightSepList _ [] = empty
tightSepList _ [d] = d
tightSepList s (d:l) = d <> s <+> commaSepList l

looseSepList :: Doc -> [Doc] -> Doc
looseSepList _ [] = empty
looseSepList _ [d] = d
looseSepList s (d:l) = d <+> s <+> commaSepList l

commaSepList, starSepList, semiSepList :: [Doc] -> Doc
commaSepList = tightSepList comma
starSepList = looseSepList (text "*")
semiSepList = tightSepList semi

period :: Doc
period = text "."

ppIdent :: Ident -> Doc
ppIdent = text

ppBinder :: Binder -> Doc
ppBinder (Binder x Nothing)  = ppIdent x
ppBinder (Binder x (Just t)) = parens (ppIdent x <+> colon <+> ppTerm t)

ppBinders :: [Binder] -> Doc
ppBinders = hsep . map ppBinder

ppMaybeTy :: Maybe Type -> Doc
ppMaybeTy Nothing = empty
ppMaybeTy (Just ty) = colon <+> ppTerm ty

ppSort :: Sort -> Doc
ppSort Prop = text "Prop"
ppSort Set = text "Set"
ppSort Type = text "Type"

ppPi :: [Binder] -> Doc
ppPi bs = hsep $ intersperse (text "->") (map ppBinder bs)

ppTerm :: Term -> Doc
ppTerm e =
  case e of
    Forall bs t ->
      text "forall" <+> ppBinders bs <> comma <+> ppTerm t
    Lambda bs t ->
      parens (text "fun" <+> ppBinders bs <+> text "=>" <+> ppTerm t)
    Pi bs t ->
      ppPi bs <+> text "->" <+> ppTerm t
    Let x bs mty t body ->
      text "let" <+> ppIdent x <+> ppBinders bs <+> ppMaybeTy mty <+>
      text ":=" <+> ppTerm t <+> text "in" <+> ppTerm body
    If c t f ->
      text "if" <+> ppTerm c <+>
      text "then" <+> ppTerm t <+>
      text "else" <+> ppTerm f
    App f args ->
      parens (hsep (ppTerm f : map ppTerm args))
    Sort s ->
      ppSort s
    Var x ->
      ppIdent x
    NatLit i ->
      integer i
    List ts ->
      list (map ppTerm ts)

ppDecl :: Decl -> Doc
ppDecl decl = case decl of
  Definition nm bs mty body ->
    (nest 2 $
     hsep ([text "Definition", text nm] ++
          map ppBinder bs ++
          [ppMaybeTy mty, text ":="]) <$>
     ppTerm body <> period) <> hardline