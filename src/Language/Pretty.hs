{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

module Language.Pretty where

import Data.Set qualified as Set
import Data.Map qualified as Map
import Data.List qualified as List

import Prettyprinter

import Base

import Data.Map.Multi qualified as Multi

import Language.Type
import Language.Expr
import Language.Container
import Language.Container.Morphism
import Language.Container.Relation
import Language.Coverage
import Language.Problem

statements :: [Doc ann] -> Doc ann
statements = concatWith \x y -> x <> flatAlt line "; " <> y

parensIf :: Bool -> Doc ann -> Doc ann
parensIf p = if p then parens else id

braced :: [Doc ann] -> Doc ann
braced = encloseSep lbrace rbrace ", "

-- Used for pretty printing with precedence.
data Prec a = Prec Int a

prettyPrec :: Pretty (Prec a) => Int -> a -> Doc ann
prettyPrec n = pretty . Prec n

prettyMinPrec :: Pretty (Prec a) => a -> Doc ann
prettyMinPrec = prettyPrec minBound

prettyMaxPrec :: Pretty (Prec a) => a -> Doc ann
prettyMaxPrec = prettyPrec maxBound

-- Used for pretty printing datatypes with named elements.
newtype Split f a = Split { getSplit :: f (Named a) }

instance (Pretty (f Name), Pretty (Named a), Foldable f, Functor f) => Pretty (Split f a) where
  pretty (Split f)
    | null elements = shape
    | otherwise = nest 2 $ vsep
      [ shape
      , nest 2 . vsep $ "where"
        : List.intersperse "" elements
      ]
    where
      elements = map pretty $ toList f
      shape = pretty $ fmap (.name) f

deriving newtype instance Pretty (Sum Nat)
deriving newtype instance Pretty Lit

prettyCtr :: Name -> Doc ann
prettyCtr = \case
  ":" -> "Cons"
  "[]" -> "Nil"
  c -> pretty c

instance Pretty h => Pretty (Expr l h) where
  pretty = prettyMinPrec

prettyC :: Pretty (Prec b) => Name -> [b] -> Int -> Doc ann
prettyC x [] _ = prettyCtr x
prettyC x xs p = parensIf (p > 2) . sep $ prettyCtr x : map prettyMaxPrec xs

instance Pretty h => Pretty (Prec (Expr l h)) where
  pretty (Prec p e) = case e of
    Tuple xs -> tupled $ map pretty xs
    List xs -> pretty xs
    Nat n -> pretty n
    Ctr c Unit -> prettyCtr c
    Ctr c x -> parensIf (p > 2) $ prettyCtr c <+> prettyPrec 3 x
    Lit l -> pretty l
    Var v -> pretty v
    Lam v (Lams vs x) -> parensIf (p > 1) $
      "\\" <> sep (map pretty (v:vs)) <> "." <+> pretty x
    Case x xs -> parensIf (p > 1) $
      nest 2 $ vsep ["case" <+> pretty x <+> "of", pretty (Elim xs)]
    App (Apps f xs) x ->
      group . parensIf (p > 2) . nest 2 . vsep $
        prettyPrec 2 f : map (prettyPrec 3) (xs ++ [x])
    Prj i x -> prettyMaxPrec x <> "." <> pretty i
    Elim xs ->
      let
        arms = xs <&> \case
          (c, Lams vs x) ->
            sep (prettyCtr c : map pretty vs) <+> "->" <+> pretty x
      in flatAlt (statements arms) $ encloseSep "{ " " }" "; " arms
    Hole h -> pretty h

instance Pretty h => Pretty (Named (Expr l h)) where
  pretty (Named name (asProgram -> Lams args expr)) =
    nest 2 $ sep (pretty name : map pretty args) <+>
      "=" <> softline <> pretty expr

instance Pretty Example where
  pretty (Example [] out) = pretty out
  pretty (Example ins out) =
    sep (map prettyMaxPrec ins) <+> "->" <+> pretty out

instance Pretty (Named Example) where
  pretty (Named name (Example ins out)) =
    sep (pretty name : map prettyMaxPrec ins ++ ["=", pretty out])

instance Pretty Base where
  pretty = viaShow

instance Pretty Constraint where
  pretty = \case
    Eq  a -> "Eq"  <+> pretty a
    Ord a -> "Ord" <+> pretty a

instance Pretty Mono where
  pretty = prettyMinPrec

instance Pretty (Prec Mono) where
  pretty (Prec p t) = case t of
    Free v -> pretty v
    Product ts -> tupled $ map pretty ts
    Data d [] -> pretty d
    Data d ts -> parensIf (p > 2) $ pretty d <+> sep (prettyPrec 3 <$> ts)
    Base b -> pretty b

instance Pretty (Named Mono) where
  pretty (Named x t) = pretty x <+> ":" <+> pretty t

instance Pretty Signature where
  pretty Signature { constraints, inputs, output } = cat
    [ constrs constraints
    , arguments inputs
    , pretty output
    ] where
      constrs [] = ""
      constrs [x] = pretty x <+> "=> "
      constrs xs = tupled (map pretty xs) <+> "=> "
      arguments [] = ""
      arguments xs = braced (map pretty xs) <+> "-> "

instance Pretty (Named Signature) where
  pretty (Named name sig) = pretty name <+> ":" <+> pretty sig

instance Pretty (Named DataDef) where
  pretty (Named name definition) =
    "data" <+> sep (pretty name : map pretty definition.arguments) <+>
      "=" <+> concatWith (surround " | ") (definition.constructors <&>
      \c -> sep (prettyCtr c.name : map prettyMaxPrec (projections c.value)))

instance Pretty DataContext where
  pretty (DataContext datatypes) = statements $ map pretty datatypes

instance Pretty Problem where
  pretty = prettyNamed "_"

instance Pretty (Named Problem) where
  pretty (Named name (Problem sig exs)) = statements $
    prettyNamed name sig : map (prettyNamed name) exs

instance Pretty Arg where
  pretty (Arg t es) = pretty t <+> "=" <+> braced (map pretty es)

instance Pretty (Named Arg) where
  pretty (Named name (Arg t es)) = prettyNamed name t
    <+> "=" <+> braced (map pretty es)

instance Pretty Args where
  pretty (Args inputs output) = statements
    [ statements $ map pretty inputs
    , "->" <+> pretty output
    ]

instance Pretty (Named Nat) where
  pretty n = pretty n.name <> pretty n.value

instance Pretty Container where
  pretty (Container s p) = pretty s <+> braced xs
    where
      xs = Map.assocs p <&> \(i, x) -> pretty i <+> "=" <+> pretty x

instance Pretty (Set Position) where
  pretty ps = case Set.toList ps of
    [x] -> pretty x
    xs  -> braced $ map pretty xs

instance Pretty Pattern where
  pretty patt
    | null relations = inputs
    | otherwise = inputs <+> "|" <+>
      concatWith (surround ", ") (pretty <$> relations)
    where
      inputs = sep (map prettyMaxPrec patt.shapes)
      relations = filter relevant patt.relations

instance Pretty Rule where
  pretty Rule { input, output, origins }
    | null input.shapes = pretty output
    | otherwise = pretty input <+> "->" <+> out
    where
      out = pretty $ fmap (`Multi.lookup` origins) output

instance Pretty (Named Rule) where
  pretty (Named name Rule { input, output, origins })
    | null input.shapes = pretty name <+> "=" <+> out
    | otherwise = pretty name <+> pretty input <+> "=" <+> out
    where
      out = pretty $ fmap (`Multi.lookup` origins) output

instance Pretty (Named [Rule]) where
  pretty (Named name xs) = statements $ prettyNamed name <$> xs

instance Pretty Conflict where
  pretty = \case
    ArgumentMismatch ts es -> "ArgumentMismatch!" <+> indent 2
      (vcat [pretty ts, pretty es])
    ShapeConflict xs -> "ShapeConflict!" <+> indent 2 (pretty xs)
    MagicOutput x -> "MagicOutput!" <+> indent 2 (pretty x)
    PositionConflict xs -> "PositionConflict!" <+> indent 2 (pretty xs)
    MonoConflict xs -> "MonoConflict!" <+> indent 2 (pretty xs)

instance Pretty Coverage where
  pretty = \case
    Total -> "Total"
    Partial -> "Partial"
    Missing c -> vcat $ "Partial, missing cases:"
      : map pretty (Set.toList c)

eqClass :: Pretty a => Set a -> Doc ann
eqClass s = case Set.toList s of
  [x] -> pretty x
  xs  -> concatWith (surround " == ") $ map pretty xs

instance Pretty Relation where
  pretty = \case
    RelEq  eq  -> concatWith (surround " /= ") . fmap eqClass $ Set.toList eq
    RelOrd ord -> concatWith (surround " < " ) $ fmap eqClass ord
