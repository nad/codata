------------------------------------------------------------------------
-- Breadth-first manipulations of trees
------------------------------------------------------------------------

module BreadthFirst where

open import Data.Function
open import Data.Unit
open import Data.List.NonEmpty using (List⁺; [_]; _∷_)
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality1

open import BreadthFirst.Universe
open import BreadthFirst.Programs
open import Tree
open import Stream using (Stream; _≺_)

module R {A B} (t : Tree A) (ls : Stream B) where

  t′ : Prog (tree ⌈ A ⌉)
  t′ = ⇒P (tree ⌈ A ⌉) t

  r : Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
  r ~ lab t′ (↓ ⌈ ls ⌉ ≺ snd r)

label : forall {A B} -> Tree A -> Stream B -> Tree B
label t ls = P⇒ (fst (R.r t ls))

⇒W⇒-lemma : forall {A} (t : Tree A) ->
            map (const tt) (W⇒ (⇒W (tree ⌈ A ⌉) t)) ≈ map (const tt) t
⇒W⇒-lemma (tree leaf)         ~ tree leaf
⇒W⇒-lemma (tree (node l x r)) ~
  tree (node (⇒W⇒-lemma l) ≡-refl (⇒W⇒-lemma r))

shape-preserved′
  : forall {k} {a : U k} {B}
    (t : Prog (tree a)) (lss : Prog (stream ⌈ Stream B ⌉)) ->
    map (const tt) (P⇒  (fst (lab t lss))) ≈ map (const tt) (P⇒ t)
shape-preserved′ t lss with P⇒W t
shape-preserved′ t lss | leaf       ~ tree leaf
shape-preserved′ t lss | node l _ r with P⇒W lss
shape-preserved′ t lss | node l _ r | ⌈ x ≺ ls ⌉ ≺ lss′ ~
  tree (node (shape-preserved′ l lss′) ≡-refl (shape-preserved′ r _))

-- shape-preserved pattern matches in order to force R.r to evaluate
-- sufficiently.

shape-preserved
  : forall {A B} (t : Tree A) (ls : Stream B) ->
    map (const tt) (label t ls) ≈ map (const tt) t
shape-preserved {A} (tree leaf)         ls        = tree leaf
shape-preserved {A} (tree (node l x r)) (l′ ≺ ls) =
  tree (destruct≈ (trans
    (shape-preserved′ (⇒P (tree ⌈ A ⌉) t) (↓ ⌈ lls ⌉ ≺ snd (R.r t lls)))
    (⇒W⇒-lemma t)))
  where
  t   = tree (node l x r)
  lls = l′ ≺ ls

concat : forall {A} -> Prog (colist ⌈ List⁺ A ⌉) -> Prog (colist ⌈ A ⌉)
concat xss with P⇒W xss
concat xss | []                ~ ↓ []
concat xss | ⌈ [ x ] ⌉  ∷ xss′ ~ ↓ ⌈ x ⌉ ∷ concat xss′
concat xss | ⌈ x ∷ xs ⌉ ∷ xss′ ~ ↓ ⌈ x ⌉ ∷ concat (↓ ⌈ xs ⌉ ∷ xss′)

-- TODO:
--
-- Prove that concat (flatten (label t ls)) is a prefix of ls.
