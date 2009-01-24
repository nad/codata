------------------------------------------------------------------------
-- Breadth-first manipulations of trees
------------------------------------------------------------------------

module BreadthFirst where

open import Coinduction
open import Data.Function
open import Data.Unit
open import Data.List.NonEmpty using (List⁺; [_]; _∷_)
import Relation.Binary.PropositionalEquality as PropEq

open import BreadthFirst.Universe
open import BreadthFirst.Programs
open import Tree
open import Stream using (Stream; _≺_)

r : ∀ {k B} {a : U k} (t : Prog (tree a)) (ls : Stream B) →
    Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
r t ls = lab t (↓ ⌈ ls ⌉ ≺ snd‿r)
  where snd‿r ~ ♯₁ snd (r t ls)

label : ∀ {A B} → Tree A → Stream B → Tree B
label t ls = P⇒ (fst (r (⇒P (tree ⌈ _ ⌉) t) ls))

⇒W⇒-lemma : ∀ {A} (t : Tree A) → W⇒ (⇒W (tree ⌈ A ⌉) t) ≈ t
⇒W⇒-lemma leaf         = leaf
⇒W⇒-lemma (node l x r) = node l′ PropEq.refl r′
  where
  l′ ~ ♯ ⇒W⇒-lemma (♭ l)
  r′ ~ ♯ ⇒W⇒-lemma (♭ r)

shape-preserved′
  : ∀ {k} {a : U k} {B}
    (t : Prog (tree a)) (lss : Prog (stream ⌈ Stream B ⌉)) →
    map (const tt) (P⇒ (fst (lab t lss))) ≈ map (const tt) (P⇒ t)
shape-preserved′ t lss with P⇒W t
shape-preserved′ t lss | leaf       = leaf
shape-preserved′ t lss | node l _ r with P⇒W lss
shape-preserved′ t lss | node l _ r | ⌈ x ≺ ls ⌉ ≺ lss′ =
  node l′ PropEq.refl r′
  where
  l′ ~ ♯ shape-preserved′ (♭₁ l) (♭₁ lss′)
  r′ ~ ♯ shape-preserved′ (♭₁ r) _

shape-preserved
  : ∀ {A B} (t : Tree A) (ls : Stream B) →
    map (const tt) (label t ls) ≈ map (const tt) t
shape-preserved t ls =
  trans (shape-preserved′ (⇒P (tree ⌈ _ ⌉) t) _)
        (map-cong (const tt) (⇒W⇒-lemma t))

concat : ∀ {A} → Prog (colist ⌈ List⁺ A ⌉) → Prog (colist ⌈ A ⌉)
concat xss with P⇒W xss
concat xss | []                = ↓ []
concat xss | ⌈ [ x ] ⌉  ∷ xss′ = ↓ ⌈ x ⌉ ∷ concat′ where concat′ ~ ♯₁ concat (♭₁ xss′)
concat xss | ⌈ x ∷ xs ⌉ ∷ xss′ = ↓ ⌈ x ⌉ ∷ concat′ where concat′ ~ ♯₁ concat (↓ ⌈ xs ⌉ ∷ xss′)

-- TODO:
--
-- Prove that concat (flatten (label t ls)) is a prefix of ls.
