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
r t ls = lab t (↓ lss)
  where lss ~ ♯₁ (⌈ ls ⌉ ≺ snd (r t ls))

label : ∀ {A B} → Tree A → Stream B → Tree B
label t ls = ⟦ fst (r ⟦ a ∣ t ⟧⁻¹ ls) ⟧
  where a = tree ⌈ _ ⌉

reflect-reify : ∀ {A} (t : Tree A) →
                reflect (reify (tree ⌈ A ⌉) t) ≈ t
reflect-reify leaf         = leaf
reflect-reify (node l x r) = node l′ PropEq.refl r′
  where
  l′ ~ ♯ reflect-reify (♭ l)
  r′ ~ ♯ reflect-reify (♭ r)

shape-preserved′
  : ∀ {k} {a : U k} {B}
    (t : Prog (tree a)) (lss : Prog (stream ⌈ Stream B ⌉)) →
    map (const tt) ⟦ fst (lab t lss) ⟧ ≈ map (const tt) ⟦ t ⟧
shape-preserved′ t lss with whnf t
shape-preserved′ t lss | leaf       = leaf
shape-preserved′ t lss | node l _ r with whnf lss
shape-preserved′ t lss | node l _ r | ⌈ x ≺ ls ⌉ ≺ lss′ =
  node l′ PropEq.refl r′
  where
  l′ ~ ♯ shape-preserved′ l lss′
  r′ ~ ♯ shape-preserved′ r _

shape-preserved
  : ∀ {A B} (t : Tree A) (ls : Stream B) →
    map (const tt) (label t ls) ≈ map (const tt) t
shape-preserved t ls =
  trans (shape-preserved′ ⟦ tree ⌈ _ ⌉ ∣ t ⟧⁻¹ _)
        (map-cong (const tt) (reflect-reify t))

concat : ∀ {A} → Prog (colist ⌈ List⁺ A ⌉) → Prog (colist ⌈ A ⌉)
concat xss with whnf xss
concat xss | []                = ↓ ♯₁ []
concat xss | ⌈ [ x ] ⌉  ∷ xss′ = ↓ concat′ where concat′ ~ ♯₁ (⌈ x ⌉ ∷ concat xss′)
concat xss | ⌈ x ∷ xs ⌉ ∷ xss′ = ↓ concat′ where concat′ ~ ♯₁ (⌈ x ⌉ ∷ concat (↓ ♯₁ (⌈ xs ⌉ ∷ xss′)))

-- TODO:
--
-- Prove that concat (flatten (label t ls)) is a prefix of ls.
