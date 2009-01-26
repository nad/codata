------------------------------------------------------------------------
-- The universe used to define breadth-first manipulations of trees
------------------------------------------------------------------------

module BreadthFirst.Universe where

open import Data.Product
open import Data.Colist as Colist
open import Relation.Binary
open import Relation.Binary.Simple
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.Product.Pointwise
open import Coinduction

import Tree
import Stream

infixr 2 _⊗_

data Kind : Set where
  μ : Kind -- Codata.
  ν : Kind -- Data.

data U : Kind → Set1 where
  tree   : ∀ {k} (a : U k) → U ν
  stream : ∀ {k} (a : U k) → U ν
  colist : ∀ {k} (a : U k) → U ν
  _⊗_    : ∀ {k₁ k₂} (a : U k₁) (b : U k₂) → U μ
  ⌈_⌉    : (A : Set) → U μ

El : ∀ {k} → U k → Set
El (tree a)   = Tree.Tree (El a)
El (stream a) = Stream.Stream (El a)
El (colist a) = Colist (El a)
El (a ⊗ b)    = El a × El b
El ⌈ A ⌉      = A

-- This equality relation could be improved.

Eq : ∀ {k} (a : U k) → Rel (El a)
Eq (tree a)   = Tree._≈_
Eq (stream a) = Stream._≈_
Eq (colist a) = Colist._≈_
Eq (a ⊗ b)    = Eq a ×-Rel Eq b
Eq ⌈ A ⌉      = _≡_

-- Conditional coinduction.

∞? : Kind → Set1 → Set1
∞? μ = λ A → A
∞? ν = ∞₁

♭? : ∀ k {A} → ∞? k A → A
♭? μ x = x
♭? ν x = ♭₁ x
