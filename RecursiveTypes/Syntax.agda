------------------------------------------------------------------------
-- Recursive types and potentially infinite trees
------------------------------------------------------------------------

module RecursiveTypes.Syntax where

open import Data.Nat
open import Data.Fin
open import Coinduction

infixr 10 _⟶_
infix  10 ν_⟶_

-- Recursive types, indexed on the maximum number of free variables. I
-- use the character ν rather than μ because the (unfoldings of the)
-- types can be infinite.

-- Note that no attempt is made to ensure that the variable bound in
-- ν_⟶_ is actually used.

data Ty (n : ℕ) : Set where
  ⊥    : Ty n
  ⊤    : Ty n
  var  : (x : Fin n) → Ty n
  _⟶_  : (τ₁ τ₂ : Ty n) → Ty n
  ν_⟶_ : (τ₁ τ₂ : Ty (suc n)) → Ty n

-- Potentially infinite trees.

data Tree (n : ℕ) : Set where
  ⊥    : Tree n
  ⊤    : Tree n
  var  : (x : Fin n) → Tree n
  _⟶_  : (τ₁ τ₂ : ∞ (Tree n)) → Tree n
