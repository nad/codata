------------------------------------------------------------------------
-- Subtyping defined in terms of finite approximations
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Semantic.Inductive where

open import Data.Nat
open import Data.Fin
open import Coinduction

open import RecursiveTypes.Syntax
open import RecursiveTypes.Semantics

-- Finite trees.

infixr 10 _⟶_

data FinTree (n : ℕ) : Set where
  ⊥   : FinTree n
  ⊤   : FinTree n
  var : (x : Fin n) → FinTree n
  _⟶_ : (σ τ : FinTree n) → FinTree n

-- Functions which prune a possibly infinite tree.

infix 8 _↑_ _↓_

mutual

  _↑_ : ∀ {n} → Tree n → ℕ → FinTree n
  τ     ↑ zero  = ⊤
  ⊥     ↑ suc k = ⊥
  ⊤     ↑ suc k = ⊤
  var x ↑ suc k = var x
  σ ⟶ τ ↑ suc k = (♭ σ ↓ k) ⟶ (♭ τ ↑ k)

  _↓_ : ∀ {n} → Tree n → ℕ → FinTree n
  τ     ↓ zero  = ⊥
  ⊥     ↓ suc k = ⊥
  ⊤     ↓ suc k = ⊤
  var x ↓ suc k = var x
  σ ⟶ τ ↓ suc k = (♭ σ ↑ k) ⟶ (♭ τ ↓ k)

-- Subtyping for finite trees.

infix 4 _≤Fin_ _≤↓_ _≤↑_ _≤Ind_

data _≤Fin_ {n} : FinTree n → FinTree n → Set where
  ⊥    : ∀ {τ} → ⊥ ≤Fin τ
  ⊤    : ∀ {σ} → σ ≤Fin ⊤
  refl : ∀ {τ} → τ ≤Fin τ
  _⟶_  : ∀ {σ₁ σ₂ τ₁ τ₂}
         (τ₁≤σ₁ : τ₁ ≤Fin σ₁) (σ₂≤τ₂ : σ₂ ≤Fin τ₂) →
         σ₁ ⟶ σ₂ ≤Fin τ₁ ⟶ τ₂

-- Subtyping for possibly infinite trees, defined in terms of
-- subtyping for finite trees.

_≤↓_ : ∀ {n} → Tree n → Tree n → Set
σ ≤↓ τ = ∀ k → σ ↓ k ≤Fin τ ↓ k

_≤↑_ : ∀ {n} → Tree n → Tree n → Set
σ ≤↑ τ = ∀ k → σ ↑ k ≤Fin τ ↑ k

-- Subtyping for recursive types, defined in terms of subtyping for
-- possibly infinite trees.

_≤Ind_ : ∀ {n k} → Ty n k → Ty n k → Set
σ ≤Ind τ = ⟦ σ ⟧ ≤↓ ⟦ τ ⟧
