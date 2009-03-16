------------------------------------------------------------------------
-- Subtyping defined in terms of finite approximations
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Inductive where

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

data _≤Fin_ : ∀ {m n} → FinTree m → FinTree n → Set where
  ⊥    : ∀ {m n} {τ : FinTree n} → ⊥ {m} ≤Fin τ
  ⊤    : ∀ {m n} {σ : FinTree m} → σ ≤Fin ⊤ {n}
  refl : ∀ {n} {τ : FinTree n} → τ ≤Fin τ
  _⟶_  : ∀ {m n} {σ₁ σ₂ : FinTree m} {τ₁ τ₂ : FinTree n}
         (τ₁≤σ₁ : τ₁ ≤Fin σ₁) (σ₂≤τ₂ : σ₂ ≤Fin τ₂) →
         σ₁ ⟶ σ₂ ≤Fin τ₁ ⟶ τ₂

-- Subtyping for possibly infinite trees, defined in terms of
-- subtyping for finite trees.

_≤↓_ : ∀ {m n} → Tree m → Tree n → Set
σ ≤↓ τ = ∀ k → σ ↓ k ≤Fin τ ↓ k

_≤↑_ : ∀ {m n} → Tree m → Tree n → Set
σ ≤↑ τ = ∀ k → σ ↑ k ≤Fin τ ↑ k

-- Subtyping for recursive types, defined in terms of subtyping for
-- possibly infinite trees.

_≤Ind_ : ∀ {m n} → Ty m → Ty n → Set
σ ≤Ind τ = ⟦ σ ⟧ ≤↓ ⟦ τ ⟧
