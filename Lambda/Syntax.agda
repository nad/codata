------------------------------------------------------------------------
-- The syntax of, and a type system for, the untyped λ-calculus with
-- constants
------------------------------------------------------------------------

module Lambda.Syntax where

open import Codata.Musical.Notation
open import Data.Nat
open import Data.Fin hiding (_≤?_)
open import Data.Vec
open import Relation.Nullary.Decidable

------------------------------------------------------------------------
-- Terms

-- Variables are represented using de Bruijn indices.

infixl 9 _·_

data Tm (n : ℕ) : Set where
  con : (i : ℕ) → Tm n
  var : (x : Fin n) → Tm n
  ƛ   : (t : Tm (suc n)) → Tm n
  _·_ : (t₁ t₂ : Tm n) → Tm n

-- Convenient helper.

vr : ∀ m {n} {m<n : True (suc m ≤? n)} → Tm n
vr _ {m<n = m<n} = var (#_ _ {m<n = m<n})

------------------------------------------------------------------------
-- Values, potentially with free variables

module WHNF where

  data Value (n : ℕ) : Set where
    con : (i : ℕ) → Value n
    ƛ   : (t : Tm (suc n)) → Value n

  ⌜_⌝ : ∀ {n} → Value n → Tm n
  ⌜ con i ⌝ = con i
  ⌜ ƛ t   ⌝ = ƛ t

------------------------------------------------------------------------
-- Closure-based definition of values

-- Environments and values. Defined in a module parametrised on the
-- type of terms.

module Closure (Tm : ℕ → Set) where

  mutual

    -- Environments.

    Env : ℕ → Set
    Env n = Vec Value n

    -- Values. Lambdas are represented using closures, so values do
    -- not contain any free variables.

    data Value : Set where
      con : (i : ℕ) → Value
      ƛ   : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value

------------------------------------------------------------------------
-- Type system (following Leroy and Grall)

-- Recursive, simple types, defined coinductively.

infixr 8 _⇾_

data Ty : Set where
  nat : Ty
  _⇾_ : (σ τ : ∞ Ty) → Ty

-- Contexts.

Ctxt : ℕ → Set
Ctxt n = Vec Ty n

-- Type system.

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctxt n) : Tm n → Ty → Set where
  con : ∀ {i} → Γ ⊢ con i ∈ nat
  var : ∀ {x} → Γ ⊢ var x ∈ lookup Γ x
  ƛ   : ∀ {t σ τ} (t∈ : ♭ σ ∷ Γ ⊢ t ∈ ♭ τ) → Γ ⊢ ƛ t ∈ σ ⇾ τ
  _·_ : ∀ {t₁ t₂ σ τ} (t₁∈ : Γ ⊢ t₁ ∈ σ ⇾ τ) (t₂∈ : Γ ⊢ t₂ ∈ ♭ σ) →
        Γ ⊢ t₁ · t₂ ∈ ♭ τ

------------------------------------------------------------------------
-- Example

-- A non-terminating term.

ω : Tm 0
ω = ƛ (vr 0 · vr 0)

Ω : Tm 0
Ω = ω · ω

-- Ω is well-typed.

Ω-well-typed : (τ : Ty) → [] ⊢ Ω ∈ τ
Ω-well-typed τ =
  _·_ {σ = ♯ σ} {τ = ♯ τ} (ƛ (var · var)) (ƛ (var · var))
  where σ = ♯ σ ⇾ ♯ τ

-- A call-by-value fix-point combinator.

Z : Tm 0
Z = ƛ (t · t)
  where t = ƛ (vr 1 · ƛ (vr 1 · vr 1 · vr 0))

-- This combinator is also well-typed.

fix-well-typed :
  ∀ {σ τ} → [] ⊢ Z ∈ ♯ (♯ (σ ⇾ τ) ⇾ ♯ (σ ⇾ τ)) ⇾ ♯ (σ ⇾ τ)
fix-well-typed =
  ƛ (_·_ {σ = υ} {τ = ♯ _}
         (ƛ (var · ƛ (var · var · var)))
         (ƛ (var · ƛ (var · var · var))))
  where
  υ : ∞ Ty
  υ = ♯ (υ ⇾ ♯ _)
