------------------------------------------------------------------------
-- The syntax of the untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.Syntax where

open import Data.Nat
open import Data.Fin
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
