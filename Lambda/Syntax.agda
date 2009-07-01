------------------------------------------------------------------------
-- The syntax of the untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.Syntax where

open import Data.Nat
open import Data.Fin
open import Relation.Nullary.Decidable

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

-- Values.

data Value (n : ℕ) : Set where
  con : (i : ℕ) → Value n
  ƛ   : (t : Tm (suc n)) → Value n

⌜_⌝ : ∀ {n} → Value n → Tm n
⌜ con i ⌝ = con i
⌜ ƛ t   ⌝ = ƛ t
