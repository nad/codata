------------------------------------------------------------------------
-- Big-step semantics for the untyped λ-calculus
------------------------------------------------------------------------

module Lambda.Substitution.OneSemantics where

open import Coinduction
open import Data.Fin
open import Function
open import Data.Nat

open import Lambda.Syntax
open WHNF
open import Lambda.Substitution

-- Semantic domain. ⊥ represents non-termination.

data Sem (n : ℕ) : Set where
  ⊥   : Sem n
  val : (v : Value n) → Sem n

-- Big-step semantics.

mutual

  infix 4 _⇒_ _⇒?_

  data _⇒_ {n} : Tm n → Sem n → Set where
    val : ∀ {v} → ⌜ v ⌝ ⇒ val v
    app : ∀ {t₁ t₂ t v s}
          (t₁⇓   : t₁ ⇒? val (ƛ t))
          (t₂⇓   : t₂ ⇒? val v)
          (t₁t₂⇒ : t / sub ⌜ v ⌝ ⇒? s) →
          t₁ · t₂ ⇒ s
    ·ˡ  : ∀ {t₁ t₂}
          (t₁⇑ : t₁ ⇒? ⊥) →
          t₁ · t₂ ⇒ ⊥
    ·ʳ  : ∀ {t₁ t₂ v}
          (t₁⇓ : t₁ ⇒? val v)
          (t₂⇑ : t₂ ⇒? ⊥) →
          t₁ · t₂ ⇒ ⊥

  -- Conditional coinduction: coinduction only for diverging
  -- computations.

  _⇒?_ : ∀ {n} → Tm n → Sem n → Set
  t ⇒? ⊥     = ∞ (t ⇒ ⊥)
  t ⇒? val v = t ⇒ val v

-- Example.

ω : Tm 0
ω = ƛ (vr 0 · vr 0)

Ω : Tm 0
Ω = ω · ω

Ω-loops : Ω ⇒ ⊥
Ω-loops = app val val (♯ Ω-loops)
