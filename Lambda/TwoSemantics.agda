------------------------------------------------------------------------
-- The two big-step semantics given by Leroy and Grall in "Coinductive
-- big-step operational semantics"
------------------------------------------------------------------------

module Lambda.TwoSemantics where

open import Coinduction

open import Lambda.Syntax
open import Lambda.Substitution

-- Big-step semantics for terminating computations.

infix 4 _⇓_

data _⇓_ {n} : Tm n → Value n → Set where
  val : ∀ {v} → ⌜ v ⌝ ⇓ v
  app : ∀ {t₁ t₂ t v v′}
        (t₁⇓   : t₁ ⇓ ƛ t)
        (t₂⇓   : t₂ ⇓ v)
        (t₁t₂⇓ : t / sub ⌜ v ⌝ ⇓ v′) →
        t₁ · t₂ ⇓ v′

-- Big-step semantics for non-terminating computations.

infix 4 _⇑

data _⇑ {n} : Tm n → Set where
  ·ˡ  : ∀ {t₁ t₂}
        (t₁⇑ : ∞ (t₁ ⇑)) →
        t₁ · t₂ ⇑
  ·ʳ  : ∀ {t₁ t₂ v}
        (t₁⇓ : t₁ ⇓ v)
        (t₂⇑ : ∞ (t₂ ⇑)) →
        t₁ · t₂ ⇑
  app : ∀ {t₁ t₂ t v}
        (t₁⇓   : t₁ ⇓ ƛ t)
        (t₂⇓   : t₂ ⇓ v)
        (t₁t₂⇓ : ∞ (t / sub ⌜ v ⌝ ⇑)) →
        t₁ · t₂ ⇑
