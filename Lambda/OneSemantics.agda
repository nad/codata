------------------------------------------------------------------------
-- Big-step semantics for the untyped λ-calculus
------------------------------------------------------------------------

module Lambda.OneSemantics where

open import Coinduction
open import Data.Fin
open import Data.Function
open import Data.Nat

open import Lambda.Syntax
open import Lambda.Substitution

-- Semantic domain. ⊥ represents non-termination.

data Sem (n : ℕ) : Set where
  ⊥   : Sem n
  val : (v : Value n) → Sem n

-- Conditional coinduction: coinduction only for ⊥.

∞? : ∀ {n} → Sem n → Set → Set
∞? ⊥       = ∞
∞? (val v) = id₁

-- Big-step semantics.

infix 4 _⇒_

data _⇒_ {n} : Tm n → Sem n → Set where
  val : ∀ {v} → ⌜ v ⌝ ⇒ val v
  app : ∀ {t₁ t₂ t v s}
        (t₁⇓   : t₁ ⇒ val (ƛ t))
        (t₂⇓   : t₂ ⇒ val v)
        (t₁t₂⇒ : ∞? s (t / sub ⌜ v ⌝ ⇒ s)) →
        t₁ · t₂ ⇒ s
  ·ˡ  : ∀ {t₁ t₂}
        (t₁⇑ : ∞ (t₁ ⇒ ⊥)) →
        t₁ · t₂ ⇒ ⊥
  ·ʳ  : ∀ {t₁ t₂ v}
        (t₁⇓ : t₁ ⇒ val v)
        (t₂⇑ : ∞ (t₂ ⇒ ⊥)) →
        t₁ · t₂ ⇒ ⊥

-- Example.

ω : Tm 0
ω = ƛ (var zero · var zero)

Ω : Tm 0
Ω = ω · ω

Ω-loops : Ω ⇒ ⊥
Ω-loops = app val val (♯ Ω-loops)
