------------------------------------------------------------------------
-- A semantics which uses closures and environments
------------------------------------------------------------------------

module Lambda.Closure where

open import Coinduction
open import Data.Fin
open import Data.Function
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality

open import Lambda.Syntax using (Tm; con; var; ƛ; _·_)

------------------------------------------------------------------------
-- Environments and values

-- Defined in a module parametrised on the type of values.

module Closure (Tm : ℕ → Set) where

 mutual

  -- Environments.

  Env : ℕ → Set
  Env n = Vec Value n

  -- Values. Lambdas are represented using closures, so values do not
  -- contain any free variables.

  data Value : Set where
    con : (i : ℕ) → Value
    ƛ   : ∀ {n} (t : Tm (suc n)) (ρ : Env n) → Value

open Closure Tm public

------------------------------------------------------------------------
-- Big-step semantics (for both terminating and non-terminating
-- computations)

-- Semantic domain. ⊥ represents non-termination.

data Sem : Set where
  ⊥   : Sem
  val : (v : Value) → Sem

-- Conditional coinduction: coinduction only for ⊥.

∞? : Sem → Set → Set
∞? ⊥       = ∞
∞? (val v) = id₁

-- Big-step semantics.

infix 4 _⊢_⇒_

data _⊢_⇒_ {n} (ρ : Env n) : Tm n → Sem → Set where
  var : ∀ {x} → ρ ⊢ var x ⇒ val (lookup x ρ)
  con : ∀ {i} → ρ ⊢ con i ⇒ val (con i)
  ƛ   : ∀ {t} → ρ ⊢ ƛ t ⇒ val (ƛ t ρ)
  app : ∀ {t₁ t₂ n t} {ρ′ : Env n} {v s}
        (t₁⇓   : ρ ⊢ t₁ ⇒ val (ƛ t ρ′))
        (t₂⇓   : ρ ⊢ t₂ ⇒ val v)
        (t₁t₂⇒ : ∞? s (v ∷ ρ′ ⊢ t ⇒ s)) →
        ρ ⊢ t₁ · t₂ ⇒ s
  ·ˡ  : ∀ {t₁ t₂}
        (t₁⇑ : ∞ (ρ ⊢ t₁ ⇒ ⊥)) →
        ρ ⊢ t₁ · t₂ ⇒ ⊥
  ·ʳ  : ∀ {t₁ t₂ v}
        (t₁⇓ : ρ ⊢ t₁ ⇒ val v)
        (t₂⇑ : ∞ (ρ ⊢ t₂ ⇒ ⊥)) →
        ρ ⊢ t₁ · t₂ ⇒ ⊥

------------------------------------------------------------------------
-- The semantics is deterministic

private
 mutual

  lemma₁ : ∀ {n} {ρ : Env n} {t v₁ v₂} →
           ρ ⊢ t ⇒ val v₁ → ρ ⊢ t ⇒ val v₂ → val v₁ ≡ val v₂
  lemma₁ var                 var                    = refl
  lemma₁ con                 con                    = refl
  lemma₁ ƛ                   ƛ                      = refl
  lemma₁ (app t₁⇓ t₂⇓ t₁t₂⇓) (app t₁⇓′ t₂⇓′ t₁t₂⇓′)
    with lemma₁ t₁⇓ t₁⇓′ | lemma₁ t₂⇓ t₂⇓′
  ... | refl | refl = lemma₁ t₁t₂⇓ t₁t₂⇓′

  lemma₂ : ∀ {n} {ρ : Env n} {t v} →
           ρ ⊢ t ⇒ val v → ρ ⊢ t ⇒ ⊥ → val v ≡ ⊥
  lemma₂ var ()
  lemma₂ con ()
  lemma₂ ƛ   ()
  lemma₂ (app t₁⇓ t₂⇓ t₁t₂⇓) (app t₁⇓′ t₂⇓′ t₁t₂⇑)
    with lemma₁ t₁⇓ t₁⇓′ | lemma₁ t₂⇓ t₂⇓′
  ... | refl | refl = lemma₂ t₁t₂⇓ (♭ t₁t₂⇑)
  lemma₂ (app t₁⇓ t₂⇓ t₁t₂⇓) (·ˡ t₁⇑)      with lemma₂ t₁⇓ (♭ t₁⇑)
  ... | ()
  lemma₂ (app t₁⇓ t₂⇓ t₁t₂⇓) (·ʳ t₁⇓′ t₂⇑) with lemma₂ t₂⇓ (♭ t₂⇑)
  ... | ()

deterministic : ∀ {n} {ρ : Env n} {t} v₁ v₂ →
                ρ ⊢ t ⇒ v₁ → ρ ⊢ t ⇒ v₂ → v₁ ≡ v₂
deterministic ⊥        ⊥        d₁ d₂ = refl
deterministic (val v₁) ⊥        d₁ d₂ = lemma₂ d₁ d₂
deterministic ⊥        (val v₂) d₁ d₂ = sym $ lemma₂ d₂ d₁
deterministic (val v₁) (val v₂) d₁ d₂ = lemma₁ d₁ d₂
