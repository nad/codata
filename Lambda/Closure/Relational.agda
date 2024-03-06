------------------------------------------------------------------------
-- A relational semantics which uses closures and environments
------------------------------------------------------------------------

module Lambda.Closure.Relational where

open import Codata.Musical.Notation
open import Data.Empty
open import Data.List hiding (lookup)
open import Data.Product
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Function hiding (_⟶_)
open import
  Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open import Lambda.Syntax using (Tm; con; var; ƛ; _·_)
open Lambda.Syntax.Closure Tm
open import Lambda.VirtualMachine as VM
open VM.Relational
open StarReasoning _⟶_
open InfiniteSequence

------------------------------------------------------------------------
-- Big-step semantics

-- For terminating computations.

infix 4 _⊢_⇓_

data _⊢_⇓_ {n} (ρ : Env n) : Tm n → Value → Set where
  var : ∀ {x} → ρ ⊢ var x ⇓ lookup ρ x
  con : ∀ {i} → ρ ⊢ con i ⇓ con i
  ƛ   : ∀ {t} → ρ ⊢ ƛ t ⇓ ƛ t ρ
  app : ∀ {t₁ t₂ n t} {ρ′ : Env n} {v v′}
        (t₁⇓   : ρ ⊢ t₁ ⇓ ƛ t ρ′)
        (t₂⇓   : ρ ⊢ t₂ ⇓ v′)
        (t₁t₂⇓ : v′ ∷ ρ′ ⊢ t ⇓ v) →
        ρ ⊢ t₁ · t₂ ⇓ v

-- For non-terminating computations.

infix 4 _⊢_⇑

data _⊢_⇑ {n} (ρ : Env n) : Tm n → Set where
  app : ∀ {t₁ t₂ n t} {ρ′ : Env n} {v′}
        (t₁⇓   : ρ ⊢ t₁ ⇓ ƛ t ρ′)
        (t₂⇓   : ρ ⊢ t₂ ⇓ v′)
        (t₁t₂⇑ : ∞ (v′ ∷ ρ′ ⊢ t ⇑)) →
        ρ ⊢ t₁ · t₂ ⇑
  ·ˡ  : ∀ {t₁ t₂}
        (t₁⇑ : ∞ (ρ ⊢ t₁ ⇑)) →
        ρ ⊢ t₁ · t₂ ⇑
  ·ʳ  : ∀ {t₁ t₂ v}
        (t₁⇓ : ρ ⊢ t₁ ⇓ v)
        (t₂⇑ : ∞ (ρ ⊢ t₂ ⇑)) →
        ρ ⊢ t₁ · t₂ ⇑

-- For crashing computations.

infix 4 _⊢_↯

_⊢_↯ : ∀ {n} → Env n → Tm n → Set
ρ ⊢ t ↯ = ¬ (∃ λ v → ρ ⊢ t ⇓ v) × ¬ (ρ ⊢ t ⇑)

------------------------------------------------------------------------
-- The semantics is deterministic

deterministic⇓ : ∀ {n} {ρ : Env n} {t v₁ v₂} →
                 ρ ⊢ t ⇓ v₁ → ρ ⊢ t ⇓ v₂ → v₁ ≡ v₂
deterministic⇓ var                 var                    = P.refl
deterministic⇓ con                 con                    = P.refl
deterministic⇓ ƛ                   ƛ                      = P.refl
deterministic⇓ (app t₁⇓ t₂⇓ t₁t₂⇓) (app t₁⇓′ t₂⇓′ t₁t₂⇓′)
  with deterministic⇓ t₁⇓ t₁⇓′ | deterministic⇓ t₂⇓ t₂⇓′
... | P.refl | P.refl = deterministic⇓ t₁t₂⇓ t₁t₂⇓′

deterministic⇓⇑ : ∀ {n} {ρ : Env n} {t v} →
                  ρ ⊢ t ⇓ v → ρ ⊢ t ⇑ → ⊥
deterministic⇓⇑ var ()
deterministic⇓⇑ con ()
deterministic⇓⇑ ƛ   ()
deterministic⇓⇑ (app t₁⇓ t₂⇓ t₁t₂⇓) (app t₁⇓′ t₂⇓′ t₁t₂⇑)
  with deterministic⇓ t₁⇓ t₁⇓′ | deterministic⇓ t₂⇓ t₂⇓′
... | P.refl | P.refl = deterministic⇓⇑ t₁t₂⇓ (♭ t₁t₂⇑)
deterministic⇓⇑ (app t₁⇓ t₂⇓ t₁t₂⇓) (·ˡ t₁⇑)      =
  deterministic⇓⇑ t₁⇓ (♭ t₁⇑)
deterministic⇓⇑ (app t₁⇓ t₂⇓ t₁t₂⇓) (·ʳ t₁⇓′ t₂⇑) =
  deterministic⇓⇑ t₂⇓ (♭ t₂⇑)

------------------------------------------------------------------------
-- Compiler "correctness"

-- The proofs below establish that the compiler in
-- Lambda.VirtualMachine preserves the semantics above (_⊢_⇓_ and
-- _⊢_⇑, not necessarily _⊢_↯), given that the virtual machine is
-- deterministic.

correct⇓′ : ∀ {n ρ c s v} {t : Tm n} →
            ρ ⊢ t ⇓ v →
            ⟨ comp t c , s , comp-env ρ ⟩ ⟶⋆
            ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩
correct⇓′ {ρ = ρ} {c} {s} (var {x}) = begin
  ⟨ var x ∷ c , s                               , comp-env ρ ⟩ ⟶⟨ var ⟩
  ⟨         c , val (lookup (comp-env ρ) x) ∷ s , comp-env ρ ⟩ ≡⟨ P.cong (λ v → ⟨ c , val v ∷ s , comp-env ρ ⟩)
                                                                         (lookup-hom x ρ) ⟩
  ⟨         c , val (comp-val (lookup ρ x)) ∷ s , comp-env ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} (con {i}) = begin
  ⟨ con i ∷ c ,                                     s , comp-env ρ ⟩ ⟶⟨ con ⟩
  ⟨         c , val (Lambda.Syntax.Closure.con i) ∷ s , comp-env ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} (ƛ {t}) = begin
  ⟨ clo (comp t [ ret ]) ∷ c ,                          s , comp-env ρ ⟩ ⟶⟨ clo ⟩
  ⟨                        c , val (comp-val (ƛ t ρ)) ∷ s , comp-env ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} {v} (app {t₁} {t₂} {t = t} {ρ′} {v′ = v′} t₁⇓ t₂⇓ t₁t₂⇓) = begin
  ⟨ comp t₁ (comp t₂ (app ∷ c)) ,                                               s ,               comp-env ρ  ⟩ ⟶*⟨ correct⇓′ t₁⇓ ⟩
  ⟨          comp t₂ (app ∷ c)  ,                     val (comp-val (ƛ t ρ′)) ∷ s ,               comp-env ρ  ⟩ ⟶*⟨ correct⇓′ t₂⇓ ⟩
  ⟨                   app ∷ c   , val (comp-val v′) ∷ val (comp-val (ƛ t ρ′)) ∷ s ,               comp-env ρ  ⟩ ⟶⟨ app ⟩
  ⟨ comp t [ ret ]              ,                          ret c (comp-env ρ) ∷ s , comp-val v′ ∷ comp-env ρ′ ⟩ ⟶*⟨ correct⇓′ t₁t₂⇓ ⟩
  ⟨        [ ret ]              ,       val (comp-val v) ∷ ret c (comp-env ρ) ∷ s , comp-val v′ ∷ comp-env ρ′ ⟩ ⟶⟨ ret ⟩
  ⟨                         c   ,       val (comp-val v) ∷                      s ,               comp-env ρ  ⟩ ∎

correct⇑′ : ∀ {n ρ c s} {t : Tm n} →
            ρ ⊢ t ⇑ → ⟨ comp t c , s , comp-env ρ ⟩ ⟶∞′
correct⇑′ {ρ = ρ} {c} {s} (app {t₁} {t₂} {t = t} {ρ′} {v′} t₁⇓ t₂⇓ t₁t₂⇑) =
  ⟨ comp t₁ (comp t₂ (app ∷ c)) ,                                               s ,               comp-env ρ  ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩′
  ⟨          comp t₂ (app ∷ c)  ,                     val (comp-val (ƛ t ρ′)) ∷ s ,               comp-env ρ  ⟩ ⟶⋆⟨ correct⇓′ t₂⇓ ⟩′
  ⟨                   app ∷ c   , val (comp-val v′) ∷ val (comp-val (ƛ t ρ′)) ∷ s ,               comp-env ρ  ⟩ ⟶⟨ app ⟩′ ♯
 (⟨ comp t [ ret ]              ,                          ret c (comp-env ρ) ∷ s , comp-val v′ ∷ comp-env ρ′ ⟩ ⟶∞⟨ correct⇑′ (♭ t₁t₂⇑) ⟩)
correct⇑′ {ρ = ρ} {c} {s} (·ˡ {t₁} {t₂} t₁⇑) =
  ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₁⇑) ⟩
correct⇑′ {ρ = ρ} {c} {s} (·ʳ {t₁} {t₂} {v} t₁⇓ t₂⇑) =
  ⟨ comp t₁ (comp t₂ (app ∷ c)) ,                    s , comp-env ρ ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩′
  ⟨          comp t₂ (app ∷ c)  , val (comp-val v) ∷ s , comp-env ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₂⇑) ⟩

correct⇓ : ∀ {t v} →
           [] ⊢ t ⇓ v →
           ∃ λ s → ⟨ comp t [] , [] , [] ⟩ ⟶⋆ s × s ⇓ comp-val v
correct⇓ t⇓ = (_ , correct⇓′ t⇓ , final)

correct⇑ : ∀ {t} → [] ⊢ t ⇑ → ⟨ comp t [] , [] , [] ⟩ ⟶∞
correct⇑ = InfiniteSequence.sound ∘ correct⇑′
