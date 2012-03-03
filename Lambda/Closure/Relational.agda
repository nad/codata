------------------------------------------------------------------------
-- A relational semantics which uses closures and environments
------------------------------------------------------------------------

module Lambda.Closure.Relational where

open import Coinduction
open import Data.Empty
open import Data.List
open import Data.Product
open import Data.Star.Properties
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Function
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
  var : ∀ {x} → ρ ⊢ var x ⇓ lookup x ρ
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
-- Lambda.VirtualMachine preserves the semantics above, on the
-- assumption that the virtual machine is deterministic.

correct⇓′ : ∀ {n ρ c s v} {t : Tm n} →
            ρ ⊢ t ⇓ v →
            ⟨ ⟦ t ⟧ c , s , ⟦ ρ ⟧ρ ⟩ ⟶⋆ ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩
correct⇓′ {ρ = ρ} {c} {s} (var {x}) = begin
  ⟨ Var x ∷ c , s                         , ⟦ ρ ⟧ρ ⟩ ⟶⟨ Var ⟩
  ⟨         c , val (lookup x ⟦ ρ ⟧ρ) ∷ s , ⟦ ρ ⟧ρ ⟩ ≡⟨ P.cong (λ v → ⟨ c , val v ∷ s , ⟦ ρ ⟧ρ ⟩)
                                                               (lookup-hom x ρ) ⟩
  ⟨         c , val ⟦ lookup x ρ ⟧v   ∷ s , ⟦ ρ ⟧ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} (con {i}) = begin
  ⟨ Con i ∷ c ,                                     s , ⟦ ρ ⟧ρ ⟩ ⟶⟨ Con ⟩
  ⟨         c , val (Lambda.Syntax.Closure.con i) ∷ s , ⟦ ρ ⟧ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} (ƛ {t}) = begin
  ⟨ Clos (⟦ t ⟧ [ Ret ]) ∷ c ,                  s , ⟦ ρ ⟧ρ ⟩ ⟶⟨ Clos ⟩
  ⟨                        c , val ⟦ ƛ t ρ ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} {v} (app {t₁} {t₂} {t = t} {ρ′} {v′ = v′} t₁⇓ t₂⇓ t₁t₂⇓) = begin
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) ,                                 s ,           ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩
  ⟨         ⟦ t₂ ⟧ (App ∷ c)  ,               val ⟦ ƛ t ρ′ ⟧v ∷ s ,           ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₂⇓ ⟩
  ⟨                 App ∷ c   , val ⟦ v′ ⟧v ∷ val ⟦ ƛ t ρ′ ⟧v ∷ s ,           ⟦ ρ ⟧ρ  ⟩ ⟶⟨ App ⟩
  ⟨ ⟦ t ⟧ [ Ret ]             ,                  ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v′ ⟧v ∷ ⟦ ρ′ ⟧ρ ⟩ ⟶⋆⟨ correct⇓′ t₁t₂⇓ ⟩
  ⟨       [ Ret ]             ,     val ⟦ v ⟧v ∷ ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v′ ⟧v ∷ ⟦ ρ′ ⟧ρ ⟩ ⟶⟨ Ret ⟩
  ⟨                       c   ,     val ⟦ v ⟧v ∷                s ,           ⟦ ρ ⟧ρ  ⟩ ∎

correct⇑′ : ∀ {n ρ c s} {t : Tm n} →
            ρ ⊢ t ⇑ → ⟨ ⟦ t ⟧ c , s , ⟦ ρ ⟧ρ ⟩ ⟶∞′
correct⇑′ {ρ = ρ} {c} {s} (app {t₁} {t₂} {t = t} {ρ′} {v′} t₁⇓ t₂⇓ t₁t₂⇑) =
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) ,                                 s ,           ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩′
  ⟨         ⟦ t₂ ⟧ (App ∷ c)  ,               val ⟦ ƛ t ρ′ ⟧v ∷ s ,           ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₂⇓ ⟩′
  ⟨                 App ∷ c   , val ⟦ v′ ⟧v ∷ val ⟦ ƛ t ρ′ ⟧v ∷ s ,           ⟦ ρ ⟧ρ  ⟩ ⟶⟨ App ⟩′ ♯
 (⟨ ⟦ t ⟧ [ Ret ]             ,                  ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v′ ⟧v ∷ ⟦ ρ′ ⟧ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₁t₂⇑) ⟩)
correct⇑′ {ρ = ρ} {c} {s} (·ˡ {t₁} {t₂} t₁⇑) =
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) , s , ⟦ ρ ⟧ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₁⇑) ⟩
correct⇑′ {ρ = ρ} {c} {s} (·ʳ {t₁} {t₂} {v} t₁⇓ t₂⇑) =
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) ,              s , ⟦ ρ ⟧ρ ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩′
  ⟨         ⟦ t₂ ⟧ (App ∷ c)  , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₂⇑) ⟩

correct⇓ : ∀ {t v} →
           [] ⊢ t ⇓ v →
           ∃ λ s → ⟨ ⟦ t ⟧ [] , [] , [] ⟩ ⟶⋆ s × s ⇓ ⟦ v ⟧v
correct⇓ t⇓ = (_ , correct⇓′ t⇓ , final)

correct⇑ : ∀ {t} → [] ⊢ t ⇑ → ⟨ ⟦ t ⟧ [] , [] , [] ⟩ ⟶∞
correct⇑ = InfiniteSequence.sound ∘ correct⇑′

-- Note that the two correctness statements above only apply to terms
-- that do not crash.
