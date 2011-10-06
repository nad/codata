------------------------------------------------------------------------
-- A relational semantics which uses closures and environments
------------------------------------------------------------------------

module Lambda.Closure.Relational where

open import Coinduction
open import Data.List
open import Data.Product
open import Data.Star.Properties
open import Data.Vec using (Vec; _∷_; []; lookup)
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open import Lambda.Syntax using (Tm; con; var; ƛ; _·_)
open Lambda.Syntax.Closure Tm
open import Lambda.VirtualMachine as VM
open VM.Relational
open StarReasoning _⟶_
open InfiniteSequence

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
∞? (val v) = id

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

  lemma₁ : ∀ {n} {ρ : Env n} {t v₁ v₂} →
           ρ ⊢ t ⇒ val v₁ → ρ ⊢ t ⇒ val v₂ →
           _≡_ {A = Sem} (val v₁) (val v₂)
  lemma₁ var                 var                    = P.refl
  lemma₁ con                 con                    = P.refl
  lemma₁ ƛ                   ƛ                      = P.refl
  lemma₁ (app t₁⇓ t₂⇓ t₁t₂⇓) (app t₁⇓′ t₂⇓′ t₁t₂⇓′)
    with lemma₁ t₁⇓ t₁⇓′ | lemma₁ t₂⇓ t₂⇓′
  ... | P.refl | P.refl = lemma₁ t₁t₂⇓ t₁t₂⇓′

  lemma₂ : ∀ {n} {ρ : Env n} {t v} →
           ρ ⊢ t ⇒ val v → ρ ⊢ t ⇒ ⊥ → val v ≡ ⊥
  lemma₂ var ()
  lemma₂ con ()
  lemma₂ ƛ   ()
  lemma₂ (app t₁⇓ t₂⇓ t₁t₂⇓) (app t₁⇓′ t₂⇓′ t₁t₂⇑)
    with lemma₁ t₁⇓ t₁⇓′ | lemma₁ t₂⇓ t₂⇓′
  ... | P.refl | P.refl = lemma₂ t₁t₂⇓ (♭ t₁t₂⇑)
  lemma₂ (app t₁⇓ t₂⇓ t₁t₂⇓) (·ˡ t₁⇑)      with lemma₂ t₁⇓ (♭ t₁⇑)
  ... | ()
  lemma₂ (app t₁⇓ t₂⇓ t₁t₂⇓) (·ʳ t₁⇓′ t₂⇑) with lemma₂ t₂⇓ (♭ t₂⇑)
  ... | ()

deterministic : ∀ {n} {ρ : Env n} {t} v₁ v₂ →
                ρ ⊢ t ⇒ v₁ → ρ ⊢ t ⇒ v₂ → v₁ ≡ v₂
deterministic ⊥        ⊥        d₁ d₂ = P.refl
deterministic (val v₁) ⊥        d₁ d₂ = lemma₂ d₁ d₂
deterministic ⊥        (val v₂) d₁ d₂ = P.sym $ lemma₂ d₂ d₁
deterministic (val v₁) (val v₂) d₁ d₂ = lemma₁ d₁ d₂

------------------------------------------------------------------------
-- Compiler "correctness"

-- The proofs below establish that the compiler in
-- Lambda.VirtualMachine preserves the semantics above, on the
-- assumption that the virtual machine is deterministic.

correct⇓′ : ∀ {n ρ c s v} {t : Tm n} →
            ρ ⊢ t ⇒ val v →
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
correct⇓′ {ρ = ρ} {c} {s} {v′} (app {t₁} {t₂} {t = t} {ρ′} {v} t₁⇓ t₂⇓ t₁t₂⇓) = begin
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) ,                                s ,          ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩
  ⟨         ⟦ t₂ ⟧ (App ∷ c)  ,              val ⟦ ƛ t ρ′ ⟧v ∷ s ,          ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₂⇓ ⟩
  ⟨                 App ∷ c   , val ⟦ v ⟧v ∷ val ⟦ ƛ t ρ′ ⟧v ∷ s ,          ⟦ ρ ⟧ρ  ⟩ ⟶⟨ App ⟩
  ⟨ ⟦ t ⟧ [ Ret ]             ,                 ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v ⟧v ∷ ⟦ ρ′ ⟧ρ ⟩ ⟶⋆⟨ correct⇓′ t₁t₂⇓ ⟩
  ⟨       [ Ret ]             ,   val ⟦ v′ ⟧v ∷ ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v ⟧v ∷ ⟦ ρ′ ⟧ρ ⟩ ⟶⟨ Ret ⟩
  ⟨                       c   ,   val ⟦ v′ ⟧v ∷                s ,          ⟦ ρ ⟧ρ  ⟩ ∎

correct⇑′ : ∀ {n ρ c s} {t : Tm n} →
            ρ ⊢ t ⇒ ⊥ → ⟨ ⟦ t ⟧ c , s , ⟦ ρ ⟧ρ ⟩ ⟶∞′
correct⇑′ {ρ = ρ} {c} {s} (app {t₁} {t₂} {t = t} {ρ′} {v} t₁⇓ t₂⇓ t₁t₂⇑) =
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) ,                                s ,          ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩′
  ⟨         ⟦ t₂ ⟧ (App ∷ c)  ,              val ⟦ ƛ t ρ′ ⟧v ∷ s ,          ⟦ ρ ⟧ρ  ⟩ ⟶⋆⟨ correct⇓′ t₂⇓ ⟩′
  ⟨                 App ∷ c   , val ⟦ v ⟧v ∷ val ⟦ ƛ t ρ′ ⟧v ∷ s ,          ⟦ ρ ⟧ρ  ⟩ ⟶⟨ App ⟩′ ♯
 (⟨ ⟦ t ⟧ [ Ret ]             ,                 ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v ⟧v ∷ ⟦ ρ′ ⟧ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₁t₂⇑) ⟩)
correct⇑′ {ρ = ρ} {c} {s} (·ˡ {t₁} {t₂} t₁⇑) =
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) , s , ⟦ ρ ⟧ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₁⇑) ⟩
correct⇑′ {ρ = ρ} {c} {s} (·ʳ {t₁} {t₂} {v} t₁⇓ t₂⇑) =
  ⟨ ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c)) ,              s , ⟦ ρ ⟧ρ ⟩ ⟶⋆⟨ correct⇓′ t₁⇓ ⟩′
  ⟨         ⟦ t₂ ⟧ (App ∷ c)  , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ⟶∞⟨ correct⇑′ (♭ t₂⇑) ⟩

correct⇓ : ∀ {t v} →
           [] ⊢ t ⇒ val v →
           ∃ λ s → ⟨ ⟦ t ⟧ [] , [] , [] ⟩ ⟶⋆ s × s ⇓ ⟦ v ⟧v
correct⇓ t⇓ = (_ , correct⇓′ t⇓ , final)

correct⇑ : ∀ {t} → [] ⊢ t ⇒ ⊥ → ⟨ ⟦ t ⟧ [] , [] , [] ⟩ ⟶∞
correct⇑ = InfiniteSequence.sound ∘ correct⇑′

-- Note that the two correctness statements above do not take account
-- of terms which crash.
