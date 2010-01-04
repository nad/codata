------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

module Lambda.VirtualMachine where

open import Coinduction
open import Data.Fin
open import Function
open import Data.List
open import Data.Nat
open import Data.Star
open import Data.Star.Properties
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality

open import Lambda.Closure as C hiding (Env; Value)
open import Lambda.Syntax hiding (Value)

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    Var  : (x : Fin n) → Instr n
    Con  : (i : ℕ) → Instr n
    Clos : (c : Code (suc n)) → Instr n
    App  : Instr n
    Ret  : Instr n

  -- Code.

  Code : ℕ → Set
  Code n = List (Instr n)

-- Values.

open Closure Code public

-- Stacks.

data StackElement : Set where
  val : (v : Value) → StackElement
  ret : ∀ {n} (c : Code n) (ρ : Env n) → StackElement

Stack : Set
Stack = List StackElement

-- Semantics.

data State : Set where
  ⟨_,_,_⟩ : ∀ {n} (c : Code n) (s : Stack) (ρ : Env n) → State

infix 4 _⟶_

data _⟶_ : State → State → Set where
  Var  : ∀ {n} {x : Fin n} {c s ρ} →
         ⟨ Var x ∷ c , s , ρ ⟩ ⟶ ⟨ c , val (lookup x ρ) ∷ s , ρ ⟩
  Con  : ∀ {n i} {c : Code n} {s ρ} →
         ⟨ Con i ∷ c , s , ρ ⟩ ⟶ ⟨ c , val (con i) ∷ s , ρ ⟩
  Clos : ∀ {n} {c : Code n} {c′ s ρ} →
         ⟨ Clos c′ ∷ c , s , ρ ⟩ ⟶ ⟨ c , val (ƛ c′ ρ) ∷ s , ρ ⟩
  App  : ∀ {n} {c : Code n} {v n′} {c′ : Code (suc n′)} {ρ′ s ρ} →
         ⟨ App ∷ c , val v ∷ val (ƛ c′ ρ′) ∷ s , ρ ⟩ ⟶ ⟨ c′ , ret c ρ ∷ s , v ∷ ρ′ ⟩
  Ret  : ∀ {n} {c : Code n} {v n′} {c′ : Code n′} {ρ′ s ρ} →
         ⟨ Ret ∷ c , val v ∷ ret c′ ρ′ ∷ s , ρ ⟩ ⟶ ⟨ c′ , val v ∷ s , ρ′ ⟩

-- Reflexive transitive closure.

infix 4 _⟶⋆_

_⟶⋆_ : State → State → Set
_⟶⋆_ = Star _⟶_

open StarReasoning _⟶_ public

-- Infinite sequences of steps.

infixr 5 _◅_
infix  4 _⟶∞ _⟶∞′

data _⟶∞ : State → Set where
  _◅_ : ∀ {s₁ s₂} (s₁⟶s₂ : s₁ ⟶ s₂) (s₂⟶∞ : ∞ (s₂ ⟶∞)) → s₁ ⟶∞

-- A variant of _⟶∞ which is easier to use.

infixr 2 _⟶⟨_⟩′_ _⟶⋆⟨_⟩′_
infix  2 _⟶∞⟨_⟩

data _⟶∞′ : State → Set where
  _⟶⟨_⟩′_  : ∀ s₁ {s₂} (s₁⟶s₂ : s₁ ⟶ s₂) (s₂⟶∞ : ∞ (s₂ ⟶∞′)) → s₁ ⟶∞′
  _⟶⋆⟨_⟩′_ : ∀ s₁ {s₂} (s₁⟶⋆s₂ : s₁ ⟶⋆ s₂) (s₂⟶∞ : s₂ ⟶∞′) → s₁ ⟶∞′
  _⟶∞⟨_⟩   : ∀ s (s⟶∞ : s ⟶∞′) → s ⟶∞′

∞′→∞ : ∀ {s} → s ⟶∞′ → s ⟶∞
∞′→∞ (s₁ ⟶⟨ s₁⟶s₂ ⟩′ s₂⟶∞)           = s₁⟶s₂ ◅ ♯ (∞′→∞ (♭ s₂⟶∞))
∞′→∞ (s  ⟶⋆⟨ ε ⟩′ s⟶∞)               = ∞′→∞ s⟶∞
∞′→∞ (s₁ ⟶⋆⟨ s₁⟶s₂ ◅ s₂⟶⋆s₃ ⟩′ s₃⟶∞) = s₁⟶s₂ ◅ ♯ (∞′→∞ (_ ⟶⋆⟨ s₂⟶⋆s₃ ⟩′ s₃⟶∞))
∞′→∞ (s  ⟶∞⟨ s⟶∞ ⟩)                  = ∞′→∞ s⟶∞

-- Compiler, formulated in continuation-passing style.

⟦_⟧ : ∀ {n} → Tm n → Code n → Code n
⟦ con i ⟧   c = Con i ∷ c
⟦ var x ⟧   c = Var x ∷ c
⟦ ƛ t ⟧     c = Clos (⟦ t ⟧ [ Ret ]) ∷ c
⟦ t₁ · t₂ ⟧ c = ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c))

mutual

  ⟦_⟧ρ : ∀ {n} → C.Env n → Env n
  ⟦ []    ⟧ρ = []
  ⟦ v ∷ ρ ⟧ρ = ⟦ v ⟧v ∷ ⟦ ρ ⟧ρ

  ⟦_⟧v : C.Value → Value
  ⟦ con i ⟧v = con i
  ⟦ ƛ t ρ ⟧v = ƛ (⟦ t ⟧ [ Ret ]) ⟦ ρ ⟧ρ

-- lookup is homomorphic.

lookup-hom : ∀ {n} (x : Fin n) ρ → lookup x ⟦ ρ ⟧ρ ≡ ⟦ lookup x ρ ⟧v
lookup-hom zero    (v ∷ ρ) = refl
lookup-hom (suc x) (v ∷ ρ) = lookup-hom x ρ

-- Compiler "correctness".
--
-- Note that the statement of compiler correctness would be more
-- useful if we knew that the virtual machine was deterministic.

correct⇓′ : ∀ {n} {ρ : C.Env n} {c s v t} →
            ρ ⊢ t ⇒ val v →
            ⟨ ⟦ t ⟧ c , s , ⟦ ρ ⟧ρ ⟩ ⟶⋆ ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩
correct⇓′ {ρ = ρ} {c} {s} (var {x}) = begin
  ⟨ Var x ∷ c , s                         , ⟦ ρ ⟧ρ ⟩ ⟶⟨ Var ⟩
  ⟨         c , val (lookup x ⟦ ρ ⟧ρ) ∷ s , ⟦ ρ ⟧ρ ⟩ ≡⟨ cong (λ v → ⟨ c , val v ∷ s , ⟦ ρ ⟧ρ ⟩)
                                                             (lookup-hom x ρ) ⟩
  ⟨         c , val ⟦ lookup x ρ ⟧v   ∷ s , ⟦ ρ ⟧ρ ⟩ ∎
correct⇓′ {ρ = ρ} {c} {s} (con {i}) = begin
  ⟨ Con i ∷ c ,               s , ⟦ ρ ⟧ρ ⟩ ⟶⟨ Con ⟩
  ⟨         c , val (con i) ∷ s , ⟦ ρ ⟧ρ ⟩ ∎
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

correct⇑′ : ∀ {n} {ρ : C.Env n} {c s t} →
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
           ⟨ ⟦ t ⟧ [] , [] , [] ⟩ ⟶⋆ ⟨ [] , [ val ⟦ v ⟧v ] , [] ⟩
correct⇓ = correct⇓′

correct⇑ : ∀ {t} → [] ⊢ t ⇒ ⊥ → ⟨ ⟦ t ⟧ [] , [] , [] ⟩ ⟶∞
correct⇑ = ∞′→∞ ∘ correct⇑′
