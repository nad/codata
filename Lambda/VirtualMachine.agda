------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

module Lambda.VirtualMachine where

open import Category.Monad
open import Category.Monad.Partiality as P
  using (_⊥; never); open P._⊥
open import Coinduction
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Product as Prod
open import Data.Star hiding (return)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function
open import Level
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary

open RawMonad (P.monad {f = zero})

open import Lambda.Syntax
private module C = Closure Tm

------------------------------------------------------------------------
-- Instruction set

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

-- Environments and values.

open Closure Code

------------------------------------------------------------------------
-- Compiler

-- The compiler is formulated in continuation-passing style.

⟦_⟧ : ∀ {n} → Tm n → Code n → Code n
⟦ con i ⟧   c = Con i ∷ c
⟦ var x ⟧   c = Var x ∷ c
⟦ ƛ t ⟧     c = Clos (⟦ t ⟧ [ Ret ]) ∷ c
⟦ t₁ · t₂ ⟧ c = ⟦ t₁ ⟧ (⟦ t₂ ⟧ (App ∷ c))

-- Environments and values can also be compiled.

mutual

  ⟦_⟧ρ : ∀ {n} → C.Env n → Env n
  ⟦ []    ⟧ρ = []
  ⟦ v ∷ ρ ⟧ρ = ⟦ v ⟧v ∷ ⟦ ρ ⟧ρ

  ⟦_⟧v : C.Value → Value
  ⟦ con i ⟧v = con i
  ⟦ ƛ t ρ ⟧v = ƛ (⟦ t ⟧ [ Ret ]) ⟦ ρ ⟧ρ

-- ⟦_⟧ρ/⟦_⟧v is homomorphic with respect to lookup.

lookup-hom : ∀ {n} (x : Fin n) ρ → lookup x ⟦ ρ ⟧ρ ≡ ⟦ lookup x ρ ⟧v
lookup-hom zero    (v ∷ ρ) = PE.refl
lookup-hom (suc x) (v ∷ ρ) = lookup-hom x ρ

------------------------------------------------------------------------
-- Stacks and states

-- Stacks.

data StackElement : Set where
  val : (v : Value) → StackElement
  ret : ∀ {n} (c : Code n) (ρ : Env n) → StackElement

Stack : Set
Stack = List StackElement

-- States.

data State : Set where
  ⟨_,_,_⟩ : ∀ {n} (c : Code n) (s : Stack) (ρ : Env n) → State

------------------------------------------------------------------------
-- Relational semantics of the VM

module Relational where

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

  -- Final (stuck) states.

  Final : State → Set
  Final s = ∄ λ s′ → s ⟶ s′

  -- s ⇓ v means that s is a successful final state, and that the
  -- corresponding value is v.

  infix 4 _⇓_

  data _⇓_ : State → Value → Set where
    final : ∀ {v} → ⟨ [] , val v ∷ [] , [] ⟩ ⇓ v

  -- Sanity check.

  ⇓-final : ∀ {s v} → s ⇓ v → Final s
  ⇓-final final (_ , ())

  -- Crashing stuck states.

  Stuck : State → Set
  Stuck s = Final s × ∄ (λ v → s ⇓ v)

  -- Reflexive transitive closure.

  infix 4 _⟶⋆_

  _⟶⋆_ : State → State → Set
  _⟶⋆_ = Star _⟶_

  -- Infinite sequences of steps.

  infixr 5 _◅_
  infix  4 _⟶∞

  data _⟶∞ : State → Set where
    _◅_ : ∀ {s₁ s₂} (s₁⟶s₂ : s₁ ⟶ s₂) (s₂⟶∞ : ∞ (s₂ ⟶∞)) → s₁ ⟶∞

  -- A variant of _⟶∞ which is easier to use.

  module InfiniteSequence where

    infix  4 _⟶∞′
    infixr 2 _⟶⟨_⟩′_ _⟶⋆⟨_⟩′_
    infix  2 _⟶∞⟨_⟩

    data _⟶∞′ : State → Set where
      _⟶⟨_⟩′_  : ∀ s₁ {s₂} (s₁⟶s₂ : s₁ ⟶ s₂) (s₂⟶∞ : ∞ (s₂ ⟶∞′)) → s₁ ⟶∞′
      _⟶⋆⟨_⟩′_ : ∀ s₁ {s₂} (s₁⟶⋆s₂ : s₁ ⟶⋆ s₂) (s₂⟶∞ : s₂ ⟶∞′) → s₁ ⟶∞′
      _⟶∞⟨_⟩   : ∀ s (s⟶∞ : s ⟶∞′) → s ⟶∞′

    sound : ∀ {s} → s ⟶∞′ → s ⟶∞
    sound (s₁ ⟶⟨ s₁⟶s₂ ⟩′ s₂⟶∞)           = s₁⟶s₂ ◅ ♯ (sound (♭ s₂⟶∞))
    sound (s  ⟶⋆⟨ ε ⟩′ s⟶∞)               = sound s⟶∞
    sound (s₁ ⟶⋆⟨ s₁⟶s₂ ◅ s₂⟶⋆s₃ ⟩′ s₃⟶∞) = s₁⟶s₂ ◅ ♯ (sound (_ ⟶⋆⟨ s₂⟶⋆s₃ ⟩′ s₃⟶∞))
    sound (s  ⟶∞⟨ s⟶∞ ⟩)                  = sound s⟶∞

    complete : ∀ {s} → s ⟶∞ → s ⟶∞′
    complete (s₁⟶s₂ ◅ s₂⟶∞) = _ ⟶⟨ s₁⟶s₂ ⟩′ ♯ complete (♭ s₂⟶∞)

------------------------------------------------------------------------
-- Functional semantics of the VM

module Functional where

  -- The result of running the VM one step.

  data Result : Set where
    continue : (s : State) → Result
    done     : (v : Value) → Result
    crash    : Result

  -- A single step of the computation.

  step : State → Result
  step ⟨ []          ,                 val v ∷ [] , [] ⟩ = done v
  step ⟨ Var x   ∷ c ,                          s , ρ  ⟩ = continue ⟨ c  , val (lookup x ρ) ∷ s ,     ρ  ⟩
  step ⟨ Con i   ∷ c ,                          s , ρ  ⟩ = continue ⟨ c  , val (con i)      ∷ s ,     ρ  ⟩
  step ⟨ Clos c′ ∷ c ,                          s , ρ  ⟩ = continue ⟨ c  , val (ƛ c′ ρ)     ∷ s ,     ρ  ⟩
  step ⟨ App     ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ  ⟩ = continue ⟨ c′ , ret c ρ          ∷ s , v ∷ ρ′ ⟩
  step ⟨ Ret     ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ  ⟩ = continue ⟨ c′ , val v            ∷ s ,     ρ′ ⟩
  step _                                                 = crash

  -- The VM.

  exec : State → Maybe Value ⊥
  exec s with step s
  ... | continue s′ = later (♯ exec s′)
  ... | done v      = return (just v)
  ... | crash       = return nothing

  -- Equality for partial computations returning Maybe Value.
  --
  -- Note that propositional equality is used for the underlying
  -- values, which can include code components. In other words, if
  -- v₁ ≈ v₂, then any code components in these values have to be
  -- /syntactically/ equal.

  module Equality where

    private
      open module PEq {A : Set} = P.Equality {A = A} _≡_ public
        using (_≈_; now; later; laterˡ)

    open P public using (later⁻¹; now≉never)

    module EqReasoning {A : Set} = P.Reasoning {A = A} PE.isEquivalence

------------------------------------------------------------------------
-- Equivalence proof

module Equivalence where

  open Relational
  open Functional
  open Functional.Equality

  ----------------------------------------------------------------------
  -- Classification of states

  -- Inductive characterisation of states which are stuck and not
  -- final.

  data Crashing : State → Set where
    crash₁  : ∀ {n ρ}                → Crashing (⟨_,_,_⟩ {    n}        []                            []        ρ )
    crash₂  : ∀ {n n′ c ρ′ s ρ}      → Crashing (⟨_,_,_⟩ {    n}        [] (         ret {n′} c ρ′  ∷ s )       ρ )
    crash₃  : ∀ {n v e s ρ}          → Crashing (⟨_,_,_⟩ {    n}        [] (val v  ∷ e              ∷ s )       ρ )
    crash₄  : ∀ {n v₁ v₂ ρ}          → Crashing (⟨_,_,_⟩ {suc n}        [] (         val v₁         ∷ []) (v₂ ∷ ρ))
    crash₅  : ∀ {n c ρ}              → Crashing (⟨_,_,_⟩ {    n} (App ∷ c)                            []        ρ )
    crash₆  : ∀ {n c v ρ}            → Crashing (⟨_,_,_⟩ {    n} (App ∷ c) (         val v          ∷ [])       ρ )
    crash₇  : ∀ {n c n′ c′ ρ′ s ρ}   → Crashing (⟨_,_,_⟩ {    n} (App ∷ c) (         ret {n′} c′ ρ′ ∷ s )       ρ )
    crash₈  : ∀ {n c v i s ρ}        → Crashing (⟨_,_,_⟩ {    n} (App ∷ c) (val v  ∷ val (con i)    ∷ s )       ρ )
    crash₉  : ∀ {n c v n′ c′ ρ′ s ρ} → Crashing (⟨_,_,_⟩ {    n} (App ∷ c) (val v  ∷ ret {n′} c′ ρ′ ∷ s )       ρ )
    crash₁₀ : ∀ {n c ρ}              → Crashing (⟨_,_,_⟩ {    n} (Ret ∷ c)                            []        ρ )
    crash₁₁ : ∀ {n c v ρ}            → Crashing (⟨_,_,_⟩ {    n} (Ret ∷ c) (         val v          ∷ [])       ρ )
    crash₁₂ : ∀ {n c n′ c′ ρ′ s ρ}   → Crashing (⟨_,_,_⟩ {    n} (Ret ∷ c) (         ret {n′} c′ ρ′ ∷ s )       ρ )
    crash₁₃ : ∀ {n c v₁ v₂ s ρ}      → Crashing (⟨_,_,_⟩ {    n} (Ret ∷ c) (val v₁ ∷ val v₂         ∷ s )       ρ )

  -- There are three kinds of states.

  data Kind (s : State) : Set where
    done     : ∀ {v} (s⇓v : s ⇓ v)    → Kind s
    continue : ∀ {s′} (s⟶s′ : s ⟶ s′) → Kind s
    crash    : (s↯ : Crashing s)      → Kind s

  -- We can assign (at least) one kind to every state.

  kind : ∀ s → Kind s
  kind ⟨ []          ,                 val v ∷ [] , [] ⟩ = done final
  kind ⟨ Var x   ∷ c ,                          s , ρ  ⟩ = continue Var
  kind ⟨ Con i   ∷ c ,                          s , ρ  ⟩ = continue Con
  kind ⟨ Clos c′ ∷ c ,                          s , ρ  ⟩ = continue Clos
  kind ⟨ App     ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ  ⟩ = continue App
  kind ⟨ Ret     ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ  ⟩ = continue Ret

  kind ⟨ []      ,                       [] , _     ⟩ = crash crash₁
  kind ⟨ []      ,         ret _ _     ∷ _  , _     ⟩ = crash crash₂
  kind ⟨ []      , val _ ∷ _           ∷ _  , _     ⟩ = crash crash₃
  kind ⟨ []      ,         val _       ∷ [] , _ ∷ _ ⟩ = crash crash₄
  kind ⟨ App ∷ _ ,                       [] , _     ⟩ = crash crash₅
  kind ⟨ App ∷ _ ,         val _       ∷ [] , _     ⟩ = crash crash₆
  kind ⟨ App ∷ _ ,         ret _ _     ∷ _  , _     ⟩ = crash crash₇
  kind ⟨ App ∷ _ , val _ ∷ val (con _) ∷ _  , _     ⟩ = crash crash₈
  kind ⟨ App ∷ _ , val _ ∷ ret _ _     ∷ _  , _     ⟩ = crash crash₉
  kind ⟨ Ret ∷ _ ,                       [] , _     ⟩ = crash crash₁₀
  kind ⟨ Ret ∷ _ ,         val _       ∷ [] , _     ⟩ = crash crash₁₁
  kind ⟨ Ret ∷ _ ,         ret _ _     ∷ _  , _     ⟩ = crash crash₁₂
  kind ⟨ Ret ∷ _ , val _ ∷ val _       ∷ _  , _     ⟩ = crash crash₁₃

  -- The functional semantics crashes for crashing states.

  exec-crashes : ∀ {s} → Crashing s → exec s ≈ return nothing
  exec-crashes crash₁  = now PE.refl
  exec-crashes crash₂  = now PE.refl
  exec-crashes crash₃  = now PE.refl
  exec-crashes crash₄  = now PE.refl
  exec-crashes crash₅  = now PE.refl
  exec-crashes crash₆  = now PE.refl
  exec-crashes crash₇  = now PE.refl
  exec-crashes crash₈  = now PE.refl
  exec-crashes crash₉  = now PE.refl
  exec-crashes crash₁₀ = now PE.refl
  exec-crashes crash₁₁ = now PE.refl
  exec-crashes crash₁₂ = now PE.refl
  exec-crashes crash₁₃ = now PE.refl

  -- The relational semantics also crashes for crashing states.

  ⟶-crashes : ∀ {s} → Crashing s → Stuck s
  ⟶-crashes s↯ = (helper₁ s↯ , helper₂ s↯)
    where
    helper₁ : ∀ {s} → Crashing s → Final s
    helper₁ crash₁  (_ , ())
    helper₁ crash₂  (_ , ())
    helper₁ crash₃  (_ , ())
    helper₁ crash₄  (_ , ())
    helper₁ crash₅  (_ , ())
    helper₁ crash₆  (_ , ())
    helper₁ crash₇  (_ , ())
    helper₁ crash₈  (_ , ())
    helper₁ crash₉  (_ , ())
    helper₁ crash₁₀ (_ , ())
    helper₁ crash₁₁ (_ , ())
    helper₁ crash₁₂ (_ , ())
    helper₁ crash₁₃ (_ , ())

    helper₂ : ∀ {s} → Crashing s → ∄ λ v → s ⇓ v
    helper₂ crash₁  (_ , ())
    helper₂ crash₂  (_ , ())
    helper₂ crash₃  (_ , ())
    helper₂ crash₄  (_ , ())
    helper₂ crash₅  (_ , ())
    helper₂ crash₆  (_ , ())
    helper₂ crash₇  (_ , ())
    helper₂ crash₈  (_ , ())
    helper₂ crash₉  (_ , ())
    helper₂ crash₁₀ (_ , ())
    helper₂ crash₁₁ (_ , ())
    helper₂ crash₁₂ (_ , ())
    helper₂ crash₁₃ (_ , ())

  ----------------------------------------------------------------------
  -- The relational semantics is sound with respect to the functional
  -- one

  -- Note that these proofs implicitly establish that the relational
  -- semantics is deterministic.

  ⇒⇓ : ∀ {s s′ v} → s ⟶⋆ s′ → s′ ⇓ v → exec s ≈ return (just v)
  ⇒⇓ ε            final = now PE.refl
  ⇒⇓ (Var  ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (Con  ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (Clos ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (App  ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (Ret  ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)

  ⇒⇑ : ∀ {s} → s ⟶∞ → exec s ≈ never
  ⇒⇑ (Var  ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (Con  ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (Clos ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (App  ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (Ret  ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))

  ⇒↯ : ∀ {s} → ∃ (λ s′ → s ⟶⋆ s′ × Stuck s′) → exec s ≈ return nothing
  ⇒↯ (_ , Var  ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , Con  ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , Clos ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , App  ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , Ret  ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (s , ε          , ↯) with kind s
  ... | done s⇓v       = ⊥-elim (proj₂ ↯ (, s⇓v))
  ... | continue s₁⟶s₂ = ⊥-elim (proj₁ ↯ (, s₁⟶s₂))
  ... | crash s↯       = exec-crashes s↯

  ----------------------------------------------------------------------
  -- The relational semantics is complete with respect to the
  -- functional one

  ⇐⇓ : ∀ {s v} → exec s ≈ return (just v) → ∃ λ s′ → s ⟶⋆ s′ × s′ ⇓ v
  ⇐⇓ {s = s} ⇓ with kind s
  ⇐⇓ (now PE.refl) | done final    = (_ , ε , final)
  ⇐⇓ (laterˡ ⇓)    | continue Var  = Prod.map id (Prod.map (_◅_ Var ) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue Con  = Prod.map id (Prod.map (_◅_ Con ) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue Clos = Prod.map id (Prod.map (_◅_ Clos) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue App  = Prod.map id (Prod.map (_◅_ App ) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue Ret  = Prod.map id (Prod.map (_◅_ Ret ) id) (⇐⇓ ⇓)
  ⇐⇓ {s} {v} ⇓     | crash s↯      with
    return (just v)  ≈⟨ sym ⇓ ⟩
    exec s           ≈⟨ exec-crashes s↯ ⟩
    return nothing   ∎
    where open EqReasoning
  ... | now ()

  ⇐⇑ : ∀ {s} → exec s ≈ never → s ⟶∞
  ⇐⇑ {s = s} ⇑ with kind s
  ⇐⇑         ⇑ | done final    = ⊥-elim (now≉never ⇑)
  ⇐⇑         ⇑ | continue Var  = Var  ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue Con  = Con  ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue Clos = Clos ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue App  = App  ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue Ret  = Ret  ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑ {s}     ⇑ | crash s↯      = ⊥-elim (now≉never (
    return nothing  ≈⟨ sym $ exec-crashes s↯ ⟩
    exec s          ≈⟨ ⇑ ⟩
    never           ∎))
    where open EqReasoning

  ⇐↯ : ∀ {s} → exec s ≈ return nothing → ∃ λ s′ → s ⟶⋆ s′ × Stuck s′
  ⇐↯ {s = s} ↯ with kind s
  ⇐↯ (now ())   | done final
  ⇐↯ (laterˡ ↯) | continue Var  = Prod.map id (Prod.map (_◅_ Var ) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue Con  = Prod.map id (Prod.map (_◅_ Con ) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue Clos = Prod.map id (Prod.map (_◅_ Clos) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue App  = Prod.map id (Prod.map (_◅_ App ) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue Ret  = Prod.map id (Prod.map (_◅_ Ret ) id) $ ⇐↯ ↯
  ⇐↯         ↯  | crash s↯      = (_ , ε , ⟶-crashes s↯)
