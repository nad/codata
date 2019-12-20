------------------------------------------------------------------------
-- A virtual machine
------------------------------------------------------------------------

module Lambda.VirtualMachine where

open import Category.Monad
open import Category.Monad.Partiality as P
  using (_⊥; never); open P._⊥
open import Codata.Musical.Notation
open import Data.Empty using (⊥-elim)
open import Data.Fin
open import Data.List hiding (lookup)
open import Data.Maybe
open import Data.Nat
open import Data.Product as Prod
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function.Base
import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive
  hiding (return)
open import Relation.Binary.PropositionalEquality as PE using (_≡_)
open import Relation.Nullary

open RawMonad (P.monad {f = Level.zero})

open import Lambda.Syntax
private module C = Closure Tm

------------------------------------------------------------------------
-- Instruction set

mutual

  -- Instructions.

  data Instr (n : ℕ) : Set where
    var : (x : Fin n) → Instr n
    con : (i : ℕ) → Instr n
    clo : (c : Code (suc n)) → Instr n
    app : Instr n
    ret : Instr n

  -- Code.

  Code : ℕ → Set
  Code n = List (Instr n)

-- Environments and values.

open Closure Code

------------------------------------------------------------------------
-- Compiler

-- The compiler takes a code continuation.

comp : ∀ {n} → Tm n → Code n → Code n
comp (con i)   c = con i ∷ c
comp (var x)   c = var x ∷ c
comp (ƛ t)     c = clo (comp t [ ret ]) ∷ c
comp (t₁ · t₂) c = comp t₁ (comp t₂ (app ∷ c))

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → C.Env n → Env n
  comp-env []      = []
  comp-env (v ∷ ρ) = comp-val v ∷ comp-env ρ

  comp-val : C.Value → Value
  comp-val (C.con i) = con i
  comp-val (C.ƛ t ρ) = ƛ (comp t [ ret ]) (comp-env ρ)

-- lookup x is homomorphic with respect to comp-env/comp-val.

lookup-hom : ∀ {n} (x : Fin n) ρ →
             lookup (comp-env ρ) x ≡ comp-val (lookup ρ x)
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
    var : ∀ {n} {x : Fin n} {c s ρ} →
          ⟨ var x ∷ c , s , ρ ⟩ ⟶ ⟨ c , val (lookup ρ x) ∷ s , ρ ⟩
    con : ∀ {n i} {c : Code n} {s ρ} →
          ⟨ con i ∷ c , s , ρ ⟩ ⟶ ⟨ c , val (con i) ∷ s , ρ ⟩
    clo : ∀ {n} {c : Code n} {c′ s ρ} →
          ⟨ clo c′ ∷ c , s , ρ ⟩ ⟶ ⟨ c , val (ƛ c′ ρ) ∷ s , ρ ⟩
    app : ∀ {n} {c : Code n} {v n′} {c′ : Code (suc n′)} {ρ′ s ρ} →
          ⟨ app ∷ c , val v ∷ val (ƛ c′ ρ′) ∷ s , ρ ⟩ ⟶ ⟨ c′ , ret c ρ ∷ s , v ∷ ρ′ ⟩
    ret : ∀ {n} {c : Code n} {v n′} {c′ : Code n′} {ρ′ s ρ} →
          ⟨ ret ∷ c , val v ∷ ret c′ ρ′ ∷ s , ρ ⟩ ⟶ ⟨ c′ , val v ∷ s , ρ′ ⟩

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
    infix  3 _⟶∞⟨_⟩
    infixr 2 _⟶⟨_⟩′_ _⟶⋆⟨_⟩′_

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
  step ⟨ []         ,                 val v ∷ [] , [] ⟩ = done v
  step ⟨ var x  ∷ c ,                          s , ρ  ⟩ = continue ⟨ c  , val (lookup ρ x) ∷ s ,     ρ  ⟩
  step ⟨ con i  ∷ c ,                          s , ρ  ⟩ = continue ⟨ c  , val (con i)      ∷ s ,     ρ  ⟩
  step ⟨ clo c′ ∷ c ,                          s , ρ  ⟩ = continue ⟨ c  , val (ƛ c′ ρ)     ∷ s ,     ρ  ⟩
  step ⟨ app    ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ  ⟩ = continue ⟨ c′ , ret c ρ          ∷ s , v ∷ ρ′ ⟩
  step ⟨ ret    ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ  ⟩ = continue ⟨ c′ , val v            ∷ s ,     ρ′ ⟩
  step _                                                = crash

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
    crash₅  : ∀ {n c ρ}              → Crashing (⟨_,_,_⟩ {    n} (app ∷ c)                            []        ρ )
    crash₆  : ∀ {n c v ρ}            → Crashing (⟨_,_,_⟩ {    n} (app ∷ c) (         val v          ∷ [])       ρ )
    crash₇  : ∀ {n c n′ c′ ρ′ s ρ}   → Crashing (⟨_,_,_⟩ {    n} (app ∷ c) (         ret {n′} c′ ρ′ ∷ s )       ρ )
    crash₈  : ∀ {n c v i s ρ}        → Crashing (⟨_,_,_⟩ {    n} (app ∷ c) (val v  ∷ val (con i)    ∷ s )       ρ )
    crash₉  : ∀ {n c v n′ c′ ρ′ s ρ} → Crashing (⟨_,_,_⟩ {    n} (app ∷ c) (val v  ∷ ret {n′} c′ ρ′ ∷ s )       ρ )
    crash₁₀ : ∀ {n c ρ}              → Crashing (⟨_,_,_⟩ {    n} (ret ∷ c)                            []        ρ )
    crash₁₁ : ∀ {n c v ρ}            → Crashing (⟨_,_,_⟩ {    n} (ret ∷ c) (         val v          ∷ [])       ρ )
    crash₁₂ : ∀ {n c n′ c′ ρ′ s ρ}   → Crashing (⟨_,_,_⟩ {    n} (ret ∷ c) (         ret {n′} c′ ρ′ ∷ s )       ρ )
    crash₁₃ : ∀ {n c v₁ v₂ s ρ}      → Crashing (⟨_,_,_⟩ {    n} (ret ∷ c) (val v₁ ∷ val v₂         ∷ s )       ρ )

  -- There are three kinds of states.

  data Kind (s : State) : Set where
    done     : ∀ {v} (s⇓v : s ⇓ v)    → Kind s
    continue : ∀ {s′} (s⟶s′ : s ⟶ s′) → Kind s
    crash    : (s↯ : Crashing s)      → Kind s

  -- We can assign (at least) one kind to every state.

  kind : ∀ s → Kind s
  kind ⟨ []         ,                 val v ∷ [] , [] ⟩ = done final
  kind ⟨ var x  ∷ c ,                          s , ρ  ⟩ = continue var
  kind ⟨ con i  ∷ c ,                          s , ρ  ⟩ = continue con
  kind ⟨ clo c′ ∷ c ,                          s , ρ  ⟩ = continue clo
  kind ⟨ app    ∷ c , val v ∷ val (ƛ c′ ρ′) ∷  s , ρ  ⟩ = continue app
  kind ⟨ ret    ∷ c , val v ∷ ret c′ ρ′     ∷  s , ρ  ⟩ = continue ret

  kind ⟨ []      ,                       [] , _     ⟩ = crash crash₁
  kind ⟨ []      ,         ret _ _     ∷ _  , _     ⟩ = crash crash₂
  kind ⟨ []      , val _ ∷ _           ∷ _  , _     ⟩ = crash crash₃
  kind ⟨ []      ,         val _       ∷ [] , _ ∷ _ ⟩ = crash crash₄
  kind ⟨ app ∷ _ ,                       [] , _     ⟩ = crash crash₅
  kind ⟨ app ∷ _ ,         val _       ∷ [] , _     ⟩ = crash crash₆
  kind ⟨ app ∷ _ ,         ret _ _     ∷ _  , _     ⟩ = crash crash₇
  kind ⟨ app ∷ _ , val _ ∷ val (con _) ∷ _  , _     ⟩ = crash crash₈
  kind ⟨ app ∷ _ , val _ ∷ ret _ _     ∷ _  , _     ⟩ = crash crash₉
  kind ⟨ ret ∷ _ ,                       [] , _     ⟩ = crash crash₁₀
  kind ⟨ ret ∷ _ ,         val _       ∷ [] , _     ⟩ = crash crash₁₁
  kind ⟨ ret ∷ _ ,         ret _ _     ∷ _  , _     ⟩ = crash crash₁₂
  kind ⟨ ret ∷ _ , val _ ∷ val _       ∷ _  , _     ⟩ = crash crash₁₃

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
  ⇒⇓ ε           final = now PE.refl
  ⇒⇓ (var ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (con ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (clo ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (app ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)
  ⇒⇓ (ret ◅ s⟶⋆) ⇓     = laterˡ (⇒⇓ s⟶⋆ ⇓)

  ⇒⇑ : ∀ {s} → s ⟶∞ → exec s ≈ never
  ⇒⇑ (var ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (con ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (clo ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (app ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))
  ⇒⇑ (ret ◅ s⟶∞) = later (♯ (⇒⇑ (♭ s⟶∞)))

  ⇒↯ : ∀ {s} → ∃ (λ s′ → s ⟶⋆ s′ × Stuck s′) → exec s ≈ return nothing
  ⇒↯ (_ , var ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , con ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , clo ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , app ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (_ , ret ◅ s⟶⋆ , ↯) = laterˡ (⇒↯ (_ , s⟶⋆ , ↯))
  ⇒↯ (s , ε          , ↯) with kind s
  ... | done s⇓v       = ⊥-elim (proj₂ ↯ (-, s⇓v))
  ... | continue s₁⟶s₂ = ⊥-elim (proj₁ ↯ (-, s₁⟶s₂))
  ... | crash s↯       = exec-crashes s↯

  ----------------------------------------------------------------------
  -- The relational semantics is complete with respect to the
  -- functional one

  ⇐⇓ : ∀ {s v} → exec s ≈ return (just v) → ∃ λ s′ → s ⟶⋆ s′ × s′ ⇓ v
  ⇐⇓ {s = s} ⇓ with kind s
  ⇐⇓ (now PE.refl) | done final   = (_ , ε , final)
  ⇐⇓ (laterˡ ⇓)    | continue var = Prod.map id (Prod.map (_◅_ var) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue con = Prod.map id (Prod.map (_◅_ con) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue clo = Prod.map id (Prod.map (_◅_ clo) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue app = Prod.map id (Prod.map (_◅_ app) id) (⇐⇓ ⇓)
  ⇐⇓ (laterˡ ⇓)    | continue ret = Prod.map id (Prod.map (_◅_ ret) id) (⇐⇓ ⇓)
  ⇐⇓ {s} {v} ⇓     | crash s↯      with
    return (just v)  ≈⟨ sym ⇓ ⟩
    exec s           ≈⟨ exec-crashes s↯ ⟩
    return nothing   ∎
    where open EqReasoning
  ... | now ()

  ⇐⇑ : ∀ {s} → exec s ≈ never → s ⟶∞
  ⇐⇑ {s = s} ⇑ with kind s
  ⇐⇑         ⇑ | done final   = ⊥-elim (now≉never ⇑)
  ⇐⇑         ⇑ | continue var = var ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue con = con ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue clo = clo ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue app = app ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑         ⇑ | continue ret = ret ◅ ♯ ⇐⇑ (later⁻¹ ⇑)
  ⇐⇑ {s}     ⇑ | crash s↯     = ⊥-elim (now≉never (
    return nothing  ≈⟨ sym $ exec-crashes s↯ ⟩
    exec s          ≈⟨ ⇑ ⟩
    never           ∎))
    where open EqReasoning

  ⇐↯ : ∀ {s} → exec s ≈ return nothing → ∃ λ s′ → s ⟶⋆ s′ × Stuck s′
  ⇐↯ {s = s} ↯ with kind s
  ⇐↯ (now ())   | done final
  ⇐↯ (laterˡ ↯) | continue var = Prod.map id (Prod.map (_◅_ var) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue con = Prod.map id (Prod.map (_◅_ con) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue clo = Prod.map id (Prod.map (_◅_ clo) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue app = Prod.map id (Prod.map (_◅_ app) id) $ ⇐↯ ↯
  ⇐↯ (laterˡ ↯) | continue ret = Prod.map id (Prod.map (_◅_ ret) id) $ ⇐↯ ↯
  ⇐↯         ↯  | crash s↯     = (_ , ε , ⟶-crashes s↯)
