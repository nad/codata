------------------------------------------------------------------------
-- Alternative functional semantics for an untyped λ-calculus with
-- constants
------------------------------------------------------------------------

-- I noted that the compiler correctness proof in
-- Lambda.Closure.Functional might be easier if the semantics was
-- defined using continuation-passing style, so I decided to try this
-- out. The proof at the end of this module /is/ slightly shorter, but
-- the overhead of working with a definition which uses nested
-- recursion/corecursion (in the current version of Agda) is quite
-- high. Furthermore it seemed to me as if the soundness proofs in
-- Lambda.Closure.Equivalence would be harder to prove using this
-- formulation of the semantics.

module Lambda.Closure.Functional.Alternative where

open import Category.Monad
open import Category.Monad.Partiality as Partiality
open import Coinduction
open import Data.List
open import Data.Maybe as Maybe
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function
open import Relation.Binary using (module Preorder)
open import Relation.Binary.PropositionalEquality as P using (_≡_)

open RelReasoning

open import Lambda.Syntax
open Closure Tm
open import Lambda.VirtualMachine renaming (⟦_⟧ to ⟦_⟧t)
open Functional
private
  module VM = Closure Code

------------------------------------------------------------------------
-- A monad with partiality and failure

PF : RawMonad (_⊥ ∘ Maybe)
PF = Maybe.monadT Partiality.monad

module PF where
  open RawMonad PF public

  fail : {A : Set} → Maybe A ⊥
  fail = now nothing

open PF

------------------------------------------------------------------------
-- Semantics

module Workaround₁ where

  -- This module provides a workaround for the limitations of
  -- guardedness.

  mutual

    data Maybe_⊥P (A : Set) : Set where
      ⌈_⌉   : (x : Maybe A ⊥) → Maybe A ⊥P
      later : (x : ∞ (Maybe A ⊥P)) → Maybe A ⊥P
      ⟦_⟧P  : ∀ {n} (t : Tm n) (ρ : Env n) (k : Value → Maybe A ⊥W) →
              Maybe A ⊥P

    data Maybe_⊥W (A : Set) : Set where
      ⌈_⌉   : (x : Maybe A ⊥) → Maybe A ⊥W
      later : (x : Maybe A ⊥P) → Maybe A ⊥W

  mutual

    -- The semantics, in slightly scrambled form.

    infix 5 _∙W_

    ⟦_⟧W : ∀ {A n} → Tm n → Env n → (Value → Maybe A ⊥W) → Maybe A ⊥W
    ⟦ con i ⟧W   ρ k = k (con i)
    ⟦ var x ⟧W   ρ k = k (lookup x ρ)
    ⟦ ƛ t ⟧W     ρ k = k (ƛ t ρ)
    ⟦ t₁ · t₂ ⟧W ρ k = ⟦ t₁ ⟧W ρ (λ v₁ →
                       ⟦ t₂ ⟧W ρ (λ v₂ →
                       (v₁ ∙W v₂) k))

    _∙W_ : ∀ {A} → Value → Value → (Value → Maybe A ⊥W) → Maybe A ⊥W
    (con i  ∙W v₂) k = ⌈ fail ⌉
    (ƛ t₁ ρ ∙W v₂) k = later (⟦ t₁ ⟧P (v₂ ∷ ρ) k)

  -- Interpretation of the definitions above.

  whnf : ∀ {A} → Maybe A ⊥P → Maybe A ⊥W
  whnf ⌈ x ⌉        = ⌈ x ⌉
  whnf (later x)    = later (♭ x)
  whnf (⟦ t ⟧P ρ k) = ⟦ t ⟧W ρ k

  mutual

    ⟪_⟫W : ∀ {A} → Maybe A ⊥W → Maybe A ⊥
    ⟪ ⌈ x ⌉    ⟫W = x
    ⟪ later  x ⟫W = later (♯ ⟪ x ⟫P)

    ⟪_⟫P : ∀ {A} → Maybe A ⊥P → Maybe A ⊥
    ⟪ x ⟫P = ⟪ whnf x ⟫W

-- The actual semantics. Note that this definition gives us
-- determinism "for free".

infix 5 _∙_

⟦_⟧ : ∀ {A n} → Tm n → Env n → (Value → Maybe A ⊥) → Maybe A ⊥
⟦ t ⟧ ρ k = ⟪ ⟦ t ⟧P ρ (λ v → ⌈ k v ⌉) ⟫P
  where open Workaround₁

_∙_ : ∀ {A} → Value → Value → (Value → Maybe A ⊥) → Maybe A ⊥
(v₁ ∙ v₂) k = ⟪ (v₁ ∙W v₂) (λ v → ⌈ k v ⌉) ⟫W
  where open Workaround₁

-- ⟦_⟧ and _∙_ preserve equality of their continuations.

module Workaround₂ {k : Kind} where

  open Workaround₁

  mutual

    infix 4 _≈P_ _≈W_

    data _≈P_ {A : Set} : Maybe A ⊥ → Maybe A ⊥ → Set where
      ⌈_⌉        : ∀ {x y} (x≈y : Rel k x y) → x ≈P y
      later      : ∀ {x y} (x≈y : ∞ (♭ x ≈P ♭ y)) → later x ≈P later y
      ⟦_⟧W-congP : ∀ {n} t (ρ : Env n) {k₁ k₂ : Value → Maybe A ⊥W}
                   (k₁≈k₂ : ∀ v → ⟪ k₁ v ⟫W ≈W ⟪ k₂ v ⟫W) →
                   ⟪ ⟦ t ⟧W ρ k₁ ⟫W ≈P ⟪ ⟦ t ⟧W ρ k₂ ⟫W

    data _≈W_ {A : Set} : Maybe A ⊥ → Maybe A ⊥ → Set where
      ⌈_⌉   : ∀ {x y} (x≈y : Rel k x y) → x ≈W y
      later : ∀ {x y} (x≈y : ♭ x ≈P ♭ y) → later x ≈W later y

  mutual

    ⟦_⟧W-congW : ∀ {A n} t (ρ : Env n) {k₁ k₂ : Value → Maybe A ⊥W} →
                 (∀ v → ⟪ k₁ v ⟫W ≈W ⟪ k₂ v ⟫W) →
                 ⟪ ⟦ t ⟧W ρ k₁ ⟫W ≈W ⟪ ⟦ t ⟧W ρ k₂ ⟫W
    ⟦ con i   ⟧W-congW ρ k₁≈k₂ = k₁≈k₂ (con i)
    ⟦ var x   ⟧W-congW ρ k₁≈k₂ = k₁≈k₂ (lookup x ρ)
    ⟦ ƛ t     ⟧W-congW ρ k₁≈k₂ = k₁≈k₂ (ƛ t ρ)
    ⟦ t₁ · t₂ ⟧W-congW ρ k₁≈k₂ = ⟦ t₁ ⟧W-congW ρ (λ v₁ →
                                 ⟦ t₂ ⟧W-congW ρ (λ v₂ →
                                 (v₁ ∙W v₂ -congW) k₁≈k₂))

    _∙W_-congW : ∀ {A} v₁ v₂ {k₁ k₂ : Value → Maybe A ⊥W} →
                 (∀ v → ⟪ k₁ v ⟫W ≈W ⟪ k₂ v ⟫W) →
                 ⟪ (v₁ ∙W v₂) k₁ ⟫W ≈W ⟪ (v₁ ∙W v₂) k₂ ⟫W
    (con i  ∙W v₂ -congW) k₁≈k₂ = ⌈ fail ∎ ⌉
    (ƛ t₁ ρ ∙W v₂ -congW) k₁≈k₂ = later (⟦ t₁ ⟧W-congP (v₂ ∷ ρ) k₁≈k₂)

  whnf≈ : ∀ {A} {x y : Maybe A ⊥} → x ≈P y → x ≈W y
  whnf≈ ⌈ x≈y ⌉                = ⌈ x≈y ⌉
  whnf≈ (later x≈y)            = later (♭ x≈y)
  whnf≈ (⟦ t ⟧W-congP ρ k₁≈k₂) = ⟦ t ⟧W-congW ρ k₁≈k₂

  mutual

    soundW : ∀ {A} {x y : Maybe A ⊥} → x ≈W y → Rel k x y
    soundW ⌈ x≈y ⌉     = x≈y
    soundW (later x≈y) = later (♯ soundP x≈y)

    soundP : ∀ {A} {x y : Maybe A ⊥} → x ≈P y → Rel k x y
    soundP x≈y = soundW (whnf≈ x≈y)

⟦_⟧-cong : ∀ {k A n} t (ρ : Env n) {k₁ k₂ : Value → Maybe A ⊥} →
           (∀ v → Rel k (k₁ v) (k₂ v)) →
           Rel k (⟦ t ⟧ ρ k₁) (⟦ t ⟧ ρ k₂)
⟦ t ⟧-cong ρ k₁≈k₂ = soundW (⟦ t ⟧W-congW ρ (λ v → ⌈ k₁≈k₂ v ⌉))
  where open Workaround₂

_∙_-cong : ∀ {k A} v₁ v₂ {k₁ k₂ : Value → Maybe A ⊥} →
           (∀ v → Rel k (k₁ v) (k₂ v)) →
           Rel k ((v₁ ∙ v₂) k₁) ((v₁ ∙ v₂) k₂)
(v₁ ∙ v₂ -cong) k₁≈k₂ = soundW ((v₁ ∙W v₂ -congW) (λ v → ⌈ k₁≈k₂ v ⌉))
  where open Workaround₂

-- ⟦_⟧ and _∙_ satisfy their intended defining equations.

sem-con : ∀ {A n} i {ρ : Env n} {k : Value → Maybe A ⊥} →
          ⟦ con i ⟧ ρ k ≅ k (con i)
sem-con i {k = k} = k (con i) ∎

sem-var : ∀ {A n} x {ρ : Env n} {k : Value → Maybe A ⊥} →
          ⟦ var x ⟧ ρ k ≅ k (lookup x ρ)
sem-var x {ρ} {k} = k (lookup x ρ) ∎

sem-ƛ : ∀ {A n} t {ρ : Env n} {k : Value → Maybe A ⊥} →
        ⟦ ƛ t ⟧ ρ k ≅ k (ƛ t ρ)
sem-ƛ t {ρ} {k} = k (ƛ t ρ) ∎

sem-· : ∀ {A n} t₁ t₂ {ρ : Env n} {k : Value → Maybe A ⊥} →
        ⟦ t₁ · t₂ ⟧ ρ k ≅ (⟦ t₁ ⟧ ρ λ v₁ → ⟦ t₂ ⟧ ρ λ v₂ → (v₁ ∙ v₂) k)
sem-· t₁ t₂ {ρ} {k} = soundW $
  ⟦ t₁ ⟧W-congW ρ λ v₁ →
  ⟦ t₂ ⟧W-congW ρ λ v₂ →
  ⌈ (v₁ ∙ v₂) k ∎ ⌉
  where open Workaround₂

app-con : ∀ {A} i v₂ {k : Value → Maybe A ⊥} →
          (con i ∙ v₂) k ≅ fail
app-con i v₂ = fail ∎

app-ƛ : ∀ {A n} t₁ (ρ : Env n) v₂ {k : Value → Maybe A ⊥} →
        (ƛ t₁ ρ ∙ v₂) k ≅ later (♯ ⟦ t₁ ⟧ (v₂ ∷ ρ) k)
app-ƛ t₁ ρ v₂ {k} = later (♯ (⟦ t₁ ⟧ (v₂ ∷ ρ) k ∎))

-- ⟦_⟧ and _∙_ are the unique solutions to the system of equations
-- which is intended to define them. I have stated this result using
-- strong equality, which is (more or less) the kind of equality you
-- get from a definition. I tried using weak equality instead, but
-- this turned out to make the proof tricky (due to the lack of
-- transitivity).

module Unique
  {A : Set}
  (⟪_⟫ : ∀ {n} t (ρ : Env n) (k : Value → Maybe A ⊥) → Maybe A ⊥)
  (_○_ : Value → Value → (Value → Maybe A ⊥) → Maybe A ⊥)

  (⟪con⟫ : ∀ {n} i {ρ : Env n} {k : Value → Maybe A ⊥} →
   ⟪ con i ⟫ ρ k ≅ k (con i))
  (⟪var⟫ : ∀ {n} x {ρ : Env n} {k : Value → Maybe A ⊥} →
   ⟪ var x ⟫ ρ k ≅ k (lookup x ρ))
  (⟪ƛ⟫ : ∀ {n} t {ρ : Env n} {k : Value → Maybe A ⊥} →
   ⟪ ƛ t ⟫ ρ k ≅ k (ƛ t ρ))
  (⟪·⟫ : ∀ {n} t₁ t₂ {ρ : Env n} {k : Value → Maybe A ⊥} →
   ⟪ t₁ · t₂ ⟫ ρ k ≅ (⟪ t₁ ⟫ ρ λ v₁ → ⟪ t₂ ⟫ ρ λ v₂ → (v₁ ○ v₂) k))

  (con○ : ∀ i v₂ {k : Value → Maybe A ⊥} →
   (con i ○ v₂) k ≅ fail)
  (ƛ○ : ∀ {n} t₁ (ρ : Env n) v₂ {k : Value → Maybe A ⊥} →
   (ƛ t₁ ρ ○ v₂) k ≅ later (♯ ⟪ t₁ ⟫ (v₂ ∷ ρ) k))
  where

  infix  4 _≅P_ _≅W_
  infixr 2 _≅⟨_⟩P_ _≅⟨_⟩W_ _≅⟪_⟫P_ _≅⟪_⟫W_

  mutual

    data _≅P_ : Maybe A ⊥ → Maybe A ⊥ → Set where
      _≅⟨_⟩P_ : ∀ x {y z} (x≅y : x ≅  y) (y≅z : y ≅P z) → x ≅P z
      _≅⟪_⟫P_ : ∀ x {y z} (x≅y : x ≅P y) (y≅z : y ≅  z) → x ≅P z
      semP    : ∀ {n} t {ρ : Env n} {k₁ k₂ : Value → Maybe A ⊥} →
                (k₁≅k₂ : ∀ v → k₁ v ≅W k₂ v) →
                ⟪ t ⟫ ρ k₁ ≅P ⟦ t ⟧ ρ k₂

    data _≅W_ : Maybe A ⊥ → Maybe A ⊥ → Set where
      ⌈_⌉    : ∀ {x y} (x≅y :   x ≅    y) →       x ≅W       y
      later  : ∀ {x y} (x≅y : ♭ x ≅P ♭ y) → later x ≅W later y

  _≅⟨_⟩W_ : ∀ x {y z} → x ≅ y → y ≅W z → x ≅W z
  _  ≅⟨ x≅y       ⟩W ⌈ y≅z ⌉    = ⌈ _ ≅⟨ x≅y ⟩ y≅z ⌉
  ._ ≅⟨ later x≅y ⟩W later  y≅z = later (_ ≅⟨ ♭ x≅y ⟩P y≅z)

  _≅⟪_⟫W_ : ∀ x {y z} → x ≅W y → y ≅ z → x ≅W z
  _  ≅⟪ ⌈ x≅y ⌉   ⟫W       y≅z = ⌈ _ ≅⟨ x≅y ⟩ y≅z ⌉
  ._ ≅⟪ later x≅y ⟫W later y≅z = later (_ ≅⟪ x≅y ⟫P ♭ y≅z)

  mutual

    semW : ∀ {n} t {ρ : Env n} {k₁ k₂ : Value → Maybe A ⊥} →
           (∀ v → k₁ v ≅W k₂ v) → ⟪ t ⟫ ρ k₁ ≅W ⟦ t ⟧ ρ k₂
    semW (con i) {ρ} {k₁} {k₂} k₁≅k₂ =
      ⟪ con i ⟫ ρ k₁  ≅⟨ ⟪con⟫ i ⟩W
      k₁ (con i)      ≅⟪ k₁≅k₂ _ ⟫W
      k₂ (con i)      ∎
    semW (var x) {ρ} {k₁} {k₂} k₁≅k₂ =
      ⟪ var x ⟫ ρ k₁   ≅⟨ ⟪var⟫ x ⟩W
      k₁ (lookup x ρ)  ≅⟪ k₁≅k₂ _ ⟫W
      k₂ (lookup x ρ)  ∎
    semW (ƛ t) {ρ} {k₁} {k₂} k₁≅k₂ =
      ⟪ ƛ t ⟫ ρ k₁  ≅⟨ ⟪ƛ⟫ t ⟩W
      k₁ (ƛ t ρ)    ≅⟪ k₁≅k₂ _ ⟫W
      k₂ (ƛ t ρ)    ∎
    semW (t₁ · t₂) {ρ} {k₁} {k₂} k₁≅k₂ =
      ⟪ t₁ · t₂ ⟫ ρ k₁                                ≅⟨ ⟪·⟫ t₁ t₂ ⟩W
      (⟪ t₁ ⟫ ρ λ v₁ → ⟪ t₂ ⟫ ρ λ v₂ → (v₁ ○ v₂) k₁)  ≅⟪ semW t₁ (λ v₁ → semW t₂ (λ v₂ → appW v₁ v₂ k₁≅k₂)) ⟫W
      (⟦ t₁ ⟧ ρ λ v₁ → ⟦ t₂ ⟧ ρ λ v₂ → (v₁ ∙ v₂) k₂)  ≅⟨ sym $ sem-· t₁ t₂ ⟩
      ⟦ t₁ · t₂ ⟧ ρ k₂                                ∎

    appW : ∀ v₁ v₂ {k₁ k₂ : Value → Maybe A ⊥} →
           (∀ v → k₁ v ≅W k₂ v) → (v₁ ○ v₂) k₁ ≅W (v₁ ∙ v₂) k₂
    appW (con i) v₂ {k₁} {k₂} k₁≅k₂ =
      ⌈ (con i ○ v₂) k₁  ≅⟨ con○ i v₂ ⟩
        fail             ∎ ⌉
    appW (ƛ t₁ ρ) v₂ {k₁} {k₂} k₁≅k₂ =
      (ƛ t₁ ρ ○ v₂) k₁  ≅⟨ ƛ○ t₁ ρ v₂ ⟩W
      later _           ≅⟪ later (semP t₁ k₁≅k₂) ⟫W
      (ƛ t₁ ρ ∙ v₂) k₂  ∎

  whnf : ∀ {x y} → x ≅P y → x ≅W y
  whnf (x ≅⟨ x≅y ⟩P y≅z) = x ≅⟨      x≅y ⟩W whnf y≅z
  whnf (x ≅⟪ x≅y ⟫P y≅z) = x ≅⟪ whnf x≅y ⟫W      y≅z
  whnf (semP t k₁≅k₂)    = semW t k₁≅k₂

  mutual

    soundW : ∀ {x y} → x ≅W y → x ≅ y
    soundW ⌈ x≅y ⌉     = x≅y
    soundW (later x≅y) = later (♯ soundP x≅y)

    soundP : ∀ {x y} → x ≅P y → x ≅ y
    soundP x≅y = soundW (whnf x≅y)

  sem : ∀ {n} t {ρ : Env n} {k : Value → Maybe A ⊥} →
        ⟪ t ⟫ ρ k ≅ ⟦ t ⟧ ρ k
  sem t {k = k} = soundW (semW t (λ v → ⌈ k v ∎ ⌉))

  app : ∀ v₁ v₂ {k : Value → Maybe A ⊥} →
        (v₁ ○ v₂) k ≅ (v₁ ∙ v₂) k
  app v₁ v₂ {k} = soundW (appW v₁ v₂ (λ v → ⌈ k v ∎ ⌉))

------------------------------------------------------------------------
-- Example

ω : Tm 0
ω = ƛ (vr 0 · vr 0)

Ω : Tm 0
Ω = ω · ω

Ω-loops : ⟦ Ω ⟧ [] return ≈ never
Ω-loops = later (♯ Ω-loops)

------------------------------------------------------------------------
-- Compiler correctness

module Correctness {k : OtherKind} where

  infix  4 _≈P_ _≈W_
  infixr 2 _≡⟨_⟩W_ _≈⟨_⟩P_ _≈⟨_⟩W_

  mutual

    data _≈P_ : Maybe VM.Value ⊥ → Maybe VM.Value ⊥ → Set where
      _≈⟨_⟩P_ : ∀ x {y z} (x≈y : x ≈P y) (y≅z : y ≅ z) → x ≈P z
      correct :
        ∀ {n} t {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
        (hyp : ∀ v → exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ≈W k v) →
        exec ⟨ ⟦ t ⟧t c , s , ⟦ ρ ⟧ρ ⟩ ≈P ⟦ t ⟧ ρ k

    data _≈W_ : Maybe VM.Value ⊥ → Maybe VM.Value ⊥ → Set where
      ⌈_⌉    : ∀ {x y} (x≈y : Rel (other k) x y) → x ≈W y
      later  : ∀ {x y} (x≈y : ♭ x ≈P ♭ y) → later x ≈W later y
      laterˡ : ∀ {x y} (x≈y : ♭ x ≈W   y) → later x ≈W       y

  _≡⟨_⟩W_ : ∀ x {y z} → x ≡ y → y ≈W z → x ≈W z
  _ ≡⟨ P.refl ⟩W y≈z = y≈z

  _≈⟨_⟩W_ : ∀ x {y z} → x ≈W y → y ≅ z → x ≈W z
  ._ ≈⟨ later  x≈y ⟩W later y≅z = later  (_ ≈⟨ x≈y ⟩P ♭ y≅z)
  ._ ≈⟨ laterˡ x≈y ⟩W       y≅z = laterˡ (_ ≈⟨ x≈y ⟩W   y≅z)
  _  ≈⟨ ⌈ x≈y ⌉    ⟩W       y≅z = ⌈ trans x≈y (≅⇒ y≅z) ⌉
    where trans = Preorder.trans (Partiality.preorder _ _)

  correctW :
    ∀ {n} t {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
    (∀ v → exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ≈W k v) →
    exec ⟨ ⟦ t ⟧t c , s , ⟦ ρ ⟧ρ ⟩ ≈W ⟦ t ⟧ ρ k
  correctW (con i) {ρ} {c} {s} {k} hyp = laterˡ (
    exec ⟨ c , val (con i) ∷ s , ⟦ ρ ⟧ρ ⟩  ≈⟨ hyp (con i) ⟩W
    k (con i)                              ∎)
  correctW (var x) {ρ} {c} {s} {k} hyp = laterˡ (
    exec ⟨ c , val (lookup x ⟦ ρ ⟧ρ) ∷ s , ⟦ ρ ⟧ρ ⟩  ≡⟨ P.cong (λ v → exec ⟨ c , val v ∷ s , ⟦ ρ ⟧ρ ⟩) $
                                                          lookup-hom x ρ ⟩W
    exec ⟨ c , val ⟦ lookup x ρ ⟧v   ∷ s , ⟦ ρ ⟧ρ ⟩  ≈⟨ hyp (lookup x ρ) ⟩W
    k (lookup x ρ)                                   ∎)
  correctW (ƛ t) {ρ} {c} {s} {k} hyp = laterˡ (
    exec ⟨ c , val ⟦ ƛ t ρ ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩  ≈⟨ hyp (ƛ t ρ) ⟩W
    k (ƛ t ρ)                                 ∎)
  correctW (t₁ · t₂) {ρ} {c} {s} {k} hyp =
    exec ⟨ ⟦ t₁ ⟧t (⟦ t₂ ⟧t (App ∷ c)) , s , ⟦ ρ ⟧ρ ⟩  ≈⟨ correctW t₁ (λ v₁ → correctW t₂ (λ v₂ → ∙-correctW v₁ v₂)) ⟩W
    (⟦ t₁ ⟧ ρ λ v₁ → ⟦ t₂ ⟧ ρ λ v₂ → (v₁ ∙ v₂) k)      ≅⟨ sym $ sem-· t₁ t₂ ⟩
    ⟦ t₁ · t₂ ⟧ ρ k                                    ∎
    where
    ∙-correctW :
      ∀ v₁ v₂ →
      exec ⟨ App ∷ c , val ⟦ v₂ ⟧v ∷ val ⟦ v₁ ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ≈W
      (v₁ ∙ v₂) k
    ∙-correctW (con i)   v₂ = ⌈ fail ∎ ⌉
    ∙-correctW (ƛ t₁ ρ′) v₂ = later (
      exec ⟨ ⟦ t₁ ⟧t [ Ret ] , ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v₂ ∷ ρ′ ⟧ρ ⟩  ≈⟨ correct t₁ (λ v → laterˡ (hyp v)) ⟩P
      ⟦ t₁ ⟧ (v₂ ∷ ρ′) k                                          ∎)

  whnf : ∀ {x y} → x ≈P y → x ≈W y
  whnf (x ≈⟨ x≈y ⟩P y≅z) = x ≈⟨ whnf x≈y ⟩W y≅z
  whnf (correct t hyp)   = correctW t hyp

  mutual

    soundW : ∀ {x y} → x ≈W y → Rel (other k) x y
    soundW ⌈ x≈y ⌉      = x≈y
    soundW (later  x≈y) = later (♯ soundP x≈y)
    soundW (laterˡ x≈y) = laterˡ (soundW x≈y)

    soundP : ∀ {x y} → x ≈P y → Rel (other k) x y
    soundP x≈y = soundW (whnf x≈y)

-- Note that the statement of compiler correctness used here is more
-- useful, and less involved, than the one in
-- Lambda.Closure.Relational. The latter statement does not apply to
-- terms which crash. Furthermore it is not a self-contained
-- correctness statement, but relies on a separate proof which shows
-- that the VM is deterministic.

correct : ∀ t →
          exec ⟨ ⟦ t ⟧t [] , [] , [] ⟩ ≳
          ⟦ t ⟧ [] (λ v → return ⟦ v ⟧v)
correct t =
  soundP $ Correctness.correct t (λ v → ⌈ return ⟦ v ⟧v ∎ ⌉)
  where open Correctness