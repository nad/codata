------------------------------------------------------------------------
-- Functional semantics for a non-deterministic untyped λ-calculus
-- with constants
------------------------------------------------------------------------

module Lambda.Closure.Functional.Non-deterministic where

open import Category.Monad.Partiality as Pa using (_⊥; now; later)
open import Coinduction
open import Data.Fin using (Fin; zero; suc; #_)
open import Data.List
open import Data.Maybe
open import Data.Nat
open import Data.Vec using ([]; _∷_; lookup)
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Decidable

open import Lambda.Syntax using (Ty; Ctxt)
open Lambda.Syntax.Closure using (con; ƛ)
open Lambda.Syntax.Ty
open import Lambda.VirtualMachine
  hiding (comp; comp-val; comp-env; lookup-hom)
open Functional
private
  module VM = Lambda.Syntax.Closure Code

------------------------------------------------------------------------
-- A monad with partiality, failure and non-determinism

module D where

  -- This is basically the maybe monad transformer applied to the
  -- partiality monad transformer applied to the non-determinism monad
  -- N A = μX. A ⊎ X × X. Unfortunately it is somewhat awkward to
  -- implement the partiality monad transformer in Agda: the
  -- definition
  --
  --   data Partiality′ (M : Set → Set) (A : Set) : Set where
  --     now-or-later : M (A ⊎ Partiality′ M A) → Partiality′ M A
  --
  -- is rejected, because M might use its argument negatively.

  infixr 6 _∣_

  data D (A : Set) : Set where
    fail   : D A
    return : (x : A) → D A
    _∣_    : (x y : D A) → D A
    later  : (x : ∞ (D A)) → D A

  -- The function force n removes (up to) n layers of later
  -- constructors.

  force : {A : Set} → ℕ → D A → D A
  force (suc n) (later x) = force n (♭ x)
  force n       (x₁ ∣ x₂) = force n x₁ ∣ force n x₂
  force _       x         = x

  -- Bind.

  infixl 5 _>>=_

  _>>=_ : {A B : Set} → D A → (A → D B) → D B
  fail      >>= f = fail
  return x  >>= f = f x
  (x₁ ∣ x₂) >>= f = (x₁ >>= f) ∣ (x₂ >>= f)
  later x   >>= f = later (♯ (♭ x >>= f))

  -- A deterministic non-terminating computation.

  never : {A : Set} → D A
  never = later (♯ never)

  -- Strong bisimilarity.

  infix 4 _≅_

  data _≅_ {A : Set} : D A → D A → Set where
    fail   : fail ≅ fail
    return : ∀ {x} → return x ≅ return x
    _∣_    : ∀ {x₁ x₂ y₁ y₂}
             (x₁≅y₁ : x₁ ≅ y₁) (x₂≅y₂ : x₂ ≅ y₂) → x₁ ∣ x₂ ≅ y₁ ∣ y₂
    later  : ∀ {x y} (x≅y : ∞ (♭ x ≅ ♭ y)) → later x ≅ later y

  -- Strong bisimilarity is reflexive.

  infixr 3 _∎

  _∎ : {A : Set} (x : D A) → x ≅ x
  fail     ∎ = fail
  return x ∎ = return
  x₁ ∣ x₂  ∎ = (x₁ ∎) ∣ (x₂ ∎)
  later x  ∎ = later (♯ (♭ x ∎))

  -- Strong bisimilarity is symmetric.

  sym : {A : Set} {x y : D A} → x ≅ y → y ≅ x
  sym fail            = fail
  sym return          = return
  sym (x₁≅y₁ ∣ x₂≅y₂) = sym x₁≅y₁ ∣ sym x₂≅y₂
  sym (later x≅y)     = later (♯ sym (♭ x≅y))

  -- Strong bisimilarity is transitive.

  infixr 2 _≅⟨_⟩_

  _≅⟨_⟩_ : ∀ {A : Set} (x : D A) {y z} → x ≅ y → y ≅ z → x ≅ z
  ._ ≅⟨ fail          ⟩ fail          = fail
  ._ ≅⟨ return        ⟩ return        = return
  ._ ≅⟨ x₁≅y₁ ∣ x₂≅y₂ ⟩ y₁≅z₁ ∣ y₂≅z₂ = (_ ≅⟨ x₁≅y₁ ⟩ y₁≅z₁) ∣ (_ ≅⟨ x₂≅y₂ ⟩ y₂≅z₂)
  ._ ≅⟨ later x≅y     ⟩ later y≅z     = later (♯ (_ ≅⟨ ♭ x≅y ⟩ ♭ y≅z))

  -- The monad laws hold up to strong bisimilarity.

  left-identity : {A B : Set} {x : A} {f : A → D B} →
                  return x >>= f ≅ f x
  left-identity {x = x} {f} = f x ∎

  right-identity : {A : Set} (x : D A) → x >>= return ≅ x
  right-identity fail       = fail
  right-identity (return x) = return
  right-identity (x₁ ∣ x₂)  = right-identity x₁ ∣ right-identity x₂
  right-identity (later x)  = later (♯ right-identity (♭ x))

  associative : {A B C : Set} (x : D A) {f : A → D B} {g : B → D C} →
                x >>= f >>= g ≅ x >>= λ y → f y >>= g
  associative fail               = fail
  associative (return x) {f} {g} = f x >>= g ∎
  associative (x₁ ∣ x₂)          = associative x₁ ∣ associative x₂
  associative (later x)          = later (♯ associative (♭ x))

  -- Bind respects strong bisimilarity.

  infixl 5 _>>=-cong_

  _>>=-cong_ : {A B : Set} {x₁ x₂ : D A} {f₁ f₂ : A → D B} →
               x₁ ≅ x₂ → (∀ y → f₁ y ≅ f₂ y) → x₁ >>= f₁ ≅ x₂ >>= f₂
  fail          >>=-cong f₁≅f₂ = fail
  return        >>=-cong f₁≅f₂ = f₁≅f₂ _
  later x≅y     >>=-cong f₁≅f₂ = later (♯ (♭ x≅y >>=-cong f₁≅f₂))
  x₁≅x₂ ∣ y₁≅y₂ >>=-cong f₁≅f₂ =
    (x₁≅x₂ >>=-cong f₁≅f₂) ∣ (y₁≅y₂ >>=-cong f₁≅f₂)

  -- More laws.

  never-left-zero : {A B : Set} {f : A → D B} → never >>= f ≅ never
  never-left-zero = later (♯ never-left-zero)

  fail-left-zero : {A B : Set} {f : A → D B} → fail >>= f ≅ fail
  fail-left-zero = fail ∎

open D using (D; _≅_; _≅⟨_⟩_; _∎; _>>=-cong_) hiding (module D)
open D.D
open D._≅_

------------------------------------------------------------------------
-- Syntax

infixl 9 _·_
infixr 6 _∣_

data Tm (n : ℕ) : Set where
  con : (i : ℕ) → Tm n
  var : (x : Fin n) → Tm n
  ƛ   : (t : Tm (suc n)) → Tm n
  _·_ : (t₁ t₂ : Tm n) → Tm n
  _∣_ : (t₁ t₂ : Tm n) → Tm n

-- Convenient helper.

vr : ∀ m {n} {m<n : True (suc m ≤? n)} → Tm n
vr _ {m<n = m<n} = var (#_ _ {m<n = m<n})

open Lambda.Syntax.Closure Tm hiding (con; ƛ)

------------------------------------------------------------------------
-- A workaround for the limitations of guardedness

module Workaround where

  infixr 6 _∣_
  infixl 5 _>>=_

  data DP : Set → Set₁ where
    fail   : ∀ {A} → DP A
    return : ∀ {A} (x : A) → DP A
    _∣_    : ∀ {A} (x y : DP A) → DP A
    later  : ∀ {A} (x : ∞ (DP A)) → DP A
    _>>=_  : ∀ {A B} (x : DP A) (f : A → DP B) → DP B

  private

    data DW : Set → Set₁ where
      fail   : ∀ {A} → DW A
      return : ∀ {A} (x : A) → DW A
      _∣_    : ∀ {A} (x y : DW A) → DW A
      later  : ∀ {A} (x : DP A) → DW A

    mutual

      _>>=W_ : ∀ {A B} → DW A → (A → DP B) → DW B
      fail     >>=W f = fail
      return x >>=W f = whnf (f x)
      (x ∣ y)  >>=W f = (x >>=W f) ∣ (y >>=W f)
      later x  >>=W f = later (x >>= f)

      whnf : ∀ {A} → DP A → DW A
      whnf fail       = fail
      whnf (return x) = return x
      whnf (later x)  = later (♭ x)
      whnf (x ∣ y)    = whnf x ∣ whnf y
      whnf (x >>= f)  = whnf x >>=W f

  mutual

    private

      ⟪_⟫W : ∀ {A} → DW A → D A
      ⟪ fail     ⟫W = fail
      ⟪ return x ⟫W = return x
      ⟪ x ∣ y    ⟫W = ⟪ x ⟫W ∣ ⟪ y ⟫W
      ⟪ later x  ⟫W = later (♯ ⟪ x ⟫P)

    ⟪_⟫P : ∀ {A} → DP A → D A
    ⟪ p ⟫P = ⟪ whnf p ⟫W

  -- The definitions above make sense. ⟪_⟫P is homomorphic with respect
  -- to fail, return, _∣_, later and _>>=_.

  fail-hom : ∀ {A} → ⟪ fail {A = A} ⟫P ≅ fail
  fail-hom = fail ∎

  return-hom : ∀ {A} (x : A) → ⟪ return x ⟫P ≅ return x
  return-hom x = return x ∎

  ∣-hom : ∀ {A} (x y : DP A) → ⟪ x ∣ y ⟫P ≅ ⟪ x ⟫P ∣ ⟪ y ⟫P
  ∣-hom x y = ⟪ x ⟫P ∣ ⟪ y ⟫P ∎

  later-hom : ∀ {A} (x : ∞ (DP A)) → ⟪ later x ⟫P ≅ later (♯ ⟪ ♭ x ⟫P)
  later-hom x = later (♯ (⟪ ♭ x ⟫P ∎))

  mutual

    private

      >>=-homW : ∀ {A B} (x : DW A) (f : A → DP B) →
                 ⟪ x >>=W f ⟫W ≅ D._>>=_ ⟪ x ⟫W (λ y → ⟪ f y ⟫P)
      >>=-homW fail       f = fail ∎
      >>=-homW (return x) f = ⟪ f x ⟫P ∎
      >>=-homW (x ∣ y)    f = >>=-homW x f ∣ >>=-homW y f
      >>=-homW (later x)  f = later (♯ >>=-hom x f)

    >>=-hom : ∀ {A B} (x : DP A) (f : A → DP B) →
              ⟪ x >>= f ⟫P ≅ D._>>=_ ⟪ x ⟫P (λ y → ⟪ f y ⟫P)
    >>=-hom x f = >>=-homW (whnf x) f

open Workaround hiding (_>>=_)

------------------------------------------------------------------------
-- Semantics

infix 9 _∙_

mutual

  ⟦_⟧′ : ∀ {n} → Tm n → Env n → DP Value
  ⟦ con i ⟧′   ρ = return (con i)
  ⟦ var x ⟧′   ρ = return (lookup x ρ)
  ⟦ ƛ t ⟧′     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ >>= λ v₁ →
                   ⟦ t₂ ⟧′ ρ >>= λ v₂ →
                   v₁ ∙ v₂
                   where open Workaround
  ⟦ t₁ ∣ t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ ∣ ⟦ t₂ ⟧′ ρ

  _∙_ : Value → Value → DP Value
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = later (♯ (⟦ t₁ ⟧′ (v₂ ∷ ρ)))

⟦_⟧ : ∀ {n} → Tm n → Env n → D Value
⟦ t ⟧ ρ = ⟪ ⟦ t ⟧′ ρ ⟫P

-- An abbreviation.

infix 9 _⟦·⟧_

_⟦·⟧_ : D Value → D Value → D Value
v₁ ⟦·⟧ v₂ = v₁ >>= λ v₁ → v₂ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P
  where open D

-- The semantics of application is compositional (with respect to the
-- syntactic equality which is used).

·-comp : ∀ {n} (t₁ t₂ : Tm n) {ρ} →
         ⟦ t₁ · t₂ ⟧ ρ ≅ ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ
·-comp t₁ t₂ {ρ} =
  ⟦ t₁ · t₂ ⟧ ρ                                   ≅⟨ >>=-hom (⟦ t₁ ⟧′ ρ) _ ⟩

  D._>>=_ (⟦ t₁ ⟧ ρ) (λ v₁ →
          ⟪ Workaround._>>=_ (⟦ t₂ ⟧′ ρ) (λ v₂ →
            v₁ ∙ v₂) ⟫P)                          ≅⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ →
                                                      >>=-hom (⟦ t₂ ⟧′ ρ) _) ⟩
  ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ                           ∎

open D

------------------------------------------------------------------------
-- Compiler

-- The compiler takes a code continuation.
--
-- Non-determinism is resolved by always picking the left choice.

comp : ∀ {n} → Tm n → Code n → Code n
comp (con i)   c = con i ∷ c
comp (var x)   c = var x ∷ c
comp (ƛ t)     c = clo (comp t [ ret ]) ∷ c
comp (t₁ · t₂) c = comp t₁ (comp t₂ (app ∷ c))
comp (t₁ ∣ t₂) c = comp t₁ c

-- Environments and values can also be compiled.

mutual

  comp-env : ∀ {n} → Env n → VM.Env n
  comp-env []      = []
  comp-env (v ∷ ρ) = comp-val v ∷ comp-env ρ

  comp-val : Value → VM.Value
  comp-val (con i) = con i
  comp-val (ƛ t ρ) = ƛ (comp t [ ret ]) (comp-env ρ)

-- lookup x is homomorphic with respect to comp-env/comp-val.

lookup-hom : ∀ {n} (x : Fin n) ρ →
             lookup x (comp-env ρ) ≡ comp-val (lookup x ρ)
lookup-hom zero    (v ∷ ρ) = P.refl
lookup-hom (suc x) (v ∷ ρ) = lookup-hom x ρ

------------------------------------------------------------------------
-- Examples

-- A non-terminating term.

Ω : Tm 0
Ω = ω · ω
  where ω = ƛ (vr 0 · vr 0)

Ω-loops : ⟦ Ω ⟧ [] ≅ never
Ω-loops = later (♯ Ω-loops)

-- A call-by-value fix-point combinator.

Z : {n : ℕ} → Tm n
Z = ƛ (t · t)
  where t = ƛ (vr 1 · ƛ (vr 1 · vr 1 · vr 0))

-- A non-deterministically non-terminating term.

! : Tm 0
! = Z · ƛ (ƛ (vr 1 · vr 0 ∣ vr 1 · vr 0)) · con 0

-- Its semantics.

!-sem : D Value
!-sem = later (♯ later (♯ later (♯ later (♯ (!-sem ∣ !-sem)))))

⟦!⟧≅!-sem : ⟦ ! ⟧ [] ≅ !-sem
⟦!⟧≅!-sem = later (♯ lem)
  where
  lem : force 1 (⟦ ! ⟧ []) ≅ force 1 !-sem
  lem = later (♯ later (♯ later (♯ (later (♯ lem) ∣ later (♯ lem)))))

-- How did I come up with this proof term? Through a manual
-- calculation...
--
-- Let us first define some abbreviations:
--
--   t₀ = vr 1 · vr 1 · vr 0
--   t₁ = ƛ t₀
--   t₂ = vr 1 · t₁
--   t₃ = ƛ t₂
--
--   u₀ = vr 1 · vr 0
--   u₁ = u₀ ∣ u₀
--   u₂ = ƛ u₁
--   u₃ = ƛ u₂
--
--   c₀ = ƛ u₂ []
--   c₁ = ƛ t₂ (c₀ ∷ [])
--   c₂ = ƛ t₀ (c₁ ∷ c₀ ∷ [])
--
-- Now we can calculate as follows (ignoring ♯):
--
--   ⟦ Z · u₃ · con 0 ⟧ []
-- = ⟦ Z · u₃ ⟧ [] ⟦·⟧ return (con 0)
-- = ƛ (t₃ · t₃) [] ∙ c₀ ⟦·⟧ return (con 0)
-- = later (⟦ t₃ · t₃ ⟧ (c₀ ∷ []) ⟦·⟧ return (con 0))
-- = later (c₁ ∙ c₁ ⟦·⟧ return (con 0))
--
-- = c₁ ∙ c₁ ⟦·⟧ return (con 0)
-- = later (⟦ t₂ ⟧ (c₁ ∷ c₀ ∷ []) ⟦·⟧ return (con 0))
-- = later (c₀ ∙ c₂ ⟦·⟧ return (con 0))
-- = later (later (⟦ u₂ ⟧ (c₂ ∷ []) ⟦·⟧ return (con 0)))
-- = later (later (ƛ u₁ (c₂ ∷ []) ∙ con 0))
-- = later (later (later (⟦ u₁ ⟧ (con 0 ∷ c₂ ∷ []))))
-- = later (later (later (⟦ u₀ ⟧ (con 0 ∷ c₂ ∷ []) ∣
--                        ⟦ u₀ ⟧ (con 0 ∷ c₂ ∷ []))))
-- = later (later (later (c₂ ∙ con 0 ∣ c₂ ∙ con 0)))
-- = later (later (later (⟦ t₀ ⟧ (con 0 ∷ c₁ ∷ c₀ ∷ []) ∣
--                        ⟦ t₀ ⟧ (con 0 ∷ c₁ ∷ c₀ ∷ []))))
-- = later (later (later (later (c₁ ∙ c₁ ⟦·⟧ return (con 0)) ∣
--                        later (c₁ ∙ c₁ ⟦·⟧ return (con 0)))))

------------------------------------------------------------------------
-- A relation relating deterministic and non-deterministic
-- computations

-- x ≈∈ y means that x implements /one/ possible semantics of y (up to
-- weak bisimilarity).

infix 4 _≈∈_

data _≈∈_ {A : Set} : Maybe A ⊥ → D A → Set where
  fail   : now nothing ≈∈ fail

  return : ∀ {x} → now (just x) ≈∈ return x

  ∣ˡ     : ∀ {x y₁ y₂} (x≈∈y₁ : x ≈∈ y₁) → x ≈∈ y₁ ∣ y₂
  ∣ʳ     : ∀ {x y₁ y₂} (x≈∈y₂ : x ≈∈ y₂) → x ≈∈ y₁ ∣ y₂

  later  : ∀ {x y} (x≈∈y : ∞ (♭ x ≈∈ ♭ y)) → later x ≈∈ later y
  laterˡ : ∀ {x y} (x≈∈y :    ♭ x ≈∈   y ) → later x ≈∈       y
  laterʳ : ∀ {x y} (x≈∈y :      x ≈∈ ♭ y ) →       x ≈∈ later y

-- A transitivity-like result for _≡_ and _≈∈_.

infixr 2 _≡⟨_⟩_

_≡⟨_⟩_ : ∀ {A : Set} (x : Maybe A ⊥) {y z} → x ≡ y → y ≈∈ z → x ≈∈ z
_ ≡⟨ P.refl ⟩ y≈z = y≈z

-- A transitivity-like result for _≈∈_ and _≅_.

infixr 2 _≈∈⟨_⟩_

_≈∈⟨_⟩_ : ∀ {A : Set} (x : Maybe A ⊥) {y z} → x ≈∈ y → y ≅ z → x ≈∈ z
._ ≈∈⟨ fail        ⟩ fail          = fail
._ ≈∈⟨ return      ⟩ return        = return
_  ≈∈⟨ ∣ˡ x₁≈∈y₁   ⟩ y₁≅z₁ ∣ y₂≅z₂ = ∣ˡ (_ ≈∈⟨ x₁≈∈y₁ ⟩ y₁≅z₁)
_  ≈∈⟨ ∣ʳ x₂≈∈y₂   ⟩ y₁≅z₁ ∣ y₂≅z₂ = ∣ʳ (_ ≈∈⟨ x₂≈∈y₂ ⟩ y₂≅z₂)
._ ≈∈⟨ later  x≈∈y ⟩ later y≅z     = later (♯ (_ ≈∈⟨ ♭ x≈∈y ⟩ ♭ y≅z))
._ ≈∈⟨ laterˡ x≈∈y ⟩       y≅z     = laterˡ   (_ ≈∈⟨   x≈∈y ⟩   y≅z)
_  ≈∈⟨ laterʳ x≈∈y ⟩ later y≅z     = laterʳ   (_ ≈∈⟨   x≈∈y ⟩ ♭ y≅z)

-- An example.

lemma : Pa.never ≈∈ !-sem
lemma = later (♯ later (♯ later (♯ later (♯ ∣ˡ lemma))))

------------------------------------------------------------------------
-- Compiler correctness

module Correctness where

  infix  4 _≈∈P_ _≈∈W_
  infixr 2 _≡⟨_⟩W_ _≈∈⟨_⟩P_ _≈∈⟨_⟩W_

  mutual

    data _≈∈P_ : Maybe VM.Value ⊥ → D VM.Value → Set where
      _≈∈⟨_⟩P_ : ∀ x {y z} (x≈y : x ≈∈P y) (y≅z : y ≅ z) → x ≈∈P z
      correct :
        ∀ {n} t {ρ : Env n} {c s} {k : Value → D VM.Value} →
        (hyp : ∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩
                       ≈∈W k v) →
        exec ⟨ comp t c , s , comp-env ρ ⟩ ≈∈P (⟦ t ⟧ ρ >>= k)

    data _≈∈W_ : Maybe VM.Value ⊥ → D VM.Value → Set where
      ⌈_⌉    : ∀ {x y} (x≈y : x ≈∈ y) → x ≈∈W y
      ∣ˡ     : ∀ {x y₁ y₂} (x≈y₁ : x ≈∈W y₁) → x ≈∈W y₁ ∣ y₂
      later  : ∀ {x y} (x≈y : ♭ x ≈∈P ♭ y) → later x ≈∈W later y
      laterˡ : ∀ {x y} (x≈y : ♭ x ≈∈W   y) → later x ≈∈W       y

  _≡⟨_⟩W_ : ∀ x {y z} → x ≡ y → y ≈∈W z → x ≈∈W z
  _ ≡⟨ P.refl ⟩W y≈z = y≈z

  _≈∈⟨_⟩W_ : ∀ x {y z} → x ≈∈W y → y ≅ z → x ≈∈W z
  _  ≈∈⟨ ⌈ x≈y ⌉    ⟩W       y≅z     = ⌈ _ ≈∈⟨ x≈y ⟩ y≅z ⌉
  _  ≈∈⟨ ∣ˡ x≈y₁    ⟩W y₁≅z₁ ∣ y₂≅z₂ = ∣ˡ (_ ≈∈⟨ x≈y₁ ⟩W y₁≅z₁)
  ._ ≈∈⟨ later  x≈y ⟩W later y≅z     = later  (_ ≈∈⟨ x≈y ⟩P ♭ y≅z)
  ._ ≈∈⟨ laterˡ x≈y ⟩W       y≅z     = laterˡ (_ ≈∈⟨ x≈y ⟩W   y≅z)

  mutual

    correctW :
      ∀ {n} t {ρ : Env n} {c s} {k : Value → D VM.Value} →
      (∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈∈W k v) →
      exec ⟨ comp t c , s , comp-env ρ ⟩ ≈∈W (⟦ t ⟧ ρ >>= k)
    correctW (con i) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (con i) ∷ s , comp-env ρ ⟩  ≈∈⟨ hyp (con i) ⟩W
      k (con i)                                  ∎)
    correctW (var x) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (lookup x (comp-env ρ)) ∷ s , comp-env ρ ⟩  ≡⟨ P.cong (λ v → exec ⟨ c , val v ∷ s , comp-env ρ ⟩) (lookup-hom x ρ) ⟩W
      exec ⟨ c , val (comp-val (lookup x ρ)) ∷ s , comp-env ρ ⟩  ≈∈⟨ hyp (lookup x ρ) ⟩W
      k (lookup x ρ)                                             ∎)
    correctW (ƛ t) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (comp-val (ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≈∈⟨ hyp (ƛ t ρ) ⟩W
      k (ƛ t ρ)                                             ∎)
    correctW (t₁ · t₂) {ρ} {c} {s} {k} hyp =
      exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩           ≈∈⟨ correctW t₁ (λ v₁ → correctW t₂ (λ v₂ →
                                                                            ∙-correctW v₁ v₂ hyp)) ⟩W
      (⟦ t₁ ⟧ ρ >>= λ v₁ →  ⟦ t₂ ⟧ ρ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P  >>= k)  ≅⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ → sym $ associative (⟦ t₂ ⟧ ρ)) ⟩
      (⟦ t₁ ⟧ ρ >>= λ v₁ → (⟦ t₂ ⟧ ρ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P) >>= k)  ≅⟨ sym $ associative (⟦ t₁ ⟧ ρ) ⟩
      (⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ >>= k)                                   ≅⟨ sym (·-comp t₁ t₂ >>=-cong λ v → k v ∎) ⟩
      (⟦ t₁ · t₂ ⟧ ρ >>= k)                                           ∎
    correctW (t₁ ∣ t₂) {ρ} {c} {s} {k} hyp =
      exec ⟨ comp t₁ c , s , comp-env ρ ⟩  ≈∈⟨ ∣ˡ (correctW t₁ hyp) ⟩W
      (⟦ t₁ ⟧ ρ >>= k) ∣ (⟦ t₂ ⟧ ρ >>= k)  ∎

    ∙-correctW :
      ∀ {n} v₁ v₂ {ρ : Env n} {c s} {k : Value → D VM.Value} →
      (∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈∈W k v) →
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s , comp-env ρ ⟩ ≈∈W
      ⟪ v₁ ∙ v₂ ⟫P >>= k
    ∙-correctW (con i)   v₂                 _   = ⌈ fail ⌉
    ∙-correctW (ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val (ƛ t₁ ρ₁)) ∷ s , comp-env ρ ⟩  ≈∈⟨ later (

        exec ⟨ comp t₁ [ ret ] , ret c (comp-env ρ) ∷ s , comp-env (v₂ ∷ ρ₁) ⟩                ≈∈⟨ correct t₁ (λ v → laterˡ (hyp v)) ⟩P
        (⟦ t₁ ⟧ (v₂ ∷ ρ₁) >>= k)                                                              ∎) ⟩W

      (⟪ ƛ t₁ ρ₁ ∙ v₂ ⟫P >>= k)                                                         ∎

  whnf : ∀ {x y} → x ≈∈P y → x ≈∈W y
  whnf (x ≈∈⟨ x≈y ⟩P y≅z) = x ≈∈⟨ whnf x≈y ⟩W y≅z
  whnf (correct t hyp)    = correctW t hyp

  mutual

    soundW : ∀ {x y} → x ≈∈W y → x ≈∈ y
    soundW ⌈ x≈y ⌉      = x≈y
    soundW (∣ˡ x≈y₁)    = ∣ˡ (soundW x≈y₁)
    soundW (later  x≈y) = later (♯ soundP x≈y)
    soundW (laterˡ x≈y) = laterˡ (soundW x≈y)

    soundP : ∀ {x y} → x ≈∈P y → x ≈∈ y
    soundP x≈y = soundW (whnf x≈y)

correct : ∀ t →
          exec ⟨ comp t [] , [] , [] ⟩ ≈∈
          ⟦ t ⟧ [] >>= λ v → return (comp-val v)
correct t =
  soundP $ Correctness.correct t (λ _ → ⌈ return ⌉)
  where open Correctness

------------------------------------------------------------------------
-- Type system (following Leroy and Grall)

infix 4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctxt n) : Tm n → Ty → Set where
  con : ∀ {i} → Γ ⊢ con i ∈ nat
  var : ∀ {x} → Γ ⊢ var x ∈ lookup x Γ
  ƛ   : ∀ {t σ τ} (t∈ : ♭ σ ∷ Γ ⊢ t ∈ ♭ τ) → Γ ⊢ ƛ t ∈ σ ⇾ τ
  _·_ : ∀ {t₁ t₂ σ τ} (t₁∈ : Γ ⊢ t₁ ∈ σ ⇾ τ) (t₂∈ : Γ ⊢ t₂ ∈ ♭ σ) →
        Γ ⊢ t₁ · t₂ ∈ ♭ τ
  _∣_ : ∀ {t₁ t₂ σ} (t₁∈ : Γ ⊢ t₁ ∈ σ) (t₂∈ : Γ ⊢ t₂ ∈ σ) →
        Γ ⊢ t₁ ∣ t₂ ∈ σ

-- Ω is well-typed.

Ω-well-typed : (τ : Ty) → [] ⊢ Ω ∈ τ
Ω-well-typed τ =
  _·_ {σ = ♯ σ} {τ = ♯ τ} (ƛ (var · var)) (ƛ (var · var))
  where σ = ♯ σ ⇾ ♯ τ

-- The call-by-value fix-point combinator is also well-typed.

fix-well-typed :
  ∀ {σ τ} → [] ⊢ Z ∈ ♯ (♯ (σ ⇾ τ) ⇾ ♯ (σ ⇾ τ)) ⇾ ♯ (σ ⇾ τ)
fix-well-typed =
  ƛ (_·_ {σ = υ} {τ = ♯ _}
         (ƛ (var · ƛ (var · var · var)))
         (ƛ (var · ƛ (var · var · var))))
  where
  υ : ∞ Ty
  υ = ♯ (υ ⇾ ♯ _)

------------------------------------------------------------------------
-- Type soundness

-- WF-Value, WF-Env and WF-DV specify when a
-- value/environment/computation is well-formed with respect to a
-- given context (and type).

mutual

  data WF-Value : Ty → Value → Set where
    con : ∀ {i} → WF-Value nat (con i)
    ƛ   : ∀ {n Γ σ τ} {t : Tm (1 + n)} {ρ}
          (t∈ : ♭ σ ∷ Γ ⊢ t ∈ ♭ τ) (ρ-wf : WF-Env Γ ρ) →
          WF-Value (σ ⇾ τ) (ƛ t ρ)

  infixr 5 _∷_

  data WF-Env : ∀ {n} → Ctxt n → Env n → Set where
    []  : WF-Env [] []
    _∷_ : ∀ {n} {Γ : Ctxt n} {ρ σ v}
          (v-wf : WF-Value σ v) (ρ-wf : WF-Env Γ ρ) →
          WF-Env (σ ∷ Γ) (v ∷ ρ)

data WF-DV (σ : Ty) : D Value → Set where
  return : ∀ {v} (v-wf : WF-Value σ v) → WF-DV σ (return v)
  _∣_    : ∀ {x y}
           (x-wf : WF-DV σ x) (y-wf : WF-DV σ y) → WF-DV σ (x ∣ y)
  later  : ∀ {x} (x-wf : ∞ (WF-DV σ (♭ x))) → WF-DV σ (later x)

-- Variables pointing into a well-formed environment refer to
-- well-formed values.

lookup-wf : ∀ {n Γ ρ} (x : Fin n) → WF-Env Γ ρ →
            WF-Value (lookup x Γ) (lookup x ρ)
lookup-wf zero    (v-wf ∷ ρ-wf) = v-wf
lookup-wf (suc x) (v-wf ∷ ρ-wf) = lookup-wf x ρ-wf

-- If we can prove WF-DV σ x, then x does not "go wrong".

does-not-go-wrong : ∀ {σ x} → WF-DV σ x → ¬ now nothing ≈∈ x
does-not-go-wrong (return v-wf) ()
does-not-go-wrong (x-wf ∣ y-wf) (∣ˡ x↯)     = does-not-go-wrong x-wf x↯
does-not-go-wrong (x-wf ∣ y-wf) (∣ʳ y↯)     = does-not-go-wrong y-wf y↯
does-not-go-wrong (later x-wf)  (laterʳ x↯) =
  does-not-go-wrong (♭ x-wf) x↯

-- A variant of WF-DV, used to please the productivity checker.

infix  3 _⟨_⟩P
infixr 2 _≅⟨_⟩P_

data WF-DVP (σ : Ty) : D Value → Set where
  return      : ∀ {v} (v-wf : WF-Value σ v) → WF-DVP σ (return v)
  _∣_         : ∀ {x y} (x-wf : WF-DVP σ x) (y-wf : WF-DVP σ y) →
                WF-DVP σ (x ∣ y)
  later       : ∀ {x} (x-wf : ∞ (WF-DVP σ (♭ x))) → WF-DVP σ (later x)
  _>>=-congP_ : ∀ {τ x f}
                (x-wf : WF-DVP τ x)
                (f-wf : ∀ {v} → WF-Value τ v → WF-DVP σ (f v)) →
                WF-DVP σ (x >>= f)
  _≅⟨_⟩P_     : ∀ x {y} (x≅y : x ≅ y) (y-wf : WF-DVP σ y) → WF-DVP σ x
  _⟨_⟩P       : ∀ x (x-wf : WF-DVP σ x) → WF-DVP σ x

-- WF-DVP is sound with respect to WF-DV.

private

  -- WHNFs.

  data WF-DVW (σ : Ty) : D Value → Set where
    return : ∀ {v} (v-wf : WF-Value σ v) → WF-DVW σ (return v)
    _∣_    : ∀ {x y} (x-wf : WF-DVW σ x) (y-wf : WF-DVW σ y) →
             WF-DVW σ (x ∣ y)
    later  : ∀ {x} (x-wf : WF-DVP σ (♭ x)) → WF-DVW σ (later x)

  -- Functions which turn programs into WHNFs.

  trans-≅ : ∀ {σ x y} → x ≅ y → WF-DVW σ y → WF-DVW σ x
  trans-≅ fail            ()
  trans-≅ return          (return v-wf)   = return v-wf
  trans-≅ (x₁≅y₁ ∣ x₂≅y₂) (y₁-wf ∣ y₂-wf) = trans-≅ x₁≅y₁ y₁-wf
                                          ∣ trans-≅ x₂≅y₂ y₂-wf
  trans-≅ (later x≅y)     (later y-wf)    = later (_ ≅⟨ ♭ x≅y ⟩P y-wf)

  mutual

    _>>=-congW_ : ∀ {σ τ x f} →
                  WF-DVW σ x →
                  (∀ {v} → WF-Value σ v → WF-DVP τ (f v)) →
                  WF-DVW τ (x >>= f)
    return v-wf   >>=-congW f-wf = whnf (f-wf v-wf)
    (x-wf ∣ y-wf) >>=-congW f-wf = (x-wf >>=-congW f-wf)
                                 ∣ (y-wf >>=-congW f-wf)
    later x-wf    >>=-congW f-wf = later (x-wf >>=-congP f-wf)

    whnf : ∀ {σ x} → WF-DVP σ x → WF-DVW σ x
    whnf (return v-wf)         = return v-wf
    whnf (x-wf ∣ y-wf)         = whnf x-wf ∣ whnf y-wf
    whnf (later x-wf)          = later (♭ x-wf)
    whnf (x-wf >>=-congP f-wf) = whnf x-wf >>=-congW f-wf
    whnf (_ ≅⟨ x≅y ⟩P y-wf)    = trans-≅ x≅y (whnf y-wf)
    whnf (_ ⟨ x-wf ⟩P)         = whnf x-wf

sound : ∀ {σ x} → WF-DVP σ x → WF-DV σ x
sound = λ p → soundW (whnf p)
  where
  soundW : ∀ {σ x} → WF-DVW σ x → WF-DV σ x
  soundW (return v-wf) = return v-wf
  soundW (x-wf ∣ y-wf) = soundW x-wf ∣ soundW y-wf
  soundW (later x-wf)  = later (♯ sound x-wf)

-- Well-typed programs do not "go wrong".

mutual

  ⟦⟧-wf : ∀ {n Γ} (t : Tm n) {σ} → Γ ⊢ t ∈ σ →
          ∀ {ρ} → WF-Env Γ ρ → WF-DVP σ (⟦ t ⟧ ρ)
  ⟦⟧-wf (con i)   con             ρ-wf = return con
  ⟦⟧-wf (var x)   var             ρ-wf = return (lookup-wf x ρ-wf)
  ⟦⟧-wf (ƛ t)     (ƛ t∈)          ρ-wf = return (ƛ t∈ ρ-wf)
  ⟦⟧-wf (t₁ ∣ t₂) (t₁∈ ∣ t₂∈)     ρ-wf = ⟦⟧-wf t₁ t₁∈ ρ-wf
                                       ∣ ⟦⟧-wf t₂ t₂∈ ρ-wf
  ⟦⟧-wf (t₁ · t₂) (t₁∈ · t₂∈) {ρ} ρ-wf =
    ⟦ t₁ · t₂ ⟧ ρ          ≅⟨ ·-comp t₁ t₂ ⟩P
    ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ   ⟨ (⟦⟧-wf t₁ t₁∈ ρ-wf >>=-congP λ f-wf →
                               ⟦⟧-wf t₂ t₂∈ ρ-wf >>=-congP λ v-wf →
                               ∙-wf f-wf v-wf) ⟩P

  ∙-wf : ∀ {σ τ f v} →
         WF-Value (σ ⇾ τ) f → WF-Value (♭ σ) v →
         WF-DVP (♭ τ) ⟪ f ∙ v ⟫P
  ∙-wf (ƛ t₁∈ ρ₁-wf) v₂-wf = later (♯ ⟦⟧-wf _ t₁∈ (v₂-wf ∷ ρ₁-wf))

type-soundness : ∀ {t : Tm 0} {σ} →
                 [] ⊢ t ∈ σ → ¬ now nothing ≈∈ ⟦ t ⟧ []
type-soundness t∈ = does-not-go-wrong (sound (⟦⟧-wf _ t∈ []))
