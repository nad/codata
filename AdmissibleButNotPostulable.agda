------------------------------------------------------------------------
-- Admissible rules are sometimes not "postulable"
------------------------------------------------------------------------

-- Even though a rule is admissible it may not be sound to postulate
-- it, i.e. add it as an inductive constructor. This was observed by
-- Edsko de Vries in a message to the Coq-club mailing list (Re:
-- [Coq-Club] Adding (inductive) transitivity to weak bisimilarity not
-- sound? (was: Need help with coinductive proof), 2009-08-28).

module AdmissibleButNotPostulable where

open import Codata.Musical.Notation using (∞; ♯_; ♭)
open import Data.Nat
open import Data.Product as Prod
open import Function
open import Relation.Binary.PropositionalEquality as P using (_≡_; [_])
open import Relation.Nullary using (¬_)

------------------------------------------------------------------------
-- The partiality monad

data _⊥ (A : Set) : Set where
  now   : (v : A) → A ⊥
  later : (x : ∞ (A ⊥)) → A ⊥

------------------------------------------------------------------------
-- Weak equality of computations in the partiality monad

module WeakEquality where

  infix 4 _≈_

  data _≈_ {A : Set} : A ⊥ → A ⊥ → Set where
    now    : ∀ {v}                         → now   v ≈ now   v
    later  : ∀ {x y} (x≈y : ∞ (♭ x ≈ ♭ y)) → later x ≈ later y
    laterʳ : ∀ {x y} (x≈y :      x ≈ ♭ y ) →       x ≈ later y
    laterˡ : ∀ {x y} (x≈y :    ♭ x ≈   y ) → later x ≈       y

  -- Some lemmas.

  laterʳ⁻¹ : ∀ {A : Set} {x : A ⊥} {y} → x ≈ later y → x ≈ ♭ y
  laterʳ⁻¹ (later  x≈y)  = laterˡ        (♭ x≈y)
  laterʳ⁻¹ (laterʳ x≈y)  = x≈y
  laterʳ⁻¹ (laterˡ x≈ly) = laterˡ (laterʳ⁻¹ x≈ly)

  laterˡ⁻¹ : ∀ {A : Set} {x} {y : A ⊥} → later x ≈ y → ♭ x ≈ y
  laterˡ⁻¹ (later  x≈y)  = laterʳ         (♭ x≈y)
  laterˡ⁻¹ (laterʳ lx≈y) = laterʳ (laterˡ⁻¹ lx≈y)
  laterˡ⁻¹ (laterˡ x≈y)  = x≈y

  -- Weak equality is an equivalence relation.

  refl : {A : Set} (x : A ⊥) → x ≈ x
  refl (now v)   = now
  refl (later x) = later (♯ refl (♭ x))

  sym : {A : Set} {x y : A ⊥} → x ≈ y → y ≈ x
  sym now          = now
  sym (later  x≈y) = later (♯ sym (♭ x≈y))
  sym (laterʳ x≈y) = laterˡ (sym x≈y)
  sym (laterˡ x≈y) = laterʳ (sym x≈y)

  trans : {A : Set} {x y z : A ⊥} → x ≈ y → y ≈ z → x ≈ z
  trans {x = now v} {z = z} p q = tr p q
    where
    tr : ∀ {y} → now v ≈ y → y ≈ z → now v ≈ z
    tr now          y≈z  = y≈z
    tr (laterʳ v≈y) ly≈z = tr v≈y (laterˡ⁻¹ ly≈z)
  trans {x = later x} lx≈y y≈z = tr lx≈y y≈z
    where
    tr : ∀ {y z} → later x ≈ y → y ≈ z → later x ≈ z
    tr         lx≈ly (later  y≈z) = later  (♯ trans (laterˡ⁻¹ lx≈ly) (laterˡ (♭ y≈z)))
    tr         lx≈y  (laterʳ y≈z) = later  (♯ trans (laterˡ⁻¹ lx≈y)             y≈z  )
    tr         lx≈ly (laterˡ y≈z) =           tr    (laterʳ⁻¹ lx≈ly)            y≈z
    tr (laterˡ  x≈y)         y≈z  = laterˡ (  trans            x≈y              y≈z  )

  -- Non-termination.

  never : {A : Set} → A ⊥
  never = later (♯ never)

  -- Weak equality is not trivial (assuming that the argument to _⊥ is
  -- non-empty).

  non-trivial : {A : Set} {v : A} → ¬ now v ≈ never
  non-trivial (laterʳ v≈⊥) = non-trivial v≈⊥

------------------------------------------------------------------------
-- Extended weak equality

module ExtendedWeakEquality where

  infix  4 _≈_
  infix  3 _∎
  infixr 2 _≈⟨_⟩_

  -- Let us try to postulate transitivity using an inductive rule.

  data _≈_ {A : Set} : A ⊥ → A ⊥ → Set where
    now    : ∀ {v}                         → now   v ≈ now   v
    later  : ∀ {x y} (x≈y : ∞ (♭ x ≈ ♭ y)) → later x ≈ later y
    laterʳ : ∀ {x y} (x≈y :      x ≈ ♭ y ) →       x ≈ later y
    laterˡ : ∀ {x y} (x≈y :    ♭ x ≈   y ) → later x ≈       y

    -- Transitivity.
    _≈⟨_⟩_ : ∀ x {y z} (x≈y : x ≈ y) (y≈z : y ≈ z) → x ≈ z

  -- Reflexivity.

  _∎ : {A : Set} (x : A ⊥) → x ≈ x
  now   v ∎ = now
  later x ∎ = later (♯ (♭ x ∎))

  -- Extended weak equality is trivial.

  trivial : {A : Set} (x y : A ⊥) → x ≈ y
  trivial x y =
    x           ≈⟨ laterʳ (x ∎)           ⟩
    later (♯ x) ≈⟨ later  (♯ trivial x y) ⟩
    later (♯ y) ≈⟨ laterˡ (y ∎)           ⟩
    y           ∎

  -- The problem is that there is no "contractive" proof of
  -- transitivity; the proof given above consumes the input
  -- certificate "faster" than it produces the output certificate.

------------------------------------------------------------------------
-- Capretta's definition of equality coincides with weak equality

-- This is not really related to the problem discussed above, I just
-- want to ensure that the definition of weak equality is not too
-- strange.

module Capretta'sEquality where

  infix 4 _⇓_ _≈_

  -- x ⇓ v means that x terminates with the value v.

  data _⇓_ {A : Set} : A ⊥ → A → Set where
    now   : ∀ {v} → now v ⇓ v
    later : ∀ {x v} (x⇓v : ♭ x ⇓ v) → later x ⇓ v

  -- Equality as defined by Capretta in "General Recursion via
  -- Coinductive Types".

  data _≈_ {A : Set} : A ⊥ → A ⊥ → Set where
    now   : ∀ {x y v} (x⇓v : x ⇓ v) (y⇓v : y ⇓ v) → x ≈ y
    later : ∀ {x y} (x≈y : ∞ (♭ x ≈ ♭ y)) → later x ≈ later y

  -- Soundness.

  open WeakEquality using () renaming (_≈_ to _≋_)

  sound : {A : Set} {x y : A ⊥} → x ≈ y → x ≋ y
  sound (later x≈y)   = WeakEquality.later (♯ sound (♭ x≈y))
  sound (now x⇓v y⇓v) = nw x⇓v y⇓v
    where
    nw : ∀ {A : Set} {x y : A ⊥} {v} → x ⇓ v → y ⇓ v → x ≋ y
    nw now         now         = WeakEquality.now
    nw x⇓v         (later y⇓v) = WeakEquality.laterʳ (nw x⇓v y⇓v)
    nw (later x⇓v) y⇓v         = WeakEquality.laterˡ (nw x⇓v y⇓v)

  -- Completeness.

  data _≈P_ {A : Set} : A ⊥ → A ⊥ → Set where
    now    : ∀ {x y v} (x⇓v : x ⇓ v) (y⇓v : y ⇓ v) → x ≈P y
    later  : ∀ {x y} (x≈y : ∞ (♭ x ≈P ♭ y)) → later x ≈P later y
    laterʳ : ∀ {x y} (x≈y :      x ≈P ♭ y ) →       x ≈P later y
    laterˡ : ∀ {x y} (x≈y :    ♭ x ≈P   y ) → later x ≈P       y

  data _≈W_ {A : Set} : A ⊥ → A ⊥ → Set where
    now   : ∀ {x y v} (x⇓v : x ⇓ v) (y⇓v : y ⇓ v) → x ≈W y
    later : ∀ {x y} (x≈y : ♭ x ≈P ♭ y) → later x ≈W later y

  laterʳW : ∀ {A : Set} {x : A ⊥} {y} → x ≈W ♭ y → x ≈W later y
  laterʳW {y = y} x≈y with ♭ y in eq
  laterʳW x≈y | y′ with x≈y
  laterʳW x≈y | y′ | now {v = v} x⇓v y⇓v =
    now x⇓v (later (P.subst (λ y → y ⇓ v) (P.sym eq) y⇓v))
  laterʳW x≈y | later y′ | later x′≈y′ =
    later (P.subst (_≈P_ _) (P.sym eq) (laterʳ x′≈y′))

  laterˡW : ∀ {A : Set} {x} {y : A ⊥} → ♭ x ≈W y → later x ≈W y
  laterˡW {x = x} x≈y with ♭ x in eq
  laterˡW x≈y | x′ with x≈y
  laterˡW x≈y | x′ | now {v = v} x⇓v y⇓v =
    now (later (P.subst (λ x → x ⇓ v) (P.sym eq) x⇓v)) y⇓v
  laterˡW x≈y | later x′ | later {y = y′} x′≈y′ =
    later (P.subst (λ x → x ≈P ♭ y′) (P.sym eq) (laterˡ x′≈y′))

  whnf : {A : Set} {x y : A ⊥} → x ≈P y → x ≈W y
  whnf (now x⇓v y⇓v) = now x⇓v y⇓v
  whnf (later  x≈y)  = later (♭ x≈y)
  whnf (laterʳ x≈y)  = laterʳW (whnf x≈y)
  whnf (laterˡ x≈y)  = laterˡW (whnf x≈y)

  mutual

    ⟦_⟧W : {A : Set} {x y : A ⊥} → x ≈W y → x ≈ y
    ⟦ now x⇓v y⇓v ⟧W = now x⇓v y⇓v
    ⟦ later x≈y   ⟧W = later (♯ ⟦ x≈y ⟧P)

    ⟦_⟧P : {A : Set} {x y : A ⊥} → x ≈P y → x ≈ y
    ⟦ x≈y ⟧P = ⟦ whnf x≈y ⟧W

  complete : {A : Set} {x y : A ⊥} → x ≋ y → x ≈ y
  complete x≋y = ⟦ completeP x≋y ⟧P
    where
    completeP : {A : Set} {x y : A ⊥} → x ≋ y → x ≈P y
    completeP WeakEquality.now          = now now now
    completeP (WeakEquality.later x≈y)  = later (♯ completeP (♭ x≈y))
    completeP (WeakEquality.laterʳ x≈y) = laterʳ (completeP x≈y)
    completeP (WeakEquality.laterˡ x≈y) = laterˡ (completeP x≈y)

------------------------------------------------------------------------
-- The weak equality above coincides with weak bisimilarity

module WeakBisimilarity {A : Set} where

  -- The function drop n drops n later constructors (if possible).

  drop : ℕ → A ⊥ → A ⊥
  drop zero    x         = x
  drop _       (now v)   = now v
  drop (suc n) (later x) = drop n (♭ x)

  -- Weak simulations and bisimulations. The removal of a later
  -- constructor is treated as a silent transition.

  record IsWeakSimulation (_R_ : A ⊥ → A ⊥ → Set) : Set where
    field
      match-later : ∀ {x y} → later x R y → ∃ λ n → ♭ x   R drop n y
      match-now   : ∀ {v y} → now v   R y → ∃ λ n → now v ≡ drop n y

  record IsWeakBisimulation (_R_ : A ⊥ → A ⊥ → Set) : Set where
    field
      left  : IsWeakSimulation _R_
      right : IsWeakSimulation (flip _R_)

  -- Weak bisimilarity.

  record _≈_ (x y : A ⊥) : Set₁ where
    field
      _R_   : A ⊥ → A ⊥ → Set
      xRy   : x R y
      bisim : IsWeakBisimulation _R_

  open WeakEquality hiding (module _≈_) renaming (_≈_ to _≋_)

  -- Completeness.

  complete : ∀ {x y} → x ≋ y → x ≈ y
  complete x≋y = record
    { _R_   = _≋_
    ; xRy   = x≋y
    ; bisim = record
      { left = record
        { match-later = λ lx≋y → (0 , laterˡ⁻¹ lx≋y)
        ; match-now   = match-now
        }
      ; right = record
        { match-later = λ x≋ly → (0 , laterʳ⁻¹ x≋ly)
        ; match-now   = match-now ∘ sym
        }
      }
    }
    where
    match-now : ∀ {v y} → now v ≋ y → ∃ λ n → now v ≡ drop n y
    match-now now          = (0 , P.refl)
    match-now (laterʳ v≋y) = Prod.map suc id (match-now v≋y)

  -- Soundness.

  module Sound {x y} (x≈y : x ≈ y) where

    open _≈_ x≈y
    open IsWeakBisimulation
    open IsWeakSimulation

    helper₁ : ∀ {x} y → (∃ λ n → now x ≡ drop n y) → now x ≋ y
    helper₁ (now y)   (zero  , P.refl) = now
    helper₁ (now y)   (suc n , P.refl) = now
    helper₁ (later y) (zero  , ())
    helper₁ (later y) (suc n , nx≡y-n) =
      laterʳ (helper₁ (♭ y) (n , nx≡y-n))

    mutual

      helper₂ : ∀ {x} y → (∃ λ n → x R drop n y) → x ≋ y
      helper₂ y         (zero  , xRy)   = sound _ _ xRy
      helper₂ (now y)   (suc n , xRny)  = sound _ _ xRny
      helper₂ (later y) (suc n , xRy-n) =
        laterʳ (helper₂ (♭ y) (n , xRy-n))

      helper₃ : ∀ x {y} → (∃ λ n → drop (suc n) x R y) → x ≋ y
      helper₃ (now x)   (n     , nxRy)  = sound _ _ nxRy
      helper₃ (later x) (zero  , xRy)   = laterˡ (sound _ _ xRy)
      helper₃ (later x) (suc n , x-nRy) =
        laterˡ (helper₃ (♭ x) (n , x-nRy))

      sound : ∀ x y → x R y → x ≋ y
      sound (now x) y nxRy = helper₁ y $ match-now (left bisim) nxRy
      sound (later x) (now y) lxRny =
        sym $ helper₁ (later x) $ match-now (right bisim) lxRny
      sound (later x) (later y) lxRly
        with match-later (left bisim) lxRly
      ... | (suc n , xRy-n) = later (♯ helper₂ (♭ y) (n , xRy-n))
      ... | (zero  , xRly)  with match-later (right bisim) xRly
      ...   | (zero  , xRy)     = later (♯ sound _ _ xRy)
      ...   | (suc n , x-1+nRy) =
        later (♯ helper₃ (♭ x) (n , x-1+nRy))

  sound : ∀ {x y} → x ≈ y → x ≋ y
  sound x≈y = Sound.sound x≈y _ _ (_≈_.xRy x≈y)

-- Note that the problem illustrated in ExtendedWeakEquality is
-- related to the problem of weak bisimulation up to weak
-- bisimilarity. Let R be a relation which is only inhabited for the
-- pair (later (♯ x), later (♯ y)). R is a weak bisimulation up to
-- weak bisimilarity (_≈_):
--
--   later (♯ x)         R later (♯ y)
--       ↓                     =
--       x ≈ later (♯ x) R later (♯ y)
--
--   later (♯ x) R           later (♯ y)
--       =                       ↓
--   later (♯ x) R later (♯ y) ≈ y
--
-- Weak bisimilarity is transitive, so if every relation which is a
-- weak bisimulation up to weak bisimilarity were contained in weak
-- bisimilarity we would have x ≈ y for all x and y.
