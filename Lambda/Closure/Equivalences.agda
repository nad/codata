------------------------------------------------------------------------
-- A very brief treatment of different kinds of term equivalences,
-- including contextual equivalence and applicative bisimilarity
------------------------------------------------------------------------

module Lambda.Closure.Equivalences where

open import Codata.Musical.Notation
open import Data.Fin using (Fin; zero)
open import Data.Maybe hiding (_>>=_)
open import Data.Maybe.Relation.Binary.Pointwise as Maybe
  using (just; nothing)
open import Data.Nat
open import Data.Product as Prod
open import Data.Unit
open import Data.Vec using ([]; _∷_)
open import Effect.Monad.Partiality as Partiality
  using (_⊥; later⁻¹; laterˡ⁻¹; laterʳ⁻¹)
open import Function.Base
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open Partiality._⊥
private
  open module EP {A : Set} = Partiality.Equality (_≡_ {A = A})
  open module RP {A : Set} =
    Partiality.Reasoning (P.isEquivalence {A = A})

  open module RC {A : Set} =
    Partiality.Reasoning {_∼_ = λ (_ _ : A) → ⊤} _
      using () renaming (_≈⟨_⟩_ to _≈○⟨_⟩_; _∎ to _∎○)

open import Lambda.Closure.Functional
open PF using (return; _>>=_; fail)
open import Lambda.Syntax
open Closure Tm

------------------------------------------------------------------------
-- Two equivalent notions of equivalence of partial values

-- _≈○_ is a notion of weak bisimilarity which identifies all values.

open module EC {A : Set} = Partiality.Equality (λ (_ _ : A) → ⊤)
  using () renaming (_≈_ to _≈○_)

-- _≈○_ is equivalent to "terminates iff terminates".

≈○⇔⇓≈⇓ : {A : Set} {x y : A ⊥} → x ≈○ y ⇔ (x ⇓ ⇔ y ⇓)
≈○⇔⇓≈⇓ {A} = equivalence
  (λ x≈y → equivalence (h₁ x≈y) (h₁ (RC.sym x≈y)))
  (h₂ _ _)
  where
  h₁ : {x y : A ⊥} → x ≈○ y → x ⇓ → y ⇓
  h₁ (EC.now _)      (v , now P.refl) = -, now P.refl
  h₁ (EC.later  x≈y) (v , laterˡ x⇓v) = Prod.map id laterˡ $ h₁ (♭ x≈y) (v , x⇓v)
  h₁ (EC.laterʳ x≈y) (v , x⇓v)        = Prod.map id laterˡ $ h₁    x≈y  (v , x⇓v)
  h₁ (EC.laterˡ x≈y) (v , laterˡ x⇓v) =                      h₁    x≈y  (v , x⇓v)

  h₂ : (x y : A ⊥) → x ⇓ ⇔ y ⇓ → x ≈○ y
  h₂ (now v) y x⇓⇔y⇓ =
    now v  ≈○⟨ EC.now _ ⟩
    now _  ≈○⟨ Partiality.map _ (sym $ proj₂ $ Equivalence.to   x⇓⇔y⇓ ⟨$⟩ (-, now P.refl)) ⟩
    y      ∎○

  h₂ x (now v) x⇓⇔y⇓ =
    x      ≈○⟨ Partiality.map _ (      proj₂ $ Equivalence.from x⇓⇔y⇓ ⟨$⟩ (-, now P.refl)) ⟩
    now _  ≈○⟨ EC.now _ ⟩
    now v  ∎○

  h₂ (later x) (later y) x⇓⇔y⇓ = EC.later (♯
    h₂ (♭ x) (♭ y)
       (equivalence (lemma (_⟨$⟩_ (Equivalence.to   x⇓⇔y⇓)))
                    (lemma (_⟨$⟩_ (Equivalence.from x⇓⇔y⇓)))))
    where
    lemma : {A : Set} {x y : ∞ (A ⊥)} →
            (later x ⇓ → later y ⇓) → (♭ x ⇓ → ♭ y ⇓)
    lemma hyp (v , x⇓) = Prod.map id laterˡ⁻¹ $ hyp (v , laterˡ x⇓)

------------------------------------------------------------------------
-- Two equivalent definitions of contextual equivalence

-- Context m n consists of contexts with zero or more holes. The holes
-- expect terms of type Tm m, and if we fill those holes we get a term
-- of type Tm n.

infixl 9 _·_

data Context (m : ℕ) : ℕ → Set where
  •   : Context m m
  con : ∀ {n} (i : ℕ) → Context m n
  var : ∀ {n} (x : Fin n) → Context m n
  ƛ   : ∀ {n} (C : Context m (suc n)) → Context m n
  _·_ : ∀ {n} (C₁ C₂ : Context m n) → Context m n

-- Fills all the holes.

infix 10 _[_]

_[_] : ∀ {m n} → Context m n → Tm m → Tm n
•         [ t ] = t
con i     [ t ] = con i
var x     [ t ] = var x
ƛ C       [ t ] = ƛ (C [ t ])
(C₁ · C₂) [ t ] = C₁ [ t ] · C₂ [ t ]

-- Contextual equivalence.
--
-- Termination is the only observation. This is perhaps a bit strange:
-- there is no way to observe the difference between con i and con j
-- for i ≢ j.

infix 4 _≈C_

_≈C_ : ∀ {n} → Tm n → Tm n → Set
t₁ ≈C t₂ = ∀ C → ⟦ C [ t₁ ] ⟧ [] ≈○ ⟦ C [ t₂ ] ⟧ []

-- Alternative definition of contextual equivalence.

infix 4 _≈C′_

_≈C′_ : ∀ {n} → Tm n → Tm n → Set
t₁ ≈C′ t₂ = ∀ C → ⟦ C [ t₁ ] ⟧ [] ⇓ ⇔ ⟦ C [ t₂ ] ⟧ [] ⇓

-- These definitions are equivalent.

≈C⇔≈C′ : ∀ {n} {t₁ t₂ : Tm n} → t₁ ≈C t₂ ⇔ t₁ ≈C′ t₂
≈C⇔≈C′ = equivalence
  (λ t₁≈t₂ C → Equivalence.to   ≈○⇔⇓≈⇓ ⟨$⟩ t₁≈t₂ C)
  (λ t₁≈t₂ C → Equivalence.from ≈○⇔⇓≈⇓ ⟨$⟩ t₁≈t₂ C)

------------------------------------------------------------------------
-- A very strict term equivalence

-- A term equivalence defined directly on top of the semantics.

infix 4 _≈!_

_≈!_ : ∀ {n} → Tm n → Tm n → Set
t₁ ≈! t₂ = ∀ ρ → ⟦ t₁ ⟧ ρ ≈ ⟦ t₂ ⟧ ρ

-- This equivalence is not compatible.
--
-- Note that the proof does not use constants (con).

¬-compatible : ¬ ((t₁ t₂ : Tm 1) → t₁ ≈! t₂ → ƛ t₁ ≈! ƛ t₂)
¬-compatible ƛ-cong with
  ƛ-cong (ƛ (vr 1) · ƛ (ƛ (vr 0))) (ƛ (vr 1) · ƛ (vr 0))
         (λ _ → later (♯ now P.refl))
         []
... | now ()

------------------------------------------------------------------------
-- Incorrect definition of applicative bisimilarity

-- The difference between this definition and the one below is that in
-- this definition ƛ is inductive rather than coinductive.

module Incorrect where

  infix 4 _≈mv_ _≈v_

  -- _≈mv_, _≈c_ and _≈v_ are defined mutually (coinductively).

  data _≈v_ : Value → Value → Set

  -- Equivalence of possibly exceptional values.

  _≈mv_ : Maybe Value → Maybe Value → Set
  _≈mv_ = Maybe.Pointwise _≈v_

  -- Equivalence of computations.

  open module EA = Partiality.Equality _≈mv_
    using () renaming (_≈_ to _≈c_)

  -- Equivalence of values.

  data _≈v_ where
    con : ∀ {i} → con i ≈v con i
    ƛ   : ∀ {n₁} {t₁ : Tm (1 + n₁)} {ρ₁} {n₂} {t₂ : Tm (1 + n₂)} {ρ₂}
          (t₁≈t₂ : ∀ v → ⟦ t₁ ⟧ (v ∷ ρ₁) ≈c ⟦ t₂ ⟧ (v ∷ ρ₂)) →
          ƛ t₁ ρ₁ ≈v ƛ t₂ ρ₂

  -- Applicative bisimilarity.

  infix 4 _≈t_

  _≈t_ : ∀ {n} → Tm n → Tm n → Set
  t₁ ≈t t₂ = ∀ ρ → ⟦ t₁ ⟧ ρ ≈c ⟦ t₂ ⟧ ρ

  -- This notion of applicative bisimilarity is not reflexive.
  --
  -- Note that the definition above is a bit strange in Agda: it is
  -- subject to the quantifier inversion described by Thorsten
  -- Altenkirch and myself in "Termination Checking in the Presence of
  -- Nested Inductive and Coinductive Types". However, for this proof
  -- it does not matter if _≈c_ is seen as having the form
  -- μX.νY.μZ. F X Y Z or νX.μY. F X Y; the ν part is never used.

  mutual

    distinct-c : ¬ now (just (ƛ (var zero) [])) ≈c
                   now (just (ƛ (var zero) []))
    distinct-c (now eq) = distinct-mv eq

    distinct-mv : ¬ just (ƛ (var zero) []) ≈mv
                    just (ƛ (var zero) [])
    distinct-mv (just eq) = distinct-v eq

    distinct-v : ¬ ƛ (var zero) [] ≈v ƛ (var zero) []
    distinct-v (ƛ eq) = distinct-c (eq (ƛ (var zero) []))

  distinct-t : ¬ ƛ (var zero) ≈t (Tm 0 ∋ ƛ (var zero))
  distinct-t eq = distinct-c (eq [])

------------------------------------------------------------------------
-- Applicative bisimilarity

infix 4 _≈mv_ _≈v_

-- _≈mv_, _≈c_ and _≈v_ are defined mutually (coinductively).

data _≈v_ : Value → Value → Set

-- Equivalence of possibly exceptional values.

_≈mv_ : Maybe Value → Maybe Value → Set
_≈mv_ = Maybe.Pointwise _≈v_

-- Equivalence of computations.

open module EA = Partiality.Equality _≈mv_
  using () renaming (_≈_ to _≈c_)

-- Equivalence of values.

data _≈v_ where
  con : ∀ {i} → con i ≈v con i
  ƛ   : ∀ {n₁} {t₁ : Tm (1 + n₁)} {ρ₁} {n₂} {t₂ : Tm (1 + n₂)} {ρ₂}
        (t₁≈t₂ : ∀ v → ∞ (⟦ t₁ ⟧ (v ∷ ρ₁) ≈c ⟦ t₂ ⟧ (v ∷ ρ₂))) →
        ƛ t₁ ρ₁ ≈v ƛ t₂ ρ₂

-- Applicative bisimilarity.

infix 4 _≈t_

_≈t_ : ∀ {n} → Tm n → Tm n → Set
t₁ ≈t t₂ = ∀ ρ → ⟦ t₁ ⟧ ρ ≈c ⟦ t₂ ⟧ ρ

-- Applicative bisimilarity is reflexive.

mutual

  infix 3 _∎mv _∎c _∎v

  _∎mv : (v : Maybe Value) → v ≈mv v
  just v  ∎mv = just (v ∎v)
  nothing ∎mv = nothing

  _∎c : (x : Maybe Value ⊥) → x ≈c x
  now mv  ∎c = EA.now (mv ∎mv)
  later x ∎c = EA.later (♯ (♭ x ∎c))

  _∎v : (v : Value) → v ≈v v
  con i ∎v = con
  ƛ t ρ ∎v = ƛ (λ v → ♯ (⟦ t ⟧ (v ∷ ρ) ∎c))

infix 3 _∎t

_∎t : ∀ {n} (t : Tm n) → t ≈t t
t ∎t = λ ρ → ⟦ t ⟧ ρ ∎c

-- Applicative bisimilarity is symmetric.

mutual

  sym-mv : ∀ {v₁ v₂} → v₁ ≈mv v₂ → v₂ ≈mv v₁
  sym-mv (just v₁≈v₂) = just (sym-v v₁≈v₂)
  sym-mv nothing      = nothing

  sym-c : ∀ {x₁ x₂} → x₁ ≈c x₂ → x₂ ≈c x₁
  sym-c (EA.now v₁≈v₂)    = EA.now (sym-mv v₁≈v₂)
  sym-c (EA.later  x₁≈x₂) = EA.later (♯ sym-c (♭ x₁≈x₂))
  sym-c (EA.laterˡ x₁≈x₂) = EA.laterʳ  (sym-c    x₁≈x₂)
  sym-c (EA.laterʳ x₁≈x₂) = EA.laterˡ  (sym-c    x₁≈x₂)

  sym-v : ∀ {v₁ v₂} → v₁ ≈v v₂ → v₂ ≈v v₁
  sym-v con       = con
  sym-v (ƛ t₁≈t₂) = ƛ (λ v → ♯ sym-c (♭ (t₁≈t₂ v)))

sym-t : ∀ {n} {t₁ t₂ : Tm n} → t₁ ≈t t₂ → t₂ ≈t t₁
sym-t t₁≈t₂ = λ ρ → sym-c (t₁≈t₂ ρ)

-- Applicative bisimilarity is transitive.

mutual

  trans-mv : ∀ {v₁ v₂ v₃} → v₁ ≈mv v₂ → v₂ ≈mv v₃ → v₁ ≈mv v₃
  trans-mv (just v₁≈v₂) (just v₂≈v₃) = just (trans-v v₁≈v₂ v₂≈v₃)
  trans-mv nothing      nothing      = nothing

  private

    now-trans-c : ∀ {x₁ x₂ v₃} → x₁ ≈c x₂ → x₂ ≈c now v₃ → x₁ ≈c now v₃
    now-trans-c (EA.now    v₁≈v₂) (EA.now    v₂≈v₃) = EA.now (trans-mv       v₁≈v₂   v₂≈v₃)
    now-trans-c (EA.laterˡ x₁≈x₂)            x₂≈v₃  = EA.laterˡ (now-trans-c x₁≈x₂   x₂≈v₃)
    now-trans-c            x₁≈lx₂ (EA.laterˡ x₂≈v₃) = now-trans-c (laterʳ⁻¹  x₁≈lx₂) x₂≈v₃

    later-trans-c : ∀ {x₁ x₂ x₃} →
                    x₁ ≈c x₂ → x₂ ≈c later x₃ → x₁ ≈c later x₃
    later-trans-c (EA.later  x₁≈x₂)        lx₂≈lx₃ = EA.later  (♯ trans-c (♭ x₁≈x₂) (later⁻¹  lx₂≈lx₃))
    later-trans-c (EA.laterˡ x₁≈x₂)         x₂≈lx₃ = EA.later  (♯ trans-c    x₁≈x₂  (laterʳ⁻¹  x₂≈lx₃))
    later-trans-c (EA.laterʳ x₁≈x₂)        lx₂≈lx₃ =        later-trans-c    x₁≈x₂  (laterˡ⁻¹ lx₂≈lx₃)
    later-trans-c         x₁≈x₂  (EA.laterʳ x₂≈x₃) = EA.laterʳ (  trans-c    x₁≈x₂             x₂≈x₃ )

  trans-c : ∀ {x₁ x₂ x₃} → x₁ ≈c x₂ → x₂ ≈c x₃ → x₁ ≈c x₃
  trans-c {x₃ = now   v₃} x₁≈x₂ x₂≈v₃  = now-trans-c   x₁≈x₂ x₂≈v₃
  trans-c {x₃ = later z₃} x₁≈x₂ x₂≈lx₃ = later-trans-c x₁≈x₂ x₂≈lx₃

  trans-v : ∀ {v₁ v₂ v₃} → v₁ ≈v v₂ → v₂ ≈v v₃ → v₁ ≈v v₃
  trans-v con       con       = con
  trans-v (ƛ t₁≈t₂) (ƛ t₂≈t₃) =
    ƛ (λ v → ♯ trans-c (♭ (t₁≈t₂ v)) (♭ (t₂≈t₃ v)))

trans-t : ∀ {n} {t₁ t₂ t₃ : Tm n} → t₁ ≈t t₂ → t₂ ≈t t₃ → t₁ ≈t t₃
trans-t t₁≈t₂ t₂≈t₃ = λ ρ → trans-c (t₁≈t₂ ρ) (t₂≈t₃ ρ)

-- Bind preserves applicative bisimilarity.

infixl 1 _>>=-cong-c_

_>>=-cong-c_ : ∀ {x₁ x₂ f₁ f₂} →
               x₁ ≈c x₂ → (∀ {v₁ v₂} → v₁ ≈v v₂ → f₁ v₁ ≈c f₂ v₂) →
               (x₁ >>= f₁) ≈c (x₂ >>= f₂)
_>>=-cong-c_ {f₁ = f₁} {f₂} x₁≈x₂ f₁≈f₂ =
  Partiality._>>=-cong_ x₁≈x₂ helper
  where
  helper : ∀ {mv₁ mv₂} → mv₁ ≈mv mv₂ →
           maybe f₁ fail mv₁ ≈c maybe f₂ fail mv₂
  helper nothing      = EA.now nothing
  helper (just v₁≈v₂) = f₁≈f₂ v₁≈v₂

-- _≈!_ is stronger than applicative bisimilarity.

≈!⇒≈t : ∀ {n} {t₁ t₂ : Tm n} → t₁ ≈! t₂ → t₁ ≈t t₂
≈!⇒≈t t₁≈t₂ = λ ρ →
  Partiality.map (λ {v₁} v₁≡v₂ → P.subst (_≈mv_ v₁) v₁≡v₂ (v₁ ∎mv))
                 (t₁≈t₂ ρ)

¬≈t⇒≈! : ¬ ((t₁ t₂ : Tm 0) → t₁ ≈t t₂ → t₁ ≈! t₂)
¬≈t⇒≈! hyp with hyp t₁ t₂ bisimilar []
  where
  t₁ : Tm 0
  t₁ = ƛ (ƛ (vr 0)) · con 0

  t₂ : Tm 0
  t₂ = ƛ (vr 0)

  bisimilar : t₁ ≈t t₂
  bisimilar [] =
    EA.laterˡ (EA.now (just (ƛ (λ v → ♯ (return v ∎c)))))
... | laterˡ (now ())
