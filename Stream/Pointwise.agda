------------------------------------------------------------------------
-- Pointwise equalities can be lifted
------------------------------------------------------------------------

{-# OPTIONS --universe-polymorphism #-}

module Stream.Pointwise where

open import Coinduction hiding (∞; unfold)
open import Stream
open import Stream.Equality
import Stream.Programs as Prog
open Prog hiding (lift; ⟦_⟧)
open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec as Vec using (Vec; _∷_)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
private
  module IsEq {A : Set} =
    IsEquivalence (Setoid.isEquivalence (Stream.setoid A))

------------------------------------------------------------------------
-- Definitions

infix  8 _∞
infixr 7 _·_
infix  6 _⟨_⟩_

-- Expressions corresponding to pointwise definitions of streams.
-- Indexed on the number of variables.

-- It is possible to generalise this type, allowing variables to
-- correspond to streams containing elements of arbitrary type, and
-- letting the function arguments of _·_ and _⟨_⟩_ be more general.
-- However, this would complicate the development, so I hesitate to do
-- so without evidence that it would be genuinely useful.

data Pointwise A n : Set where
  var   : (x : Fin n) → Pointwise A n
  _∞    : (x : A) → Pointwise A n
  _·_   : (f : A → A) (xs : Pointwise A n) → Pointwise A n
  _⟨_⟩_ : (xs : Pointwise A n)
          (_∙_ : A → A → A)
          (ys : Pointwise A n) →
          Pointwise A n

-- Stream semantics.

⟦_⟧ : ∀ {A n} → Pointwise A n → (Vec (Prog A) n → Prog A)
⟦ var x ⟧         ρ = Vec.lookup x ρ
⟦ x ∞ ⟧           ρ = x ∞
⟦ f · xs ⟧        ρ = f · ⟦ xs ⟧ ρ
⟦ xs ⟨ _∙_ ⟩ ys ⟧ ρ = ⟦ xs ⟧ ρ ⟨ _∙_ ⟩ ⟦ ys ⟧ ρ

-- Pointwise semantics.

⟪_⟫ : ∀ {A n} → Pointwise A n → (Vec A n → A)
⟪ var x ⟫         ρ = Vec.lookup x ρ
⟪ x ∞ ⟫           ρ = x
⟪ f · xs ⟫        ρ = f (⟪ xs ⟫ ρ)
⟪ xs ⟨ _∙_ ⟩ ys ⟫ ρ = ⟪ xs ⟫ ρ ∙ ⟪ ys ⟫ ρ

------------------------------------------------------------------------
-- Some lemmas used below

private

  -- lookup is natural.

  lookup-nat : ∀ {a b n} {A : Set a} {B : Set b}
               (f : A → B) (x : Fin n) ρ →
               f (Vec.lookup x ρ) ≡ Vec.lookup x (Vec.map f ρ)
  lookup-nat f zero    (x ∷ ρ) = refl
  lookup-nat f (suc i) (x ∷ ρ) = lookup-nat f i ρ

------------------------------------------------------------------------
-- The two semantics above are related via the function lift

private

  -- Lifts a pointwise function to a function on stream programs.

  lift : ∀ {A B n} →
         (Vec A n → B) → Vec (Prog A) n → Prog B
  lift f xs = f (Vec.map headP xs) ≺ ♯ lift f (Vec.map tailP xs)

  -- lift is a congruence in its first argument.

  lift-cong : ∀ {A B n} {f g : Vec A n → B} →
              (∀ ρ → f ρ ≡ g ρ) →
              ∀ ρ → lift f ρ ≊ lift g ρ
  lift-cong hyp ρ = hyp (Vec.map headP ρ) ≺
                    ♯ lift-cong hyp (Vec.map tailP ρ)

  -- unfold xs ρ is the one-step unfolding of ⟦ xs ⟧ ρ. Note the
  -- similarity to lift.

  unfold : ∀ {A n} (xs : Pointwise A n) ρ → Prog A
  unfold xs ρ = ⟪ xs ⟫ (Vec.map headP ρ) ≺♯
                ⟦ xs ⟧ (Vec.map tailP ρ)

  unfold-lemma : ∀ {A n} (xs : Pointwise A n) ρ →
                 ⟦ xs ⟧ ρ ≊ unfold xs ρ
  unfold-lemma (var x) ρ =
    Vec.lookup x ρ
      ≊⟨ ≊-η (Vec.lookup x ρ) ⟩
    headP (Vec.lookup x ρ) ≺♯ tailP (Vec.lookup x ρ)
      ≊⟨ lookup-nat headP x ρ ≺
         ♯ ≈⇒≅ (IsEq.reflexive
                  (cong Prog.⟦_⟧ (lookup-nat tailP x ρ))) ⟩
    Vec.lookup x (Vec.map headP ρ) ≺♯
    Vec.lookup x (Vec.map tailP ρ)
      ≡⟨ refl ⟩
    unfold (var x) ρ
      ∎
  unfold-lemma (x ∞)    ρ = x ∞ ∎
  unfold-lemma (f · xs) ρ =
    f · ⟦ xs ⟧ ρ
      ≊⟨ ·-cong f (⟦ xs ⟧ ρ) (unfold xs ρ) (unfold-lemma xs ρ) ⟩
    f · unfold xs ρ
      ∎
  unfold-lemma (xs ⟨ ∙ ⟩ ys) ρ =
    ⟦ xs ⟧ ρ ⟨ ∙ ⟩ ⟦ ys ⟧ ρ
      ≊⟨ ⟨ ∙ ⟩-cong (⟦ xs ⟧ ρ) (unfold xs ρ) (unfold-lemma xs ρ)
                    (⟦ ys ⟧ ρ) (unfold ys ρ) (unfold-lemma ys ρ) ⟩
    unfold xs ρ ⟨ ∙ ⟩ unfold ys ρ
      ∎

  -- The two semantics are related.

  main-lemma : ∀ {A n} (xs : Pointwise A n) →
               ∀ ρ → ⟦ xs ⟧ ρ ≊ lift ⟪ xs ⟫ ρ
  main-lemma xs ρ =
    ⟦ xs ⟧ ρ
      ≊⟨ unfold-lemma xs ρ ⟩
    unfold xs ρ
      ≡⟨ refl ⟩
    ⟪ xs ⟫ (Vec.map headP ρ) ≺♯ ⟦ xs ⟧ (Vec.map tailP ρ)
      ≊⟨ refl ≺ ♯ main-lemma xs (Vec.map tailP ρ) ⟩
    lift ⟪ xs ⟫ ρ
      ∎

------------------------------------------------------------------------
-- To prove that two streams which are defined pointwise are equal, it
-- is enough to reason about a single (arbitrary) point

-- This function is a bit awkward to use, since the user has to come
-- up with a suitable environment manually. The alternative function
-- pointwise below may be slightly easier to use.

pointwise' : ∀ {A n} (xs ys : Pointwise A n) →
             (∀ ρ → ⟪ xs ⟫ ρ ≡ ⟪ ys ⟫ ρ) →
             (∀ ρ → ⟦ xs ⟧ ρ ≊ ⟦ ys ⟧ ρ)
pointwise' xs ys hyp ρ =
  ⟦ xs ⟧ ρ
    ≊⟨ main-lemma xs ρ ⟩
  lift ⟪ xs ⟫ ρ
    ≊⟨ lift-cong hyp ρ ⟩
  lift ⟪ ys ⟫ ρ
    ≊⟨ ≅-sym (main-lemma ys ρ) ⟩
  ⟦ ys ⟧ ρ
    ∎

open import Data.Vec.N-ary

-- Applies the function to all possible variables.

app : ∀ {A} n →
      N-ary n (Pointwise A n) (Pointwise A n) → Pointwise A n
app n f = f $ⁿ Vec.map var (Vec.allFin n)

-- The type signature of this function may be a bit daunting, but once
-- n, f and g are instantiated with well-behaved concrete values the
-- remaining type evaluates nicely.

pointwise
  : ∀ {A} n (f g : N-ary n (Pointwise A n) (Pointwise A n)) →
    Eq n _≡_ (curryⁿ ⟪ app n f ⟫) (curryⁿ ⟪ app n g ⟫) →
    Eq n _≊_ (curryⁿ ⟦ app n f ⟧) (curryⁿ ⟦ app n g ⟧)
pointwise n f g hyp =
  curryⁿ-cong _≊_ ⟦ app n f ⟧ ⟦ app n g ⟧
    (pointwise' (app n f) (app n g)
      (curryⁿ-cong⁻¹ _≡_ ⟪ app n f ⟫ ⟪ app n g ⟫ hyp))

------------------------------------------------------------------------
-- Some examples

private

  example₁ : suc · 0 ∞ ≊ 1 ∞
  example₁ = pointwise 0 (suc · 0 ∞) (1 ∞) refl

  example₂ : ∀ s → suc · s ≊ 1 ∞ ⟨ _+_ ⟩ s
  example₂ = pointwise 1 (λ s → suc · s)
                         (λ s → 1 ∞ ⟨ _+_ ⟩ s)
                         (λ _ → refl)

  example₃ : ∀ s t u →
             (s ⟨ _+_ ⟩ t) ⟨ _+_ ⟩ u ≊ s ⟨ _+_ ⟩ (t ⟨ _+_ ⟩ u)
  example₃ = pointwise 3 (λ s t u → (s ⟨ _+_ ⟩ t) ⟨ _+_ ⟩ u)
                         (λ s t u →  s ⟨ _+_ ⟩ (t ⟨ _+_ ⟩ u))
                         +-assoc
    where
    open import Data.Nat.Properties
    open import Algebra.Structures
    open IsCommutativeSemiring isCommutativeSemiring
