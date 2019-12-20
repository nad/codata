------------------------------------------------------------------------
-- A universe for stream programs
------------------------------------------------------------------------

module Stream.Programs where

open import Codata.Musical.Notation renaming (∞ to ∞_)
import Stream as S
open S using (Stream; _≈_; _≺_; head; tail)
open import Relation.Binary.PropositionalEquality
open import Data.Vec using (Vec; []; _∷_)

------------------------------------------------------------------------
-- Stream programs

infix  8 _∞
infixr 7 _·_
infix  6 _⟨_⟩_
infixr 5 _≺_ _⋎_ _≺≺_

data Prog (A : Set) : Set1 where
  _≺_     : (x : A) (xs : ∞ (Prog A)) → Prog A
  _∞      : (x : A) → Prog A
  _·_     : ∀ {B} (f : B → A) (xs : Prog B) → Prog A
  _⟨_⟩_   : ∀ {B C} (xs : Prog B) (_∙_ : B → C → A) (ys : Prog C) →
            Prog A
  _⋎_     : (xs ys : Prog A) → Prog A
  iterate : (f : A → A) (x : A) → Prog A
  _≺≺_    : ∀ {n} (xs : Vec A n) (ys : Prog A) → Prog A

data WHNF A : Set1 where
  _≺_ : (x : A) (xs : Prog A) → WHNF A

------------------------------------------------------------------------
-- Conversion

whnf : ∀ {A} → Prog A → WHNF A
whnf (x ≺ xs)         = x ≺ ♭ xs
whnf (x ∞)            = x ≺ x ∞
whnf (f · xs)         with whnf xs
whnf (f · xs)         | x ≺ xs′ = f x ≺ f · xs′
whnf (xs ⟨ _∙_ ⟩ ys)  with whnf xs | whnf ys
whnf (xs ⟨ _∙_ ⟩ ys)  | x ≺ xs′ | y ≺ ys′ = (x ∙ y) ≺ xs′ ⟨ _∙_ ⟩ ys′
whnf (xs ⋎ ys)        with whnf xs
whnf (xs ⋎ ys)        | x ≺ xs′ = x ≺ ys ⋎ xs′
whnf (iterate f x)    = x ≺ iterate f (f x)
whnf ([]       ≺≺ ys) = whnf ys
whnf ((x ∷ xs) ≺≺ ys) = x ≺ xs ≺≺ ys

mutual

  value : ∀ {A} → WHNF A → Stream A
  value (x ≺ xs) = x ≺ ♯ ⟦ xs ⟧

  ⟦_⟧ : ∀ {A} → Prog A → Stream A
  ⟦ xs ⟧ = value (whnf xs)

fromStream : ∀ {A} → Stream A → Prog A
fromStream (x ≺ xs) = x ≺ ♯ fromStream (♭ xs)

lift : ∀ {A} → (Prog A → Prog A) → Stream A → Stream A
lift f xs = ⟦ f (fromStream xs) ⟧

------------------------------------------------------------------------
-- Some abbreviations

infixr 5 _≺♯_

_≺♯_ : ∀ {A} → A → Prog A → Prog A
x ≺♯ xs = x ≺ ♯ xs

headP : ∀ {A} → Prog A → A
headP xs = head ⟦ xs ⟧

tailP : ∀ {A} → Prog A → Prog A
tailP xs with whnf xs
tailP xs | x ≺ xs′ = xs′
