------------------------------------------------------------------------
-- A universe for stream programs
------------------------------------------------------------------------

module Stream.Programs where

open import Coinduction hiding (∞)
import Stream as S
open S using (Stream; _≈_; _≺_; head; tail)
open import Relation.Binary.PropositionalEquality
open import Data.Vec using (Vec; []; _∷_)

------------------------------------------------------------------------
-- Stream programs

infix  8 _∞
infixr 7 _·_
infix  6 _⟨_⟩_
infixr 5 _≺_ _≺′_ _⋎_ _≺≺_
infix  4 ↓_

mutual

  data Stream′ A : Set1 where
    _≺_ : (x : A) (xs : ∞₁ (StreamProg A)) → Stream′ A

  data StreamProg (A : Set) : Set1 where
    ↓_      : (xs : Stream′ A) → StreamProg A
    _∞      : (x : A) → StreamProg A
    _·_     : ∀ {B}
              (f : B → A) (xs : StreamProg B) → StreamProg A
    _⟨_⟩_   : ∀ {B C}
              (xs : StreamProg B)
              (_∙_ : B → C → A)
              (ys : StreamProg C) →
              StreamProg A
    _⋎_     : (xs ys : StreamProg A) → StreamProg A
    iterate : (f : A → A) (x : A) → StreamProg A
    _≺≺_    : ∀ {n} (xs : Vec A n) (ys : StreamProg A) →
              StreamProg A

_≺′_ : ∀ {A} → A → StreamProg A → Stream′ A
x ≺′ xs = x ≺ ♯₁ xs

------------------------------------------------------------------------
-- Conversion

P⇒′ : ∀ {A} → StreamProg A → Stream′ A
P⇒′ (↓ xs)           = xs
P⇒′ (x ∞)            = x ≺′ x ∞
P⇒′ (f · xs)         with P⇒′ xs
P⇒′ (f · xs)         | x ≺ xs′ = f x ≺′ f · ♭₁ xs′
P⇒′ (xs ⟨ _∙_ ⟩ ys)  with P⇒′ xs | P⇒′ ys
P⇒′ (xs ⟨ _∙_ ⟩ ys)  | x ≺ xs′ | y ≺ ys′ = (x ∙ y) ≺′ ♭₁ xs′ ⟨ _∙_ ⟩ ♭₁ ys′
P⇒′ (xs ⋎ ys)        with P⇒′ xs
P⇒′ (xs ⋎ ys)        | x ≺ xs′ = x ≺′ ys ⋎ ♭₁ xs′
P⇒′ (iterate f x)    = x ≺′ iterate f (f x)
P⇒′ ([]       ≺≺ ys) = P⇒′ ys
P⇒′ ((x ∷ xs) ≺≺ ys) = x ≺′ xs ≺≺ ys

mutual

  ′⇒ : ∀ {A} → Stream′ A → Stream A
  ′⇒ (x ≺ xs) = x ≺ ′⇒′ where ′⇒′ ~ ♯ P⇒ (♭₁ xs)

  P⇒ : ∀ {A} → StreamProg A → Stream A
  P⇒ xs = ′⇒ (P⇒′ xs)

⇒P : ∀ {A} → Stream A → StreamProg A
⇒P (x ≺ xs) = ↓ x ≺ ⇒P′ where ⇒P′ ~ ♯₁ ⇒P (♭ xs)

lift : ∀ {A} →
       (StreamProg A → StreamProg A) → Stream A → Stream A
lift f xs = P⇒ (f (⇒P xs))

------------------------------------------------------------------------
-- Some abbreviations

headP : ∀ {A} → StreamProg A → A
headP xs = head (P⇒ xs)

tailP : ∀ {A} → StreamProg A → StreamProg A
tailP xs with P⇒′ xs
tailP xs | x ≺ xs′ = ♭₁ xs′
