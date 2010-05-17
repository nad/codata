------------------------------------------------------------------------
-- Proofs of the map-iterate property and iterate fusion
------------------------------------------------------------------------

module MapIterate where

open import Coinduction
open import Data.Nat
open import Data.Stream as Stream
  using (Stream; map; zipWith; iterate; _≈_)
open Stream.Stream; open Stream._≈_
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

private
  module SS {A} = Setoid (Stream.setoid A)

-- The map-iterate property:

map-iterate :  {A : Set} (f : A → A) (x : A) →
               map f (iterate f x) ≈ iterate f (f x)
map-iterate f x = f x ∷ ♯ map-iterate f (f x)

-- An equality proof language.

infixr 5 _∷_
infix  4 _≈P_ _≈W_
infix  3 _∎
infixr 2 _≈⟨_⟩_

data _≈P_ {A : Set} : Stream A → Stream A → Set where
  _∷_          : ∀ (x : A) {xs ys}
                 (xs≈ys : ∞ (♭ xs ≈P ♭ ys)) → x ∷ xs ≈P x ∷ ys
  _≈⟨_⟩_       : ∀ (xs : Stream A) {ys zs}
                 (xs≈ys : xs ≈P ys) (ys≈zs : ys ≈P zs) → xs ≈P zs
  _∎           : (xs : Stream A) → xs ≈P xs
  zipWith-cong : ∀ (_∙_ : A → A → A) {xs₁ ys₁ xs₂ ys₂}
                 (xs₁≈ys₁ : xs₁ ≈P ys₁) (xs₂≈ys₂ : xs₂ ≈P ys₂) →
                 zipWith _∙_ xs₁ xs₂ ≈P zipWith _∙_ ys₁ ys₂

-- Completeness.

completeP : {A : Set} {xs ys : Stream A} → xs ≈ ys → xs ≈P ys
completeP (x ∷ xs≈ys) = x ∷ ♯ completeP (♭ xs≈ys)

-- Weak head normal forms.

data _≈W_ {A : Set} : Stream A → Stream A → Set where
  _∷_ : ∀ x {xs ys} (xs≈ys : ♭ xs ≈P ♭ ys) → x ∷ xs ≈W x ∷ ys

transW : {A : Set} {xs ys zs : Stream A} →
         xs ≈W ys → ys ≈W zs → xs ≈W zs
transW (x ∷ xs≈ys) (.x ∷ ys≈zs) = x ∷ (_ ≈⟨ xs≈ys ⟩ ys≈zs)

reflW : {A : Set} (xs : Stream A) → xs ≈W xs
reflW (x ∷ xs) = x ∷ (♭ xs ∎)

zipWith-congW : ∀ {A : Set} (_∙_ : A → A → A) {xs₁ ys₁ xs₂ ys₂} →
                xs₁ ≈W ys₁ → xs₂ ≈W ys₂ →
                zipWith _∙_ xs₁ xs₂ ≈W zipWith _∙_ ys₁ ys₂
zipWith-congW _∙_ (x₁ ∷ xs₁≈ys₁) (x₂ ∷ xs₂≈ys₂) =
  (x₁ ∙ x₂) ∷ zipWith-cong _∙_ xs₁≈ys₁ xs₂≈ys₂

whnf : {A : Set} {xs ys : Stream A} → xs ≈P ys → xs ≈W ys
whnf (x ∷ xs≈ys)           = x ∷ ♭ xs≈ys
whnf (xs ≈⟨ xs≈ys ⟩ ys≈zs) = transW (whnf xs≈ys) (whnf ys≈zs)
whnf (xs ∎)                = reflW xs
whnf (zipWith-cong _∙_ xs₁≈ys₁ xs₂≈ys₂) =
  zipWith-congW _∙_ (whnf xs₁≈ys₁) (whnf xs₂≈ys₂)

-- Soundness.

mutual

  soundW : {A : Set} {xs ys : Stream A} → xs ≈W ys → xs ≈ ys
  soundW (x ∷ xs≈ys) = x ∷ ♯ soundP xs≈ys

  soundP : {A : Set} {xs ys : Stream A} → xs ≈P ys → xs ≈ ys
  soundP xs≈ys = soundW (whnf xs≈ys)

-- A small hack which enables me to write "by definition" below.

definition : {A : Set} {xs : Stream A} → xs ≈P xs
definition {xs = xs} = xs ∎

by : ∀ {A : Set} {x : A} {xs ys : ∞ (Stream A)} →
     ♭ xs ≈P ♭ ys → x ∷ xs ≈P x ∷ ys
by {x = x} ♭xs≈♭ys = x ∷ ♯ ♭xs≈♭ys

-- Iterate preserves equality.

iterate-cong : {A : Set} (f : A → A) {x y : A} →
               x ≡ y → iterate f x ≈P iterate f y
iterate-cong f {x} refl = iterate f x ∎

-- Iterate fusion.

iterate-fusion : {A B : Set} (h : A → B) (f₁ : A → A) (f₂ : B → B) →
                 ((x : A) → h (f₁ x) ≡ f₂ (h x)) →
                 (x : A) → map h (iterate f₁ x) ≈P iterate f₂ (h x)
iterate-fusion h f₁ f₂ hyp x =
  map h (iterate f₁ x)               ≈⟨ by definition ⟩
  h x ∷ ♯ map h (iterate f₁ (f₁ x))  ≈⟨ h x ∷ ♯ iterate-fusion h f₁ f₂ hyp (f₁ x) ⟩
  h x ∷ ♯ iterate f₂ (h (f₁ x))      ≈⟨ h x ∷ ♯ iterate-cong f₂ (hyp x) ⟩
  h x ∷ ♯ iterate f₂ (f₂ (h x))      ≈⟨ by definition ⟩
  iterate f₂ (h x)                   ∎

-- The equation given for fib in StreamProg has a unique solution.

fib-rhs : Stream ℕ → Stream ℕ
fib-rhs ns = 0 ∷ ♯ zipWith _+_ ns (1 ∷ ♯ ns)

fib-unique :
  ∀ ms ns → ms ≈ fib-rhs ms → ns ≈ fib-rhs ns → ms ≈P ns
fib-unique ms ns ms≈ ns≈ =
  ms         ≈⟨ completeP ms≈ ⟩
  fib-rhs ms ≈⟨ 0 ∷ ♯ zipWith-cong _+_ (fib-unique ms ns ms≈ ns≈)
                                       (1 ∷ ♯ fib-unique ms ns ms≈ ns≈) ⟩
  fib-rhs ns ≈⟨ completeP (SS.sym ns≈) ⟩
  ns         ∎
