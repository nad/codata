------------------------------------------------------------------------
-- Nested applications of the defined function can be handled
------------------------------------------------------------------------

module Nested where

open import Coinduction
open import Data.Stream
open import Function

------------------------------------------------------------------------
-- A definition of φ (x ∷ xs) = x ∷ φ (φ xs)

module φ where

  infixr 5 _∷_

  data StreamP (A : Set) : Set where
    _∷_ : (x : A) (xs : ∞ (StreamP A)) → StreamP A
    φP  : (xs : StreamP A) → StreamP A

  data StreamW (A : Set) : Set where
    _∷_ : (x : A) (xs : StreamP A) → StreamW A

  φW  : {A : Set} → StreamW A → StreamW A
  φW (x ∷ xs) = x ∷ φP (φP xs)

  whnf : {A : Set} → StreamP A → StreamW A
  whnf (x ∷ xs)   = x ∷ ♭ xs
  whnf (φP xs)    = φW (whnf xs)

  mutual

    ⟦_⟧W : {A : Set} → StreamW A → Stream A
    ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

    ⟦_⟧P : {A : Set} → StreamP A → Stream A
    ⟦ xs ⟧P = ⟦ whnf xs ⟧W

  ⌈_⌉ : {A : Set} → Stream A → StreamP A
  ⌈ x ∷ xs ⌉ = x ∷ ♯ ⌈ ♭ xs ⌉

  φ : {A : Set} → Stream A → Stream A
  φ xs = ⟦ φP ⌈ xs ⌉ ⟧P

open φ using (⟦_⟧P; ⟦_⟧W; φP; φW; φ; _∷_; ⌈_⌉)

------------------------------------------------------------------------
-- An equality proof language

module Equality where

  infixr 5 _∷_
  infix  4 _≈P_ _≈W_
  infix  3 _∎
  infixr 2 _≈⟨_⟩_

  data _≈P_ {A : Set} : Stream A → Stream A → Set where
    _∷_     : ∀ (x : A) {xs ys}
              (xs≈ys : ∞ (♭ xs ≈P ♭ ys)) → x ∷ xs ≈P x ∷ ys
    _≈⟨_⟩_  : ∀ (xs : Stream A) {ys zs}
              (xs≈ys : xs ≈P ys) (ys≈zs : ys ≈P zs) → xs ≈P zs
    _∎      : (xs : Stream A) → xs ≈P xs
    sym     : ∀ {xs ys} (xs≈ys : xs ≈P ys) → ys ≈P xs
    φP-cong : (xs ys : φ.StreamP A) (xs≈ys : ⟦ xs ⟧P ≈P ⟦ ys ⟧P) →
              ⟦ φP xs ⟧P ≈P ⟦ φP ys ⟧P

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

  symW : {A : Set} {xs ys : Stream A} → xs ≈W ys → ys ≈W xs
  symW (x ∷ xs≈ys) = x ∷ sym xs≈ys

  φW-cong : {A : Set} (xs ys : φ.StreamW A) →
            ⟦ xs ⟧W ≈W ⟦ ys ⟧W → ⟦ φW xs ⟧W ≈W ⟦ φW ys ⟧W
  φW-cong (.x ∷ xs) (.x ∷ ys) (x ∷ xs≈ys) =
    x ∷ φP-cong (φP xs) (φP ys) (φP-cong xs ys xs≈ys)

  whnf : {A : Set} {xs ys : Stream A} → xs ≈P ys → xs ≈W ys
  whnf (x ∷ xs≈ys)           = x ∷ ♭ xs≈ys
  whnf (xs ≈⟨ xs≈ys ⟩ ys≈zs) = transW (whnf xs≈ys) (whnf ys≈zs)
  whnf (xs ∎)                = reflW xs
  whnf (sym xs≈ys)           = symW (whnf xs≈ys)
  whnf (φP-cong xs ys xs≈ys) =
    φW-cong (φ.whnf xs) (φ.whnf ys) (whnf xs≈ys)

  -- Soundness.

  mutual

    soundW : {A : Set} {xs ys : Stream A} → xs ≈W ys → xs ≈ ys
    soundW (x ∷ xs≈ys) = x ∷ ♯ soundP xs≈ys

    soundP : {A : Set} {xs ys : Stream A} → xs ≈P ys → xs ≈ ys
    soundP xs≈ys = soundW (whnf xs≈ys)

open Equality using (_≈P_; _∷_; _≈⟨_⟩_; _∎; sym; φP-cong)

------------------------------------------------------------------------
-- Correctness

module Correctness where

  ⟦⌈_⌉⟧P : {A : Set} (xs : Stream A) → ⟦ ⌈ xs ⌉ ⟧P ≈P xs
  ⟦⌈ x ∷ xs ⌉⟧P = x ∷ ♯ ⟦⌈ ♭ xs ⌉⟧P

  φ-cong : {A : Set} (xs ys : Stream A) → xs ≈P ys → φ xs ≈P φ ys
  φ-cong xs ys xs≈ys =
    φ xs            ≈⟨ φ xs ∎ ⟩
    ⟦ φP ⌈ xs ⌉ ⟧P  ≈⟨ φP-cong ⌈ xs ⌉ ⌈ ys ⌉ lemma ⟩
    ⟦ φP ⌈ ys ⌉ ⟧P  ≈⟨ φ ys ∎ ⟩
    φ ys  ∎
    where
    lemma =
      ⟦ ⌈ xs ⌉ ⟧P  ≈⟨ ⟦⌈ xs ⌉⟧P ⟩
      xs           ≈⟨ xs≈ys ⟩
      ys           ≈⟨ sym ⟦⌈ ys ⌉⟧P ⟩
      ⟦ ⌈ ys ⌉ ⟧P  ∎

  -- A workaround for Agda's strange definitional equality.

  infix 10 ♯′_

  ♯′_ : {A : Set} → A → ∞ A
  ♯′_ = ♯_

  φW-hom : {A : Set} (xs : φ.StreamW A) →
           ⟦ φW xs ⟧W ≈P head ⟦ xs ⟧W ∷ ♯′ φ (φ (tail ⟦ xs ⟧W))
  φW-hom (x ∷ xs) = x ∷ ♯ (
    ⟦ φP (φP xs) ⟧P                  ≈⟨ φP-cong (φP xs) (φP ⌈ ⟦ xs ⟧P ⌉) $
                                                φP-cong xs (⌈ ⟦ xs ⟧P ⌉)
                                                        (sym ⟦⌈ ⟦ xs ⟧P ⌉⟧P) ⟩
    ⟦ φP (φP ⌈ ⟦ xs ⟧P ⌉) ⟧P         ≈⟨ φP-cong (φP ⌈ ⟦ xs ⟧P ⌉)
                                                ⌈ ⟦ φP ⌈ ⟦ xs ⟧P ⌉ ⟧P ⌉
                                                (sym ⟦⌈ ⟦ φP ⌈ ⟦ xs ⟧P ⌉ ⟧P ⌉⟧P) ⟩
    ⟦ φP ⌈ ⟦ φP ⌈ ⟦ xs ⟧P ⌉ ⟧P ⌉ ⟧P  ∎)

  φ-hom : {A : Set} (xs : φ.StreamP A) →
          ⟦ φP xs ⟧P ≈P head ⟦ xs ⟧P ∷ ♯′ φ (φ (tail ⟦ xs ⟧P))
  φ-hom xs = φW-hom (φ.whnf xs)

  φ-correct : {A : Set} (x : A) (xs : Stream A) →
              φ (x ∷ ♯ xs) ≈P x ∷ ♯ φ (φ xs)
  φ-correct x xs =
    φ (x ∷ ♯ xs)              ≈⟨ φ (x ∷ ♯ xs) ∎ ⟩
    ⟦ φP ⌈ x ∷ ♯ xs ⌉ ⟧P      ≈⟨ φ-hom ⌈ x ∷ ♯ xs ⌉ ⟩
    x ∷ ♯′ φ (φ ⟦ ⌈ xs ⌉ ⟧P)  ≈⟨ x ∷ ♯ φ-cong (φ ⟦ ⌈ xs ⌉ ⟧P) (φ xs)
                                              (φ-cong (⟦ ⌈ xs ⌉ ⟧P) xs ⟦⌈ xs ⌉⟧P) ⟩
    x ∷ _                     ∎
