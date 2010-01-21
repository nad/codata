------------------------------------------------------------------------
-- An implementation of the Fibonacci sequence using tail
------------------------------------------------------------------------

module SingletonChunks where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Stream as S using (Stream; _≈_; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)

------------------------------------------------------------------------
-- Stream programs

-- StreamP b A encodes programs generating streams in chunks of size
-- (at least) 1. The first chunk may be empty if b is false.

infixr 5 _∷_

data StreamP : Bool → Set → Set₁ where
  [_]     : ∀ {A} (xs : ∞ (StreamP true A)) → StreamP false A
  _∷_     : ∀ {b A} (x : A) (xs : StreamP b A) → StreamP true A
  forget  : ∀ {A} (xs : StreamP true A) → StreamP false A
  tail    : ∀ {A} (xs : StreamP true A) → StreamP false A
  zipWith : ∀ {b A B C} (f : A → B → C)
            (xs : StreamP b A) (ys : StreamP b B) → StreamP b C

data StreamW : Bool → Set → Set₁ where
  [_] : ∀ {A} (xs : StreamP true A) → StreamW false A
  _∷_ : ∀ {A} (x : A) (xs : StreamP true A) → StreamW true A

consW : ∀ {b A} → A → StreamW b A → StreamW true A
consW x [ xs ]   = x ∷ xs
consW x (y ∷ xs) = x ∷ y ∷ xs

forgetW : ∀ {A} → StreamW true A → StreamW false A
forgetW (x ∷ xs) = [ x ∷ forget xs ]

tailW : ∀ {A} → StreamW true A → StreamW false A
tailW (x ∷ xs) = [ xs ]

zipWithW : ∀ {b A B C} → (A → B → C) →
           StreamW b A → StreamW b B → StreamW b C
zipWithW f [ xs ]   [ ys ]   = [ zipWith f xs ys ]
zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

whnf : ∀ {b A} → StreamP b A → StreamW b A
whnf [ xs ]            = [ ♭ xs ]
whnf (x ∷ xs)          = consW x (whnf xs)
whnf (forget xs)       = forgetW (whnf xs)
whnf (tail xs)         = tailW (whnf xs)
whnf (zipWith f xs ys) = zipWithW f (whnf xs) (whnf ys)

mutual

  ⟦_⟧W : ∀ {A} → StreamW true A → Stream A
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  ⟦_⟧P : ∀ {A} → StreamP true A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- The Fibonacci sequence

fib : StreamP true ℕ
fib = 0 ∷ [ ♯ (1 ∷ zipWith _+_ (forget fib) (tail fib)) ]

------------------------------------------------------------------------
-- The definition of fib is correct

-- ⟦_⟧ is homomorphic with respect to zipWith/S.zipWith.

zipWith-hom : ∀ {A B C} (_∙_ : A → B → C) xs ys →
              ⟦ zipWith _∙_ xs ys ⟧P ≈ S.zipWith _∙_ ⟦ xs ⟧P ⟦ ys ⟧P
zipWith-hom _∙_ xs ys with whnf xs | whnf ys
zipWith-hom _∙_ xs ys | x ∷ xs′ | y ∷ ys′ =
  (x ∙ y) ∷ ♯ zipWith-hom _∙_ xs′ ys′

-- S.zipWith is a congruence.

open import StreamProg using (zipWith-cong)

-- forget is the identity on streams.

open import MapIterate using (_≈P_; _∷_; _≈⟨_⟩_; _∎; soundP)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _with-≡_)

forget-lemma : ∀ {A} x (xs : StreamP true A) →
               ⟦ x ∷ forget xs ⟧P ≈P x ∷ ♯ ⟦ xs ⟧P
forget-lemma x xs with P.inspect (whnf xs)
... | (y ∷ ys) with-≡ eq rewrite eq = x ∷ ♯ helper
  where
  helper : ⟦ y ∷ forget ys ⟧P ≈P ⟦ xs ⟧P
  helper rewrite eq = _ ≈⟨ forget-lemma y ys ⟩ (y ∷ ♯ (_ ∎))

-- The stream ⟦ fib ⟧P satisfies its intended defining equation.

open import Relation.Binary
module SS {A : Set} = Setoid (S.setoid A)

fib-correct :
  ⟦ fib ⟧P ≈ 0 ∷ ♯ (1 ∷ ♯ S.zipWith _+_ ⟦ fib ⟧P (S.tail ⟦ fib ⟧P))
fib-correct =
  0 ∷ ♯ (1 ∷ ♯ SS.trans
    (zipWith-hom _+_ (0 ∷ forget fib′) fib′)
    (zipWith-cong _+_ (SS.trans (soundP (forget-lemma 0 fib′))
                                (0 ∷ ♯ SS.refl)) SS.refl))
  where fib′ = 1 ∷ zipWith _+_ (forget fib) (tail fib)
