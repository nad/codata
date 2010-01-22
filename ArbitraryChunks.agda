------------------------------------------------------------------------
-- Another implementation of the Fibonacci sequence using tail
------------------------------------------------------------------------

module ArbitraryChunks where

open import Coinduction
open import Data.Bool
open import Data.Nat
open import Data.Stream as S using (Stream; _≈_; _∷_)
open import Data.Vec as V using (Vec; []; _∷_)

------------------------------------------------------------------------
-- Stream programs

-- StreamP m n A encodes programs generating streams in chunks of size
-- (at least) m, where the first chunk has size (at least) n.

infixr 5 _∷_

data StreamP (m : ℕ) : ℕ → Set → Set₁ where
  [_]     : ∀ {A} (xs : ∞ (StreamP m m A)) → StreamP m 0 A
  _∷_     : ∀ {n A} (x : A) (xs : StreamP m n A) → StreamP m (suc n) A
  forget  : ∀ {n A} (xs : StreamP m (suc n) A) → StreamP m n A
  tail    : ∀ {n A} (xs : StreamP m (suc n) A) → StreamP m n A
  zipWith : ∀ {n A B C} (f : A → B → C)
            (xs : StreamP m n A) (ys : StreamP m n B) → StreamP m n C

data StreamW (m : ℕ) : ℕ → Set → Set₁ where
  [_] : ∀ {A} (xs : StreamP m m A) → StreamW m 0 A
  _∷_ : ∀ {n A} (x : A) (xs : StreamW m n A) → StreamW m (suc n) A

consW : ∀ {m n A} → A → StreamW m n A → StreamW m (suc n) A
consW x [ xs ]   = x ∷ [ xs ]
consW x (y ∷ xs) = x ∷ y ∷ xs

forgetW : ∀ {m n A} → StreamW (suc m) (suc n) A → StreamW (suc m) n A
forgetW {n = zero}  (x ∷ [ xs ]) = [ x ∷ forget xs ]
forgetW {n = suc n} (x ∷ xs)     = x ∷ forgetW xs

tailW : ∀ {m n A} → StreamW m (suc n) A → StreamW m n A
tailW (x ∷ xs) = xs

zipWithW : ∀ {m n A B C} → (A → B → C) →
           StreamW m n A → StreamW m n B → StreamW m n C
zipWithW f [ xs ]   [ ys ]   = [ zipWith f xs ys ]
zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithW f xs ys

whnf : ∀ {m n A} → StreamP (suc m) n A → StreamW (suc m) n A
whnf [ xs ]            = [ ♭ xs ]
whnf (x ∷ xs)          = consW x (whnf xs)
whnf (forget xs)       = forgetW (whnf xs)
whnf (tail xs)         = tailW (whnf xs)
whnf (zipWith f xs ys) = zipWithW f (whnf xs) (whnf ys)

mutual

  ⟦_⟧W : ∀ {m n A} → StreamW (suc m) (suc n) A → Stream A
  ⟦ x ∷ [ xs ]   ⟧W = x ∷ ♯ ⟦ xs ⟧P
  ⟦ x ∷ (y ∷ xs) ⟧W = x ∷ ♯ ⟦ y ∷ xs ⟧W

  ⟦_⟧P : ∀ {m n A} → StreamP (suc m) (suc n) A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- Some examples

-- The Fibonacci sequence.

fib : StreamP 1 1 ℕ
fib = 0 ∷ [ ♯ (1 ∷ zipWith _+_ (forget fib) (tail fib)) ]

-- Some sequence which is defined using (tail ∘ tail).

someSequence : StreamP 2 2 ℕ
someSequence =
  0 ∷ 1 ∷ [ ♯ (1 ∷ 2 ∷ zipWith _+_ (tail (tail someSequence))
                                   (forget (forget someSequence))) ]

------------------------------------------------------------------------
-- The definition of fib is correct

-- ⟦_⟧ is homomorphic with respect to zipWith/S.zipWith.

mutual

  zipWithW-hom :
    ∀ {m n A B C} (_∙_ : A → B → C)
    (xs : StreamW (suc m) (suc n) A) ys →
    ⟦ zipWithW _∙_ xs ys ⟧W ≈ S.zipWith _∙_ ⟦ xs ⟧W ⟦ ys ⟧W
  zipWithW-hom _∙_ (x ∷ [ xs ]) (y ∷ [ ys ])   =
    (x ∙ y) ∷ ♯ zipWith-hom _∙_ xs ys
  zipWithW-hom _∙_ (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) =
    (x ∙ y) ∷ ♯ zipWithW-hom _∙_ (x′ ∷ xs) (y′ ∷ ys)

  zipWith-hom : ∀ {m n A B C} (_∙_ : A → B → C)
                (xs : StreamP (suc m) (suc n) A) ys →
                ⟦ zipWith _∙_ xs ys ⟧P ≈ S.zipWith _∙_ ⟦ xs ⟧P ⟦ ys ⟧P
  zipWith-hom _∙_ xs ys = zipWithW-hom _∙_ (whnf xs) (whnf ys)

-- S.zipWith is a congruence.

open import StreamProg using (zipWith-cong)

-- forget is the identity on streams.

open import MapIterate using (_≈P_; _∷_; _≈⟨_⟩_; _∎; soundP)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; _with-≡_)

mutual

  forgetW-lemma : ∀ {m n A} x (xs : StreamW (suc m) (suc n) A) →
                  ⟦ x ∷ forgetW xs ⟧W ≈P x ∷ ♯ ⟦ xs ⟧W
  forgetW-lemma x (x′ ∷ [ xs ])  = x ∷ ♯ (_ ≈⟨ forget-lemma x′ xs ⟩ x′ ∷ ♯ (_ ∎))
  forgetW-lemma x (x′ ∷ x″ ∷ xs) = x ∷ ♯ (_ ≈⟨ forgetW-lemma x′ (x″ ∷ xs) ⟩ x′ ∷ ♯ (_ ∎) )

  forget-lemma : ∀ {m n A} x (xs : StreamP (suc m) (suc n) A) →
                 ⟦ x ∷ forget xs ⟧P ≈P x ∷ ♯ ⟦ xs ⟧P
  forget-lemma x xs with P.inspect (whnf xs)
  ... | (y ∷ y′ ∷ ys) with-≡ eq rewrite eq = x ∷ ♯ helper
    where
    helper : ⟦ y ∷ forgetW (y′ ∷ ys) ⟧W ≈P ⟦ xs ⟧P
    helper rewrite eq = _ ≈⟨ forgetW-lemma y (y′ ∷ ys) ⟩ y ∷ ♯ (_ ∎)
  ... | (y ∷ [ ys ])  with-≡ eq rewrite eq = x ∷ ♯ helper
    where
    helper : ⟦ y ∷ forget ys ⟧P ≈P ⟦ xs ⟧P
    helper rewrite eq = _ ≈⟨ forget-lemma y ys ⟩ y ∷ ♯ (_ ∎)

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
