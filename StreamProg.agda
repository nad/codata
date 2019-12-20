------------------------------------------------------------------------
-- An ad-hoc but straightforward solution to the problem of showing
-- that elegant definitions of the Hamming numbers (see EWD 792) and
-- the Fibonacci sequence are productive
------------------------------------------------------------------------

module StreamProg where

open import Codata.Musical.Notation
open import Codata.Musical.Stream as S using (Stream; _∷_; _≈_)
open import Data.Nat
open import Relation.Binary
import Relation.Binary.PropositionalEquality as P

private
  module SS {A : Set} = Setoid (S.setoid A)

------------------------------------------------------------------------
-- Merging of streams

data Ord : Set where
  lt : Ord
  eq : Ord
  gt : Ord

merge : {A : Set} → (A → A → Ord) → Stream A → Stream A → Stream A
merge cmp (x ∷ xs) (y ∷ ys) with cmp x y
... | lt = x ∷ ♯ merge cmp (♭ xs)   (y ∷ ys)
... | eq = x ∷ ♯ merge cmp (♭ xs)   (♭ ys)
... | gt = y ∷ ♯ merge cmp (x ∷ xs) (♭ ys)

------------------------------------------------------------------------
-- Stream programs

infixr 5 _∷_

data StreamP (A : Set) : Set1 where
  _∷_     : (x : A) (xs : ∞ (StreamP A)) → StreamP A
  zipWith : ∀ {B C} (f : B → C → A)
            (xs : StreamP B) (ys : StreamP C) → StreamP A
  map     : ∀ {B} (f : B → A) (xs : StreamP B) → StreamP A
  mergeP  : (cmp : A → A → Ord)
            (xs : StreamP A) (ys : StreamP A) → StreamP A

data StreamW A : Set1 where
  _∷_ : (x : A) (xs : StreamP A) → StreamW A

zipWithW : {A B C : Set} →
           (A → B → C) → StreamW A → StreamW B → StreamW C
zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWith f xs ys

mapW : {A B : Set} → (A → B) → StreamW A → StreamW B
mapW f (x ∷ xs) = f x ∷ map f xs

mergeW : {A : Set} →
         (A → A → Ord) → StreamW A → StreamW A → StreamW A
mergeW cmp (x ∷ xs) (y ∷ ys) with cmp x y
... | lt = x ∷ mergeP cmp xs (y ∷ ♯ ys)
... | eq = x ∷ mergeP cmp xs ys
... | gt = y ∷ mergeP cmp (x ∷ ♯ xs) ys

whnf : ∀ {A} → StreamP A → StreamW A
whnf (x ∷ xs)           = x ∷ ♭ xs
whnf (zipWith f xs ys)  = zipWithW f (whnf xs) (whnf ys)
whnf (map f xs)         = mapW f (whnf xs)
whnf (mergeP cmp xs ys) = mergeW cmp (whnf xs) (whnf ys)

mutual

  ⟦_⟧W : ∀ {A} → StreamW A → Stream A
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  ⟦_⟧P : ∀ {A} → StreamP A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- Examples

fib : StreamP ℕ
fib = 0 ∷ ♯ zipWith _+_ fib (1 ∷ ♯ fib)

-- Alternative definition showing that definitions do not need to
-- start with a cons constructor.

fib′ : StreamP ℕ
fib′ = zipWith _+_ (0 ∷ ♯ fib′) (0 ∷ ♯ (1 ∷ ♯ fib′))

cmp : ℕ → ℕ → Ord
cmp m n = toOrd (compare m n)
  where
  toOrd : ∀ {m n} → Ordering m n → Ord
  toOrd (less _ _)    = lt
  toOrd (equal _)     = eq
  toOrd (greater _ _) = gt

hamming : StreamP ℕ
hamming = 1 ∷ ♯ mergeP cmp (map (_*_ 2) hamming) (map (_*_ 3) hamming)

------------------------------------------------------------------------
-- The definition of fib is correct

-- ⟦_⟧P is homomorphic with respect to zipWith/S.zipWith.

zipWith-hom : ∀ {A B C} (_∙_ : A → B → C) xs ys →
              ⟦ zipWith _∙_ xs ys ⟧P ≈ S.zipWith _∙_ ⟦ xs ⟧P ⟦ ys ⟧P
zipWith-hom _∙_ xs ys with whnf xs | whnf ys
zipWith-hom _∙_ xs ys | x ∷ xs′ | y ∷ ys′ =
  P.refl ∷ ♯ zipWith-hom _∙_ xs′ ys′

-- Unfortunately Agda's definitional equality for coinductive
-- constructors is currently a little strange, so the result type
-- cannot be written out completely here:

fib-correct′ :
  ⟦ fib ⟧P ≈ 0 ∷ ♯ S.zipWith _+_ ⟦ fib ⟧P (1 ∷ _ {- ♯ ⟦ fib ⟧P -})
fib-correct′ = P.refl ∷ ♯ zipWith-hom _+_ fib (1 ∷ ♯ fib)

-- Fortunately there is a workaround.

fib-correct : ⟦ fib ⟧P ≈ 0 ∷ ♯ S.zipWith _+_ ⟦ fib ⟧P (1 ∷ ♯ ⟦ fib ⟧P)
fib-correct =
  P.refl ∷ ♯ SS.trans (zipWith-hom _+_ fib (1 ∷ ♯ fib))
                      (S.zipWith-cong _+_ (SS.refl {x = 0 ∷ _})
                                          (P.refl ∷ ♯ SS.refl))

-- For a proof showing that the given equation for fib has a unique
-- solution, see MapIterate.

------------------------------------------------------------------------
-- The definition of hamming is correct

-- ⟦_⟧P is homomorphic with respect to map/S.map.

map-hom : ∀ {A B} (f : A → B) xs →
          ⟦ map f xs ⟧P ≈ S.map f ⟦ xs ⟧P
map-hom f xs with whnf xs
... | x ∷ xs′ = P.refl ∷ ♯ map-hom f xs′

-- ⟦_⟧P is homomorphic with respect to mergeP/merge.

merge-hom : ∀ {A} (cmp : A → A → Ord) xs ys →
            ⟦ mergeP cmp xs ys ⟧P ≈ merge cmp ⟦ xs ⟧P ⟦ ys ⟧P
merge-hom cmp xs ys with whnf xs | whnf ys
... | x ∷ xs′ | y ∷ ys′ with cmp x y
...   | lt = P.refl ∷ ♯ merge-hom cmp xs′ (y ∷ ♯ ys′)
...   | eq = P.refl ∷ ♯ merge-hom cmp xs′ ys′
...   | gt = P.refl ∷ ♯ merge-hom cmp (x ∷ ♯ xs′) ys′

-- merge is a congruence.

merge-cong : ∀ {A} (cmp : A → A → Ord) {xs xs′ ys ys′} →
             xs ≈ xs′ → ys ≈ ys′ →
             merge cmp xs ys ≈ merge cmp xs′ ys′
merge-cong cmp (_∷_ {x = x} P.refl xs≈)
               (_∷_ {x = y} P.refl ys≈) with cmp x y
... | lt = P.refl ∷ ♯ merge-cong cmp (♭ xs≈) (P.refl ∷ ys≈)
... | eq = P.refl ∷ ♯ merge-cong cmp (♭ xs≈) (♭ ys≈)
... | gt = P.refl ∷ ♯ merge-cong cmp (P.refl ∷ xs≈) (♭ ys≈)

-- hamming is correct.

hamming-correct : ⟦ hamming ⟧P ≈
                  1 ∷ ♯ merge cmp (S.map (_*_ 2) ⟦ hamming ⟧P)
                                  (S.map (_*_ 3) ⟦ hamming ⟧P)
hamming-correct =
  P.refl ∷ ♯ SS.trans (merge-hom cmp (map (_*_ 2) hamming)
                                     (map (_*_ 3) hamming))
                      (merge-cong cmp (map-hom (_*_ 2) hamming)
                                      (map-hom (_*_ 3) hamming))
