------------------------------------------------------------------------
-- An ad-hoc but straightforward solution to the problem of showing
-- that elegant definitions of the Hamming numbers (see EWD 792) and
-- the Fibonacci sequence are productive
------------------------------------------------------------------------

module StreamProg where

open import Coinduction
import Stream as S
open S using (Stream; _≺_; _≈_; Ord; lt; eq; gt)
open import Data.Nat
open import Relation.Binary
private
  module SS {A} = Setoid (S.setoid A)
import IO

------------------------------------------------------------------------
-- Stream programs

infixr 5 _≺_

data Prog (A : Set) : Set1 where
  _≺_     : (x : A) (xs : ∞ (Prog A)) → Prog A
  zipWith : ∀ {B C} (f : B → C → A)
            (xs : Prog B) (ys : Prog C) → Prog A
  map     : ∀ {B} (f : B → A) (xs : Prog B) → Prog A
  merge   : (cmp : A → A → Ord)
            (xs : Prog A) (ys : Prog A) → Prog A

data WHNF A : Set1 where
  _≺_ : (x : A) (xs : Prog A) → WHNF A

whnf : ∀ {A} → Prog A → WHNF A
whnf (x ≺ xs)          = x ≺ ♭ xs
whnf (zipWith f xs ys) with whnf xs | whnf ys
whnf (zipWith f xs ys) | x ≺ xs′ | y ≺ ys′ = f x y ≺ zipWith f xs′ ys′
whnf (map f xs)        with whnf xs
whnf (map f xs)        | x ≺ xs′ = f x ≺ map f xs′
whnf (merge cmp xs ys) with whnf xs | whnf ys
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ with cmp x y
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | lt = x ≺ merge cmp xs′ (y ≺ ♯ ys′)
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | eq = x ≺ merge cmp xs′ ys′
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | gt = y ≺ merge cmp (x ≺ ♯ xs′) ys′

mutual

  value : ∀ {A} → WHNF A → Stream A
  value (x ≺ xs) = x ≺ ♯ ⟦ xs ⟧

  ⟦_⟧ : ∀ {A} → Prog A → Stream A
  ⟦ xs ⟧ = value (whnf xs)

------------------------------------------------------------------------
-- Examples

fib : Prog ℕ
fib = 0 ≺ ♯ zipWith _+_ fib (1 ≺ ♯ fib)

-- Alternative definition showing that definitions do not need to
-- start with a cons constructor.

fib′ : Prog ℕ
fib′ = zipWith _+_ (0 ≺ ♯ fib′) (0 ≺ ♯ (1 ≺ ♯ fib′))

cmp : ℕ → ℕ → Ord
cmp m n = toOrd (compare m n)
  where
  toOrd : ∀ {m n} → Ordering m n → Ord
  toOrd (less _ _)    = lt
  toOrd (equal _)     = eq
  toOrd (greater _ _) = gt

hamming : Prog ℕ
hamming = 1 ≺ ♯ merge cmp (map (_*_ 2) hamming) (map (_*_ 3) hamming)

main = IO.run (S.putStream (S._⋎_ ⟦ fib ⟧ ⟦ hamming ⟧))

------------------------------------------------------------------------
-- The definition of fib is correct

-- ⟦_⟧ is homomorphic with respect to zipWith/S.zipWith.

zipWith-hom : ∀ {A B C} (_∙_ : A → B → C) xs ys →
              ⟦ zipWith _∙_ xs ys ⟧ ≈ S.zipWith _∙_ ⟦ xs ⟧ ⟦ ys ⟧
zipWith-hom _∙_ xs ys with whnf xs | whnf ys
zipWith-hom _∙_ xs ys | x ≺ xs′ | y ≺ ys′ =
  (x ∙ y) ≺ ♯ zipWith-hom _∙_ xs′ ys′

-- S.zipWith is a congruence.

zipWith-cong : ∀ {A B C} (_∙_ : A → B → C) {xs xs′ ys ys′} →
               xs ≈ xs′ → ys ≈ ys′ →
               S.zipWith _∙_ xs ys ≈ S.zipWith _∙_ xs′ ys′
zipWith-cong _∙_ (x ≺ xs≈) (y ≺ ys≈) =
  (x ∙ y) ≺ ♯ zipWith-cong _∙_ (♭ xs≈) (♭ ys≈)

-- Unfortunately Agda's definitional equality for coinductive
-- constructors is currently a little strange, so the result type
-- cannot be written out completely here:

fib-correct′ :
  ⟦ fib ⟧ ≈ 0 ≺ ♯ S.zipWith _+_ ⟦ fib ⟧ (1 ≺ _ {- ♯ ⟦ fib ⟧ -})
fib-correct′ = 0 ≺ ♯ zipWith-hom _+_ fib (1 ≺ ♯ fib)

-- Fortunately there is a workaround.

fib-correct : ⟦ fib ⟧ ≈ 0 ≺ ♯ S.zipWith _+_ ⟦ fib ⟧ (1 ≺ ♯ ⟦ fib ⟧)
fib-correct =
  0 ≺ ♯ SS.trans (zipWith-hom  _+_ fib     (1 ≺ ♯ fib))
                 (zipWith-cong _+_ SS.refl (1 ≺ ♯ SS.refl))

------------------------------------------------------------------------
-- The definition of hamming is correct

-- ⟦_⟧ is homomorphic with respect to map/S.map.

map-hom : ∀ {A B} (f : A → B) xs →
          ⟦ map f xs ⟧ ≈ S.map f ⟦ xs ⟧
map-hom f xs with whnf xs
... | x ≺ xs′ = f x ≺ ♯ map-hom f xs′

-- ⟦_⟧ is homomorphic with respect to merge/S.merge.

merge-hom : ∀ {A} (cmp : A → A → Ord) xs ys →
            ⟦ merge cmp xs ys ⟧ ≈ S.merge cmp ⟦ xs ⟧ ⟦ ys ⟧
merge-hom cmp xs ys with whnf xs | whnf ys
... | x ≺ xs′ | y ≺ ys′ with cmp x y
...   | lt = x ≺ ♯ merge-hom cmp xs′ _
...   | eq = x ≺ ♯ merge-hom cmp xs′ ys′
...   | gt = y ≺ ♯ merge-hom cmp _ ys′

-- S.merge is a congruence.

merge-cong : ∀ {A} (cmp : A → A → Ord) {xs xs′ ys ys′} →
             xs ≈ xs′ → ys ≈ ys′ →
             S.merge cmp xs ys ≈ S.merge cmp xs′ ys′
merge-cong cmp (x ≺ xs≈) (y ≺ ys≈) with cmp x y
... | lt = x ≺ ♯ merge-cong cmp (♭ xs≈) (y ≺ ys≈)
... | eq = x ≺ ♯ merge-cong cmp (♭ xs≈) (♭ ys≈)
... | gt = y ≺ ♯ merge-cong cmp (x ≺ xs≈) (♭ ys≈)

-- hamming is correct.

hamming-correct : ⟦ hamming ⟧ ≈
                  1 ≺ ♯ S.merge cmp (S.map (_*_ 2) ⟦ hamming ⟧)
                                    (S.map (_*_ 3) ⟦ hamming ⟧)
hamming-correct =
  1 ≺ ♯ SS.trans (merge-hom cmp (map (_*_ 2) hamming)
                                (map (_*_ 3) hamming))
                 (merge-cong cmp (map-hom (_*_ 2) hamming)
                                 (map-hom (_*_ 3) hamming))
