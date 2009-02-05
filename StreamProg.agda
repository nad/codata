------------------------------------------------------------------------
-- An ad-hoc but straightforward solution to the problem of showing
-- that elegant definitions of the Hamming numbers (see EWD 792) and
-- the Fibonacci sequence are productive
------------------------------------------------------------------------

module StreamProg where

open import Coinduction
import Stream as S
open S using (Stream; _≺_)
open import Data.Nat
import IO

------------------------------------------------------------------------
-- Stream programs

data Ord : Set where
  lt : Ord
  eq : Ord
  gt : Ord

infixr 5 _≺_

data Prog (A : Set) : Set1 where
  _≺_     : (x : A) (xs : ∞₁ (Prog A)) → Prog A
  zipWith : ∀ {B C} (f : B → C → A)
            (xs : Prog B) (ys : Prog C) → Prog A
  map     : ∀ {B} (f : B → A) (xs : Prog B) → Prog A
  merge   : (cmp : A → A → Ord)
            (xs : Prog A) (ys : Prog A) → Prog A

data WHNF A : Set1 where
  _≺_ : (x : A) (xs : Prog A) → WHNF A

whnf : ∀ {A} → Prog A → WHNF A
whnf (x ≺ xs)          = x ≺ ♭₁ xs
whnf (zipWith f xs ys) with whnf xs | whnf ys
whnf (zipWith f xs ys) | x ≺ xs′ | y ≺ ys′ = f x y ≺ zipWith f xs′ ys′
whnf (map f xs)        with whnf xs
whnf (map f xs)        | x ≺ xs′ = f x ≺ map f xs′
whnf (merge cmp xs ys) with whnf xs | whnf ys
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ with cmp x y
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | lt = x ≺ merge cmp xs′ ys
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | eq = x ≺ merge cmp xs′ ys′
whnf (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | gt = y ≺ merge cmp xs  ys′

mutual

  value : ∀ {A} → WHNF A → Stream A
  value (x ≺ xs) = x ≺ value′ where value′ ~ ♯ ⟦ xs ⟧

  ⟦_⟧ : ∀ {A} → Prog A → Stream A
  ⟦ xs ⟧ = value (whnf xs)

------------------------------------------------------------------------
-- Examples

fib : Prog ℕ
fib = 0 ≺ fib′
  where fib′ ~ ♯₁ zipWith _+_ fib (1 ≺ ♯₁ fib)

hamming : Prog ℕ
hamming = 1 ≺ hamming′
  where
  hamming′ ~ ♯₁ merge cmp (map (_*_ 2) hamming) (map (_*_ 3) hamming)
    where
    toOrd : ∀ {m n} → Ordering m n → Ord
    toOrd (less _ _)    = lt
    toOrd (equal _)     = eq
    toOrd (greater _ _) = gt

    cmp : ℕ → ℕ → Ord
    cmp m n = toOrd (compare m n)

main = IO.run (S.putStream (S._⋎_ ⟦ fib ⟧ ⟦ hamming ⟧))
