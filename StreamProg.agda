------------------------------------------------------------------------
-- An ad-hoc but straightforward solution to the problem of showing
-- that elegant definitions of the Hamming numbers (see EWD 792) and
-- the Fibonacci sequence are productive
------------------------------------------------------------------------

module StreamProg where

import Stream as S
open S using (Stream; _∷_)
open import Data.Nat

------------------------------------------------------------------------
-- Stream programs

data Ord : Set where
  lt : Ord
  eq : Ord
  gt : Ord

infix 4 ↓_

mutual

  codata Stream′ A : Set1 where
    _∷_ : (x : A) (xs : StreamProg A) -> Stream′ A

  data StreamProg (A : Set) : Set1 where
    ↓_      : (xs : Stream′ A) -> StreamProg A
    zipWith : forall {B C}
              (f : B -> C -> A)
              (xs : StreamProg B) (ys : StreamProg C) -> StreamProg A
    map     : forall {B}
              (f : B -> A) (xs : StreamProg B) -> StreamProg A
    merge   : (cmp : A -> A -> Ord)
              (xs : StreamProg A) (ys : StreamProg A) -> StreamProg A

P⇒′ : forall {A} -> StreamProg A -> Stream′ A
P⇒′ (↓ xs)            = xs
P⇒′ (zipWith f xs ys) with P⇒′ xs | P⇒′ ys
P⇒′ (zipWith f xs ys) | x ∷ xs′ | y ∷ ys′ = f x y ∷ zipWith f xs′ ys′
P⇒′ (map f xs)        with P⇒′ xs
P⇒′ (map f xs)        | x ∷ xs′ = f x ∷ map f xs′
P⇒′ (merge cmp xs ys) with P⇒′ xs | P⇒′ ys
P⇒′ (merge cmp xs ys) | x ∷ xs′ | y ∷ ys′ with cmp x y
P⇒′ (merge cmp xs ys) | x ∷ xs′ | y ∷ ys′ | lt = x ∷ merge cmp xs′ ys
P⇒′ (merge cmp xs ys) | x ∷ xs′ | y ∷ ys′ | eq = x ∷ merge cmp xs′ ys′
P⇒′ (merge cmp xs ys) | x ∷ xs′ | y ∷ ys′ | gt = y ∷ merge cmp xs ys′

mutual

  ′⇒ : forall {A} -> Stream′ A -> Stream A
  ′⇒ (x ∷ xs) ~ x ∷ P⇒ xs

  P⇒ : forall {A} -> StreamProg A -> Stream A
  P⇒ xs ~ ′⇒ (P⇒′ xs)

------------------------------------------------------------------------
-- Lifting of stream program transformers into functions on streams

⇒P : forall {A} -> Stream A -> StreamProg A
⇒P (x ∷ xs) ~ ↓ x ∷ ⇒P xs

lift : forall {A B} ->
       (StreamProg A -> StreamProg B) -> Stream A -> Stream B
lift f xs = P⇒ (f (⇒P xs))

------------------------------------------------------------------------
-- Examples

fib : StreamProg ℕ
fib ~ ↓ 0 ∷ zipWith _+_ fib (↓ 1 ∷ fib)

hamming : StreamProg ℕ
hamming ~ ↓ 1 ∷ merge cmp (map (_*_ 2) hamming) (map (_*_ 3) hamming)
  where
  toOrd : forall {m n} -> Ordering m n -> Ord
  toOrd (less _ _)    ~ lt
  toOrd (equal _)     ~ eq
  toOrd (greater _ _) ~ gt

  cmp : ℕ -> ℕ -> Ord
  cmp m n ~ toOrd (compare m n)

main = S.putStream (S.interleave (P⇒ fib) (P⇒ hamming))
