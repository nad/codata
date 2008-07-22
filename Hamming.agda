------------------------------------------------------------------------
-- An ad-hoc but straightforward solution to the problem of showing
-- that an elegant definition of the Hamming numbers (see EWD 792) is
-- productive
------------------------------------------------------------------------

module Hamming where

data Ordering : Set where
  lt : Ordering
  eq : Ordering
  gt : Ordering

infixr 5 _∷_
infix  4 ↓_

codata Stream A : Set where
  _∷_ : (x : A) (xs : Stream A) -> Stream A

mutual

  codata Stream′ A : Set1 where
    _∷_ : (x : A) (xs : Stream″ A) -> Stream′ A

  data Stream″ (A : Set) : Set1 where
    ↓_    : (xs : Stream′ A) -> Stream″ A
    map   : forall {B} (f : B -> A) (xs : Stream″ B) -> Stream″ A
    merge : (cmp : A -> A -> Ordering) (xs ys : Stream″ A) -> Stream″ A

″⇒′ : forall {A} -> Stream″ A -> Stream′ A
″⇒′ (↓ xs)            = xs
″⇒′ (map f xs)        with ″⇒′ xs
″⇒′ (map f xs)        | x ∷ xs' = f x ∷ map f xs'
″⇒′ (merge cmp xs ys) with ″⇒′ xs | ″⇒′ ys
″⇒′ (merge cmp xs ys) | x ∷ xs' | y ∷ ys' with cmp x y
″⇒′ (merge cmp xs ys) | x ∷ xs' | y ∷ ys' | lt = x ∷ merge cmp xs' ys
″⇒′ (merge cmp xs ys) | x ∷ xs' | y ∷ ys' | eq = x ∷ merge cmp xs' ys'
″⇒′ (merge cmp xs ys) | x ∷ xs' | y ∷ ys' | gt = y ∷ merge cmp xs  ys'

mutual

  ′⇒ : forall {A} -> Stream′ A -> Stream A
  ′⇒ (x ∷ xs) ~ x ∷ ″⇒ xs

  ″⇒ : forall {A} -> Stream″ A -> Stream A
  ″⇒ xs ~ ′⇒ (″⇒′ xs)

⇒′ : forall {A} -> Stream A -> Stream′ A
⇒′ (x ∷ xs) ~ x ∷ (↓ ⇒′ xs)

open import Data.Nat renaming (Ordering to Ord)

forget : forall {m n} -> Ord m n -> Ordering
forget (less _ _)    = lt
forget (equal _)     = eq
forget (greater _ _) = gt

cmp : ℕ -> ℕ -> Ordering
cmp m n = forget (compare m n)

hamming″ : Stream″ ℕ
hamming″ ~ ↓ 1 ∷ merge cmp (map (_*_ 2) hamming″) (map (_*_ 3) hamming″)

hamming : Stream ℕ
hamming = ″⇒ hamming″
