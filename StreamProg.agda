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

------------------------------------------------------------------------
-- Stream programs

data Ord : Set where
  lt : Ord
  eq : Ord
  gt : Ord

infixr 5 _≺_
infix  4 ↓_

mutual

  data Stream′ A : Set1 where
    _≺_ : (x : A) (xs : ∞₁ (StreamProg A)) → Stream′ A

  data StreamProg (A : Set) : Set1 where
    ↓_      : (xs : Stream′ A) → StreamProg A
    zipWith : ∀ {B C} (f : B → C → A)
              (xs : StreamProg B) (ys : StreamProg C) → StreamProg A
    map     : ∀ {B} (f : B → A) (xs : StreamProg B) → StreamProg A
    merge   : (cmp : A → A → Ord)
              (xs : StreamProg A) (ys : StreamProg A) → StreamProg A

P⇒′ : ∀ {A} → StreamProg A → Stream′ A
P⇒′ (↓ xs)            = xs
P⇒′ (zipWith f xs ys) with P⇒′ xs | P⇒′ ys
P⇒′ (zipWith f xs ys) | x ≺ xs′ | y ≺ ys′ = f x y ≺ ♯₁ zipWith f (♭₁ xs′) (♭₁ ys′)
P⇒′ (map f xs)        with P⇒′ xs
P⇒′ (map f xs)        | x ≺ xs′ = f x ≺ ♯₁ map f (♭₁ xs′)
P⇒′ (merge cmp xs ys) with P⇒′ xs | P⇒′ ys
P⇒′ (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ with cmp x y
P⇒′ (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | lt = x ≺ ♯₁ merge cmp (♭₁ xs′)     ys
P⇒′ (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | eq = x ≺ ♯₁ merge cmp (♭₁ xs′) (♭₁ ys′)
P⇒′ (merge cmp xs ys) | x ≺ xs′ | y ≺ ys′ | gt = y ≺ ♯₁ merge cmp     xs   (♭₁ ys′)

mutual

  ′⇒ : ∀ {A} → Stream′ A → Stream A
  ′⇒ (x ≺ xs) = x ≺ ′⇒′ where ′⇒′ ~ ♯ P⇒ (♭₁ xs)

  P⇒ : ∀ {A} → StreamProg A → Stream A
  P⇒ xs = ′⇒ (P⇒′ xs)

------------------------------------------------------------------------
-- Lifting of stream program transformers into functions on streams

⇒P : ∀ {A} → Stream A → StreamProg A
⇒P (x ≺ xs) = ↓ x ≺ ⇒P′ where ⇒P′ ~ ♯₁ ⇒P (♭ xs)

lift : ∀ {A B} →
       (StreamProg A → StreamProg B) → Stream A → Stream B
lift f xs = P⇒ (f (⇒P xs))

------------------------------------------------------------------------
-- Examples

fib : StreamProg ℕ
fib = ↓ 0 ≺ fib′
  where fib′ ~ ♯₁ zipWith _+_ fib (↓ 1 ≺ ♯₁ fib)

hamming : StreamProg ℕ
hamming = ↓ 1 ≺ hamming′
  where
  hamming′ ~ ♯₁ merge cmp (map (_*_ 2) hamming) (map (_*_ 3) hamming)
    where
    toOrd : ∀ {m n} → Ordering m n → Ord
    toOrd (less _ _)    = lt
    toOrd (equal _)     = eq
    toOrd (greater _ _) = gt

    cmp : ℕ → ℕ → Ord
    cmp m n = toOrd (compare m n)

main = S.putStream (S._⋎_ (P⇒ fib) (P⇒ hamming))
