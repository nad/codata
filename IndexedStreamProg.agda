------------------------------------------------------------------------
-- A variant of StreamProg which allows the use of tail and similar
-- functions, but is more awkward to use and less efficient
------------------------------------------------------------------------

module IndexedStreamProg where

open import Coinduction
import Stream as S
open S using (Stream; _≺_)
open import Data.Nat
import Data.Vec as V
open V using (Vec; []; _∷_)
import IO

------------------------------------------------------------------------
-- Stream programs

data Ord : Set where
  lt : Ord
  eq : Ord
  gt : Ord

infixr 5 _≺≺_
infix  4 ↓_

mutual

  -- Streams generated in chunks of m. A more general variant is also
  -- possible (drop the first index of StreamProg and let _≺≺_ have
  -- type (xs′ : Vec A (suc m)) (xs″ : StreamProg A 0) →
  -- Stream′ A m), but the current indexing scheme may be slightly
  -- easier to understand.

  data Stream′ A m : Set1 where
    _≺≺_ : (xs′ : Vec A m) (xs″ : ∞₁ (StreamProg A m m)) → Stream′ A m

  data StreamProg (A : Set) : ℕ → ℕ → Set1 where
    ↓_      : ∀ {m} (xs : Stream′ A m) → StreamProg A m m
    forget  : ∀ {m n} (xs : StreamProg A m (suc n)) → StreamProg A m n
    _≺_     : ∀ {m n} (x : A) (xs : StreamProg A m n) →
              StreamProg A m (suc n)
    tail    : ∀ {m n} (xs : StreamProg A m (suc n)) → StreamProg A m n
    zipWith : ∀ {m n B C} (f : B → C → A)
              (xs : StreamProg B m n) (ys : StreamProg C m n) →
              StreamProg A m n
    map     : ∀ {m n B}
              (f : B → A) (xs : StreamProg B m n) → StreamProg A m n
    -- The implementation of merge becomes messy if the indices are
    -- more general.
    merge   : (cmp : A → A → Ord)
              (xs : StreamProg A 1 1) (ys : StreamProg A 1 1) →
              StreamProg A 1 1

data Stream″ A m n : Set1 where
  _≺≺_ : (xs′ : Vec A n) (xs″ : StreamProg A m m) → Stream″ A m n

P⇒″ : ∀ {A m n} → StreamProg A m n → Stream″ A m n
P⇒″ (↓ xs′ ≺≺ xs″)    = xs′ ≺≺ ♭₁ xs″
P⇒″ (forget xs)       with P⇒″ xs
P⇒″ (forget xs)       | xs′ ≺≺ xs″ = V.init xs′ ≺≺ forget (V.last xs′ ≺ xs″)
P⇒″ (x ≺ xs)          with P⇒″ xs
P⇒″ (x ≺ xs)          | xs′ ≺≺ xs″ = (x ∷ xs′) ≺≺ xs″
P⇒″ (tail xs)         with P⇒″ xs
P⇒″ (tail xs)         | xs′ ≺≺ xs″ = V.tail xs′ ≺≺ xs″
P⇒″ (zipWith f xs ys) with P⇒″ xs | P⇒″ ys
P⇒″ (zipWith f xs ys) | xs′ ≺≺ xs″ | ys′ ≺≺ ys″ =
  V.zipWith f xs′ ys′ ≺≺ zipWith f xs″ ys″
P⇒″ (map f xs)        with P⇒″ xs
P⇒″ (map f xs)        | xs′ ≺≺ xs″ = V.map f xs′ ≺≺ map f xs″
P⇒″ (merge cmp xs ys) with P⇒″ xs | P⇒″ ys
P⇒″ (merge cmp xs ys) | (x ∷ []) ≺≺ xs″ | (y ∷ []) ≺≺ ys″ with cmp x y
... | lt = (x ∷ []) ≺≺ merge cmp xs″ (forget (y ≺ ys″))
... | eq = (x ∷ []) ≺≺ merge cmp xs″ ys″
... | gt = (y ∷ []) ≺≺ merge cmp (forget (x ≺ xs″)) ys″

mutual

  ″⇒ : ∀ {A m n} → Stream″ A (suc m) (suc n) → Stream A
  ″⇒ ((x ∷ [])        ≺≺ ys) = x ≺ ″⇒′ where ″⇒′ ~ ♯ P⇒ ys
  ″⇒ ((x ∷ (x' ∷ xs)) ≺≺ ys) = x ≺ (♯ ″⇒ ((x' ∷ xs) ≺≺ ys))

  P⇒ : ∀ {A m n} → StreamProg A (suc m) (suc n) → Stream A
  P⇒ xs = ″⇒ (P⇒″ xs)

------------------------------------------------------------------------
-- Lifting of stream program transformers into functions on streams

⇒P : ∀ {A} n → Stream A → StreamProg A n n
⇒P n xs = ↓ S.take n xs ≺≺ ⇒P′ where ⇒P′ ~ ♯₁ ⇒P n (S.drop n xs)

lift : ∀ {i j k A B} →
       (StreamProg A i i → StreamProg B (suc j) (suc k)) →
       Stream A → Stream B
lift f xs = P⇒ (f (⇒P _ xs))

------------------------------------------------------------------------
-- Examples

-- Note that for every cycle another instance of forget is applied, so
-- after a while there will be a large number of forgets in the
-- unevaluated thunk. However, there will also be a large number of
-- _+_'s, so the forgets shouldn't change the asymptotic complexity of
-- the code. On the other hand, the asymptotic performance of merge
-- (defined above) is likely to be affected by the presence of the
-- forgets.

fib : StreamProg ℕ 1 1
fib = ↓ (0 ∷ []) ≺≺ fib′
  where fib′ ~ ♯₁ 1 ≺ zipWith _+_ (forget fib) (tail fib)

hamming : StreamProg ℕ 1 1
hamming = ↓ (1 ∷ []) ≺≺ hamming′
  where
  hamming′ ~ ♯₁ merge cmp (map (_*_ 2) hamming) (map (_*_ 3) hamming)
    where
    toOrd : ∀ {m n} → Ordering m n → Ord
    toOrd (less _ _)    = lt
    toOrd (equal _)     = eq
    toOrd (greater _ _) = gt

    cmp : ℕ → ℕ → Ord
    cmp m n = toOrd (compare m n)

main = IO.run (S.putStream (S._⋎_ (P⇒ fib) (P⇒ hamming)))
