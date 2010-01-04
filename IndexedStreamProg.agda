------------------------------------------------------------------------
-- A variant of StreamProg which allows the use of tail and similar
-- functions, but is more awkward to use and less efficient
------------------------------------------------------------------------

-- For a potentially better approach, see FibUsingTail.

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

infixr 5 _≺_ _≺≺_

-- Prog A m n encodes programs generating streams in chunks of (at
-- least) m, with (at least) n elements in the first chunk. A more
-- general variant is also possible (drop the first index of Prog and
-- let _≺≺_ have type (xs′ : Vec A (suc m)) (xs″ : Prog A 0) →
-- Prog A m), but the current indexing scheme may be slightly easier
-- to understand.

data Prog (A : Set) : ℕ → ℕ → Set1 where
  _≺≺_    : ∀ {m} (xs′ : Vec A m) (xs″ : ∞ (Prog A m m)) → Prog A m m
  forget  : ∀ {m n} (xs : Prog A m (suc n)) → Prog A m n
  _≺_     : ∀ {m n} (x : A) (xs : Prog A m n) → Prog A m (suc n)
  tail    : ∀ {m n} (xs : Prog A m (suc n)) → Prog A m n
  zipWith : ∀ {m n B C} (f : B → C → A)
            (xs : Prog B m n) (ys : Prog C m n) → Prog A m n
  map     : ∀ {m n B} (f : B → A) (xs : Prog B m n) → Prog A m n
  -- The implementation of merge becomes messy if the indices are
  -- too general.
  merge   : (cmp : A → A → Ord)
            (xs : Prog A 1 1) (ys : Prog A 1 1) → Prog A 1 1

data WHNF A m n : Set1 where
  _≺≺_ : (xs′ : Vec A n) (xs″ : Prog A m m) → WHNF A m n

whnf : ∀ {A m n} → Prog A m n → WHNF A m n
whnf (xs′ ≺≺ xs″)      = xs′ ≺≺ ♭ xs″
whnf (forget xs)       with whnf xs
whnf (forget xs)       | xs′ ≺≺ xs″ = V.init xs′ ≺≺ forget (V.last xs′ ≺ xs″)
whnf (x ≺ xs)          with whnf xs
whnf (x ≺ xs)          | xs′ ≺≺ xs″ = (x ∷ xs′) ≺≺ xs″
whnf (tail xs)         with whnf xs
whnf (tail xs)         | xs′ ≺≺ xs″ = V.tail xs′ ≺≺ xs″
whnf (zipWith f xs ys) with whnf xs | whnf ys
whnf (zipWith f xs ys) | xs′ ≺≺ xs″ | ys′ ≺≺ ys″ =
  V.zipWith f xs′ ys′ ≺≺ zipWith f xs″ ys″
whnf (map f xs)        with whnf xs
whnf (map f xs)        | xs′ ≺≺ xs″ = V.map f xs′ ≺≺ map f xs″
whnf (merge cmp xs ys) with whnf xs | whnf ys
whnf (merge cmp xs ys) | (x ∷ []) ≺≺ xs″ | (y ∷ []) ≺≺ ys″ with cmp x y
... | lt = (x ∷ []) ≺≺ merge cmp xs″ (forget (y ≺ ys″))
... | eq = (x ∷ []) ≺≺ merge cmp xs″ ys″
... | gt = (y ∷ []) ≺≺ merge cmp (forget (x ≺ xs″)) ys″

mutual

  value : ∀ {A m n} → WHNF A (suc m) (suc n) → Stream A
  value ((x ∷ [])        ≺≺ ys) = x ≺ ♯ ⟦ ys ⟧
  value ((x ∷ (x' ∷ xs)) ≺≺ ys) = x ≺ ♯ value ((x' ∷ xs) ≺≺ ys)

  ⟦_⟧ : ∀ {A m n} → Prog A (suc m) (suc n) → Stream A
  ⟦ xs ⟧ = value (whnf xs)

------------------------------------------------------------------------
-- Examples

-- Note that for every cycle another instance of forget is applied, so
-- after a while there will be a large number of forgets in the
-- unevaluated thunk. However, there will also be a large number of
-- _+_'s, so the forgets shouldn't change the asymptotic complexity of
-- the code. On the other hand, the asymptotic performance of merge
-- (defined above) is likely to be affected by the presence of the
-- forgets.

fib : Prog ℕ 1 1
fib = (0 ∷ []) ≺≺ ♯ (1 ≺ zipWith _+_ (forget fib) (tail fib))

hamming : Prog ℕ 1 1
hamming = (1 ∷ []) ≺≺ ♯ merge cmp (map (_*_ 2) hamming)
                                  (map (_*_ 3) hamming)
    where
    toOrd : ∀ {m n} → Ordering m n → Ord
    toOrd (less _ _)    = lt
    toOrd (equal _)     = eq
    toOrd (greater _ _) = gt

    cmp : ℕ → ℕ → Ord
    cmp m n = toOrd (compare m n)

main = IO.run (S.putStream (S._⋎_ ⟦ fib ⟧ ⟦ hamming ⟧))
