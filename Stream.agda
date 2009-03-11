module Stream where

open import Coinduction
open import Data.Nat
open import Data.Nat.Show
open import Data.Function
open import Data.Unit
open import Relation.Binary.PropositionalEquality
import IO; open IO using (IO)

------------------------------------------------------------------------
-- Streams

import Data.Stream as Stream
open Stream public hiding (lookup) renaming (_∷_ to _≺_)

infixl 4 _!_

_!_ : ∀ {A} → Stream A → ℕ → A
_!_ = flip Stream.lookup

data Ord : Set where
  lt : Ord
  eq : Ord
  gt : Ord

merge : ∀ {A} → (A → A → Ord) → Stream A → Stream A → Stream A
merge cmp (x ≺ xs) (y ≺ ys) with cmp x y
merge cmp (x ≺ xs) (y ≺ ys) | lt = x ≺ ♯ merge cmp (♭ xs)   (y ≺ ys)
merge cmp (x ≺ xs) (y ≺ ys) | eq = x ≺ ♯ merge cmp (♭ xs)   (♭ ys)
merge cmp (x ≺ xs) (y ≺ ys) | gt = y ≺ ♯ merge cmp (x ≺ xs) (♭ ys)

------------------------------------------------------------------------
-- Outputting streams

putStream : Stream ℕ → IO ⊤
putStream xs = IO.mapM′ IO.putStrLn (toColist $ map show xs)
