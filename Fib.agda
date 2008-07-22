module Fib where

open import Stream
open import Data.Nat
import Data.Vec as V
open V using (Vec; []; _∷_)

infixr 5 _++_
infix  4 ↓_

mutual

  -- Streams generated in chunks of m.

  codata Stream′ A m : Set1 where
    _++_ : (xs′ : Vec A m) (xs″ : StreamProg A m m) -> Stream′ A m

  data StreamProg (A : Set) : ℕ -> ℕ -> Set1 where
    ↓_      : forall {m} (xs : Stream′ A m) -> StreamProg A m m
    forget  : forall {m n}
              (xs : StreamProg A m (suc n)) -> StreamProg A m n
    _∷_     : forall {m n}
              (x : A) (xs : StreamProg A m n) ->
              StreamProg A m (suc n)
    tail    : forall {m n}
              (xs : StreamProg A m (suc n)) -> StreamProg A m n
    zipWith : forall {m n B C}
              (f : B -> C -> A)
              (xs : StreamProg B m n) (ys : StreamProg C m n) ->
              StreamProg A m n

data Stream″ A m n : Set1 where
  _++_ : (xs′ : Vec A n) (xs″ : StreamProg A m m) -> Stream″ A m n

P⇒″ : forall {A m n} -> StreamProg A m n -> Stream″ A m n
P⇒″ (↓ xs′ ++ xs″)    = xs′ ++ xs″
P⇒″ (forget xs)       with P⇒″ xs
P⇒″ (forget xs)       | xs′ ++ xs″ = V.init xs′ ++ forget (V.last xs′ ∷ xs″)
P⇒″ (x ∷ xs)          with P⇒″ xs
P⇒″ (x ∷ xs)          | xs′ ++ xs″ = (x ∷ xs′) ++ xs″
P⇒″ (tail xs)         with P⇒″ xs
P⇒″ (tail xs)         | xs′ ++ xs″ = V.tail xs′ ++ xs″
P⇒″ (zipWith f xs ys) with P⇒″ xs | P⇒″ ys
P⇒″ (zipWith f xs ys) | xs′ ++ xs″ | ys′ ++ ys″ =
  V.zipWith f xs′ ys′ ++ zipWith f xs″ ys″

mutual

  ″⇒ : forall {A m n} -> Stream″ A (suc m) (suc n) -> Stream A
  ″⇒ ((x ∷ [])        ++ ys) ~ x ∷ P⇒ ys
  ″⇒ ((x ∷ (x' ∷ xs)) ++ ys) ~ x ∷ ″⇒ ((x' ∷ xs) ++ ys)

  P⇒ : forall {A m n} -> StreamProg A (suc m) (suc n) -> Stream A
  P⇒ xs ~ ″⇒ (P⇒″ xs)

-- Note that for every cycle another instance of forget is applied, so
-- after a while there will be a large number of forgets in the
-- unevaluated thunk. However, there will also be a large number of
-- _+_'s, so the forgets shouldn't change the asymptotic complexity of
-- the code.

fibP : StreamProg ℕ 1 1
fibP ~ ↓ (1 ∷ []) ++ 1 ∷ zipWith _+_ (forget fibP) (tail fibP)

fib : Stream ℕ
fib = P⇒ fibP

main = putStream fib
