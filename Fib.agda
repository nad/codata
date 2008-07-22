module Fib where

open import Stream
open import Data.Nat
import Data.Vec as V
open V using (Vec; []; _∷_)

infixr 5 _++_
infix  4 ↓_

mutual

  codata Stream′ A : ℕ -> Set1 where
    _++_ : forall {n} (xs : Vec A (suc n)) (ys : StreamProg A 0) ->
           Stream′ A n

  data StreamProg (A : Set) : ℕ -> Set1 where
    ↓_      : forall {n} (xs : Stream′ A n) -> StreamProg A n
    _∷_     : forall {n} (x : A) (xs : StreamProg A n) ->
              StreamProg A (suc n)
    tail    : forall {n} (xs : StreamProg A (suc n)) -> StreamProg A n
    zipWith : forall {n B C}
              (f : B -> C -> A)
              (xs : StreamProg B (suc n)) (ys : StreamProg C n) ->
              StreamProg A n

P⇒′ : forall {A n} -> StreamProg A n -> Stream′ A n
P⇒′ (↓ xs) = xs
P⇒′ (x ∷ xs) with P⇒′ xs
P⇒′ (x ∷ xs) | xs′ ++ ys = (x ∷ xs′) ++ ys
P⇒′ (tail xs) with P⇒′ xs
P⇒′ (tail xs) | (x ∷ xs′) ++ ys = xs′ ++ ys
P⇒′ (zipWith f xs ys) with P⇒′ xs | P⇒′ ys
P⇒′ (zipWith f xs ys) | xs′ ++ xs″ | ys′ ++ ys″ =
  V.zipWith f (V.init xs′) ys′ ++ zipWith f (V.last xs′ ∷ xs″) ys″

mutual

  ′⇒ : forall {A n} -> Stream′ A n -> Stream A
  ′⇒ ((x ∷ [])        ++ ys) ~ x ∷ P⇒ ys
  ′⇒ ((x ∷ (x′ ∷ xs)) ++ ys) ~ x ∷ ′⇒ ((x′ ∷ xs) ++ ys)

  P⇒ : forall {A n} -> StreamProg A n -> Stream A
  P⇒ xs ~ ′⇒ (P⇒′ xs)

fibP : StreamProg ℕ 1
fibP ~ ↓ (1 ∷ (1 ∷ [])) ++ zipWith _+_ fibP (tail fibP)

fib : Stream ℕ
fib = P⇒ fibP

main = putStream fib
