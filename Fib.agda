module Fib where

open import Stream
open import Data.Nat
import Data.Vec as V
open V using (Vec; []; _∷_)
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Data.Nat.Properties
open ℕ-semiringSolver
open import Data.Fin
open import Algebra.Structures

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
    _++_    : forall {m n} (xs : Vec A m) (ys : StreamProg A n) ->
              StreamProg A (m + n)
    tail    : forall {n} (xs : StreamProg A (suc n)) -> StreamProg A n
    zipWith : forall {m n B C}
              (f : B -> C -> A)
              (xs : StreamProg B m) (ys : StreamProg C n) ->
              StreamProg A (m ⊓ n)

zipWith' : forall {A B C m n} ->
           (A -> B -> C) -> Vec A m -> Vec B n ->
           Vec C (m ⊓ n) × Vec A (m ∸ n) × Vec B (n ∸ m)
zipWith' f []       []       = ([] , [] , [])
zipWith' f []       (y ∷ ys) = ([] , [] , y ∷ ys)
zipWith' f (x ∷ xs) []       = ([] , x ∷ xs , [])
zipWith' f (x ∷ xs) (y ∷ ys) with zipWith' f xs ys
zipWith' f (x ∷ xs) (y ∷ ys) | (fxsys , xs′ , ys′) = (f x y ∷ fxsys , xs′ , ys′)

lemma₁ : forall m n -> m + suc n ≡ suc (m + n)
lemma₁ m n = prove (m ∷ (n ∷ []))
                   (M :+ (con 1 :+ N)) (con 1 :+ M :+ N)
                   ≡-refl
  where M = var zero; N = var (suc zero)

lemma₂ : forall m n -> (m ∸ n + 0) ⊓ (n ∸ m + 0) ≡ 0
lemma₂ m n with m ∸ n + 0 | proj₂ +-identity (m ∸ n)
              | n ∸ m + 0 | proj₂ +-identity (n ∸ m)
  where open IsCommutativeSemiring _ ℕ-isCommutativeSemiring
lemma₂ m n | .(m ∸ n) | ≡-refl | .(n ∸ m) | ≡-refl = [m∸n]⊓[n∸m]≡0 m n

P⇒′ : forall {A n} -> StreamProg A n -> Stream′ A n
P⇒′ (↓ xs)            = xs
P⇒′ (x ∷ xs)          with P⇒′ xs
P⇒′ (x ∷ xs)          | xs′ ++ ys = (x ∷ xs′) ++ ys
P⇒′ (xs ++ ys)        with P⇒′ ys
P⇒′ (_++_ {m} xs ys)  | _++_ {n} ys′ ys″ = cast (V._++_ xs ys′) ++ ys″
  where cast = ≡-subst (Vec _) (lemma₁ m n)
P⇒′ (tail xs)         with P⇒′ xs
P⇒′ (tail xs)         | (x ∷ xs′) ++ ys = xs′ ++ ys
P⇒′ (zipWith f xs ys) with P⇒′ xs | P⇒′ ys
P⇒′ (zipWith f xs ys) | _++_ {m} xs′ xs″ | _++_ {n} ys′ ys″ with zipWith' f xs′ ys′
P⇒′ (zipWith f xs ys) | _++_ {m} xs′ xs″ | _++_ {n} ys′ ys″ | (fxys , xs‴ , ys‴) =
  fxys ++ cast (zipWith f (xs‴ ++ xs″) (ys‴ ++ ys″))
  where cast = ≡-subst₁ (StreamProg _) (lemma₂ m n)

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
