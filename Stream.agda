module Stream where

import Data.Vec as V
open V using (Vec; []; _∷_)
open import Data.Unit
open import Data.Nat
open import Data.Nat.Show
open import Data.Colist hiding (take)
import Data.String as S
open import Data.Function
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import IO

------------------------------------------------------------------------
-- Streams

infixr 5 _∷_

codata Stream A : Set where
  _∷_ : (x : A) (xs : Stream A) -> Stream A

head : forall {A} -> Stream A -> A
head (x ∷ xs) = x

tail : forall {A} -> Stream A -> Stream A
tail (x ∷ xs) = xs

interleave : forall {A} -> Stream A -> Stream A -> Stream A
interleave (x ∷ xs) ys ~ x ∷ interleave ys xs

take : forall {A} n -> Stream A -> Vec A n
take zero    xs       = []
take (suc n) (x ∷ xs) = x ∷ take n xs

drop : forall {A} -> ℕ -> Stream A -> Stream A
drop zero    xs       ~ xs
drop (suc n) (x ∷ xs) ~ drop n xs

map : forall {A B} -> (A -> B) -> Stream A -> Stream B
map f (x ∷ xs) ~ f x ∷ map f xs

zipWith : forall {A B C} ->
          (A -> B -> C) -> Stream A -> Stream B -> Stream C
zipWith _∙_ (x ∷ xs) (y ∷ ys) ~ (x ∙ y) ∷ zipWith _∙_ xs ys

repeat : forall {A} -> A -> Stream A
repeat x ~ x ∷ repeat x

toColist : forall {A} -> Stream A -> Colist A
toColist (x ∷ xs) ~ x ∷ toColist xs

------------------------------------------------------------------------
-- Stream equality

infix 4 _≈_

codata _≈_ {A} (xs ys : Stream A) : Set where
  _∷_ : (x≡ : head xs ≡ head ys) (xs≈ : tail xs ≈ tail ys) -> xs ≈ ys

refl : forall {A} -> Reflexive (_≈_ {A})
refl ~ ≡-refl ∷ refl

sym : forall {A} -> Symmetric (_≈_ {A})
sym (x≡ ∷ xs≈) ~ ≡-sym x≡ ∷ sym xs≈

trans : forall {A} -> Transitive (_≈_ {A})
trans (x≡ ∷ xs≈) (y≡ ∷ ys≈) ~ ≡-trans x≡ y≡ ∷ trans xs≈ ys≈

≈-isEquivalence : forall {A} -> IsEquivalence (_≈_ {A})
≈-isEquivalence {A} = record
  { refl  = refl
  ; sym   = sym
  ; trans = trans
  }

Stream-setoid : Set -> Setoid
Stream-setoid A = record
  { carrier       = Stream A
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

------------------------------------------------------------------------
-- IO

-- This definition would be accepted by the termination checker if
-- return and _>>=_ were constructors.

mapM_ : forall {A B} -> (A -> IO B) -> Colist A -> IO Unit
mapM_ f []       ~ return unit
mapM_ f (x ∷ xs) ~ f x >>= \_ -> mapM_ f xs

putStream : Stream ℕ -> IO Unit
putStream = mapM_ (\s -> putStrLn s) ∘
            toColist ∘
            map (S.toCostring ∘ show)
