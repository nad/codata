module Stream where

open import Data.Vec hiding (take; drop; map)
open import Data.Unit
open import Data.Nat
open import Data.Nat.Show
open import Data.Colist hiding (take)
import Data.String as S
open import Data.Function
open import IO

codata Stream A : Set where
  _∷_ : (x : A) (xs : Stream A) -> Stream A

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

toColist : forall {A} -> Stream A -> Colist A
toColist (x ∷ xs) ~ x ∷ toColist xs

-- This definition would be accepted by the termination checker if
-- return and _>>=_ were constructors.

mapM_ : forall {A B} -> (A -> IO B) -> Colist A -> IO Unit
mapM_ f []       ~ return unit
mapM_ f (x ∷ xs) ~ f x >>= \_ -> mapM_ f xs

putStream : Stream ℕ -> IO Unit
putStream = mapM_ (\s -> putStrLn s) ∘
            toColist ∘
            map (S.toCostring ∘ show)
