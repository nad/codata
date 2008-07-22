module Stream where

open import Data.Unit
open import Data.Nat
open import Data.Nat.Show
open import Data.Colist
import Data.String as S
open import Data.Function
open import IO

infixr 5 _∷_

codata Stream A : Set where
  _∷_ : (x : A) (xs : Stream A) -> Stream A

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
