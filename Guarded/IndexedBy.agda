------------------------------------------------------------------------
-- "Indexing" a productive thing on something
------------------------------------------------------------------------

module Guarded.IndexedBy where

open import Guarded
open import Data.Product
open import Data.Function

_IndexedBy_ : Productive → Set → Productive
Prod IndexedBy Index = record
  { Producer = λ s g → Index → P.Producer (s × Index) g
  ; T        = Index → P.T
  ; return   = λ f x → P.return (f x)
  ; rec      = curry P.rec
  ; unguard  = λ step rhs nt → P.unguard (uncurry step) (rhs nt)
  ; produce  = λ step rhs nt → P.produce (uncurry step) (rhs nt)
  ; smap     = λ f rhs nt → P.smap (map f id) (rhs nt)
  }
  where module P = Productive Prod

module Examples where

  import Guarded.Stream as S
  open S using (_∷_)
  open import Data.Nat
  open import Data.Unit
  open import Data.Bool
  open import Data.Vec as Vec renaming (_∷_ to _::_)
  open import Relation.Binary.PropositionalEquality
  open Productive (S.StreamProductive IndexedBy Bool)

  -- Note that the ones and twos can now be made properly
  -- interleaving. Compare with Guarded.Product.Examples.onesTwos.

  onesTwos : Bool → S.Stream ℕ
  onesTwos = unfold step tt
    where
    step : ⊤ → Bool → S.StreamProd ℕ _ unguarded
    step s false = 1 ∷ rec s true
    step s true  = 2 ∷ rec s false

  alternating : ∀ n → Vec ℕ (n * 2)
  alternating zero    = []
  alternating (suc n) = 1 :: 2 :: alternating n

  n = 3

  ex : S.take (n * 2)
         (S.Examples.zip (onesTwos false) (onesTwos true)) ≡
       Vec.zip (alternating n) (tail (alternating n) ++ 1 :: [])
  ex = refl
