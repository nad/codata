------------------------------------------------------------------------
-- Products of productive things
------------------------------------------------------------------------

module Guarded.Product where

open import Guarded
open import Data.Product
open import Data.Function

-- Minor issue (perhaps): Note that sharing might be lost in
-- unguard/produce below.

infixr 5 _⊗_

_⊗_ : (AP BP : Productive) → Productive
AP ⊗ BP = record
  { T        = A.T × B.T
  ; Producer = λ s g → A.Producer s g × B.Producer s g
  ; return   = map A.return B.return
  ; rec      = < A.rec , B.rec >
  ; unguard  = λ step → map (A.unguard (proj₁ ∘ step))
                            (B.unguard (proj₂ ∘ step))
  ; produce  = λ step → map (A.produce (proj₁ ∘ step))
                            (B.produce (proj₂ ∘ step))
  ; smap     = λ f → map (A.smap f) (B.smap f)
  }
  where
  module A = Productive AP
  module B = Productive BP

-- Note that the corecursion of the A.T type is entirely confined to
-- the first component, and similarly for B.T. See onesTwos below. If
-- you want another behaviour, see Guarded.IndexedBy.

module Examples where

  import Guarded.Stream as S
  open S using (_∷_)
  open import Data.Nat
  open import Data.Unit
  open import Relation.Binary.PropositionalEquality
  import Data.Vec as Vec
  open Productive (S.StreamProductive ⊗ S.StreamProductive)

  onesTwos : S.Stream ℕ × S.Stream ℕ
  onesTwos = unfold (λ s → 1 ∷ proj₂ (rec s) , 2 ∷ proj₁ (rec s)) tt

  -- Note that even though proj₂ (rec tt) is used for the first
  -- component, and proj₁ (rec tt) for the second, the ones and twos
  -- still do not interleave. Note that
  --
  --   proj₁ (rec s) = proj₂ (rec s) = S.rec s.
  --
  -- The definition unfolds as follows:
  --
  --   onesTwos
  -- = unfold step tt
  -- = produce step (1 ∷ proj₂ (rec tt) , 2 ∷ proj₁ (rec tt))
  -- = ( S.produce (proj₁ ∘ step) (1 ∷ proj₂ (rec tt))
  --   , S.produce (proj₂ ∘ step) (2 ∷ proj₁ (rec tt)) )
  -- = ( S.produce (proj₁ ∘ step) (1 ∷ S.rec tt)
  --   , S.produce (proj₂ ∘ step) (2 ∷ S.rec tt) )
  -- = ( 1 ∷ S.produce (proj₁ ∘ step) (proj₁ (step (S.rec tt)))
  --   , 2 ∷ S.produce (proj₂ ∘ step) (proj₂ (step (S.rec tt))) )
  -- = ( 1 ∷ S.produce (proj₁ ∘ step) (1 ∷ proj₂ (rec tt))
  --   , 2 ∷ S.produce (proj₂ ∘ step) (2 ∷ proj₁ (rec tt)) )
  -- = ( 1 ∷ 1 ∷ S.produce (proj₁ ∘ step) (1 ∷ proj₂ (rec tt))
  --   , 2 ∷ 2 ∷ S.produce (proj₂ ∘ step) (2 ∷ proj₁ (rec tt)) )
  -- = ( 1 ∷ 1 ∷ 1 ∷ S.produce (proj₁ ∘ step) (1 ∷ proj₂ (rec tt))
  --   , 2 ∷ 2 ∷ 2 ∷ S.produce (proj₂ ∘ step) (2 ∷ proj₁ (rec tt)) )
  -- = ...
  --
  -- Note that the rec in the first component is always instantiated
  -- with (proj₁ (step (S.rec tt))), and similarly for the second
  -- component.

  n = 5

  ex : map {Q = λ _ → Vec.Vec ℕ n} (S.take n) (S.take n) onesTwos ≡
       (Vec.replicate 1 , Vec.replicate 2)
  ex = refl
