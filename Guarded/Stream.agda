------------------------------------------------------------------------
-- An example of how Guarded can be used: Streams
------------------------------------------------------------------------

module Guarded.Stream where

------------------------------------------------------------------------
-- Streams

open import Data.Nat
import Data.Vec as Vec

infixr 5 _∷_

codata Stream (a : Set) : Set where
  _∷_ : a → Stream a → Stream a

take : ∀ {a} n → Stream a → Vec.Vec a n
take zero    _         = Vec.[]
take (suc n) (x ∷ xs)  = Vec._∷_ x (take n xs)

head : ∀ {a} → Stream a → a
head (x ∷ xs) = x

tail : ∀ {a} → Stream a → Stream a
tail (x ∷ xs) = xs

------------------------------------------------------------------------
-- Stream producers

open import Guarded

data StreamProd (a seed : Set) : Guardedness → Set where
  return : ∀ {g} → Stream a → StreamProd a seed g
  _∷_    : ∀ {g} →
           a → StreamProd a seed guarded →
           StreamProd a seed g
  rec    : seed → StreamProd a seed guarded

private
 module Dummy {a seed : Set}
              (step : seed → StreamProd a seed unguarded)
              where

  unguard : StreamProd a seed guarded → StreamProd a seed unguarded
  unguard (return xs) = return xs
  unguard (x ∷ xs)    = x ∷ xs
  unguard (rec x)     = step x

  -- Note that produce is guarded and hence productive. If StreamProd
  -- is always used, rather than Stream, then produce encapsulates all
  -- corecursion for streams.

  produce : StreamProd a seed unguarded → Stream a
  produce (return xs) = xs
  produce (x ∷ xs)    = x ∷ produce (unguard xs)

open Dummy public

smap : ∀ {a s₁ s₂ g} →
       (s₁ → s₂) → StreamProd a s₁ g → StreamProd a s₂ g
smap f (return xs) = return xs
smap f (x ∷ xs)    = x ∷ smap f xs
smap f (rec s)     = rec (f s)

StreamProductive : {a : Set} → Productive
StreamProductive {a} = record
  { T        = Stream a
  ; Producer = StreamProd a
  ; return   = return
  ; rec      = rec
  ; unguard  = unguard
  ; produce  = produce
  ; smap     = smap
  }

------------------------------------------------------------------------
-- Examples

module Examples where

  open import Data.Unit
  open import Data.Product using (_×_; _,_; curry)
  module StreamProductive {a : Set} =
    Productive (StreamProductive {a})
  open StreamProductive using (unfold)

  ones : Stream ℕ
  ones = unfold (λ _ → 1 ∷ rec tt) _

  map : ∀ {a b} → (a → b) → Stream a → Stream b
  map f = unfold (λ xs → f (head xs) ∷ rec (tail xs))

  zip : ∀ {a b} → Stream a → Stream b → Stream (a × b)
  zip = curry (unfold step)
    where
    step : Stream _ × Stream _ → _
    step (x ∷ xs , y ∷ ys) = (x , y) ∷ rec (xs , ys)

  enumFrom : ℕ → Stream ℕ
  enumFrom = unfold (λ n → n ∷ rec (suc n))

  ex₁ : Vec.Vec ℕ _
  ex₁ = take 12 (enumFrom 9)
