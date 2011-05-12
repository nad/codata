------------------------------------------------------------------------
-- By indexing the program and WHNF types on a universe one can handle
-- several types at the same time
------------------------------------------------------------------------

module UniverseIndex where

open import Coinduction
open import Data.Product
open import Data.Stream

infixr 5 _∷_
infixr 4 _,_

data U : Set₁ where
  lift    : Set → U
  stream  : U → U
  product : U → U → U

El : U → Set
El (lift A)      = A
El (stream a)    = Stream (El a)
El (product a b) = El a × El b

data ElP : U → Set₁ where
  interleave : ∀ {a} → ElP (stream a) → ElP (stream a) → ElP (stream a)
  fst        : ∀ {a b} → ElP (product a b) → ElP a
  snd        : ∀ {a b} → ElP (product a b) → ElP b

data ElW : U → Set₁ where
  _∷_  : ∀ {a} → ElW a → ElP (stream a) → ElW (stream a)
  _,_  : ∀ {a b} → ElW a → ElW b → ElW (product a b)
  ⌈_⌉  : ∀ {A} → A → ElW (lift A)

interleaveW : ∀ {a} → ElW (stream a) → ElP (stream a) → ElW (stream a)
interleaveW (x ∷ xs) ys = x ∷ interleave ys xs

fstW : ∀ {a b} → ElW (product a b) → ElW a
fstW (x , y) = x

sndW : ∀ {a b} → ElW (product a b) → ElW b
sndW (x , y) = y

whnf : ∀ {a} → ElP a → ElW a
whnf (interleave xs ys) = interleaveW (whnf xs) ys
whnf (fst p)            = fstW (whnf p)
whnf (snd p)            = sndW (whnf p)

mutual

  ⟦_⟧W : ∀ {a} → ElW a → El a
  ⟦ x ∷ xs ⟧W = ⟦ x ⟧W ∷ ♯ ⟦ xs ⟧P
  ⟦ x , y  ⟧W = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦ ⌈ x ⌉  ⟧W = x

  ⟦_⟧P : ∀ {a} → ElP a → El a
  ⟦ p ⟧P = ⟦ whnf p ⟧W
