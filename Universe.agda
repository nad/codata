------------------------------------------------------------------------
-- By indexing the program and WHNF types on a universe one can handle
-- several types at the same time
------------------------------------------------------------------------

module Universe where

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

data Program : U → Set₁ where
  interleave : ∀ {a} → Program (stream a) → Program (stream a) →
               Program (stream a)
  fst        : ∀ {a b} → Program (product a b) → Program a
  snd        : ∀ {a b} → Program (product a b) → Program b

data WHNF : U → Set₁ where
  _∷_  : ∀ {a} → WHNF a → Program (stream a) → WHNF (stream a)
  _,_  : ∀ {a b} → WHNF a → WHNF b → WHNF (product a b)
  ⌈_⌉  : ∀ {A} → A → WHNF (lift A)

interleaveW : ∀ {a} → WHNF (stream a) → Program (stream a) →
              WHNF (stream a)
interleaveW (x ∷ xs) ys = x ∷ interleave ys xs

fstW : ∀ {a b} → WHNF (product a b) → WHNF a
fstW (x , y) = x

sndW : ∀ {a b} → WHNF (product a b) → WHNF b
sndW (x , y) = y

whnf : ∀ {a} → Program a → WHNF a
whnf (interleave xs ys) = interleaveW (whnf xs) ys
whnf (fst p)            = fstW (whnf p)
whnf (snd p)            = sndW (whnf p)

mutual

  ⟦_⟧W : ∀ {a} → WHNF a → El a
  ⟦ x ∷ xs ⟧W = ⟦ x ⟧W ∷ ♯ ⟦ xs ⟧P
  ⟦ x , y  ⟧W = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦ ⌈ x ⌉  ⟧W = x

  ⟦_⟧P : ∀ {a} → Program a → El a
  ⟦ p ⟧P = ⟦ whnf p ⟧W
