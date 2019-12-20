------------------------------------------------------------------------
-- An implementation of the Thue-Morse sequence
------------------------------------------------------------------------

-- This module is a variant of ThueMorse. The difference is that, in
-- this module, the cast operation takes an inequality instead of an
-- equality, and that this module does not contain any correctness
-- proofs.

module ThueMorseLeq where

open import Codata.Musical.Notation
open import Codata.Musical.Stream using (Stream; _≈_)
open Codata.Musical.Stream.Stream
open import Data.Bool using (Bool; not); open Data.Bool.Bool
open import Data.Nat using (ℕ); open Data.Nat.ℕ
open import Data.Vec using (Vec; _∷ʳ_); open Data.Vec.Vec

------------------------------------------------------------------------
-- Chunks

-- A value of type Chunks describes how a stream is generated. Note
-- that an infinite sequence of empty chunks is not allowed.

data Chunks : Set where
  -- Start the next chunk.
  next : (m :   Chunks) → Chunks
  -- Cons an element to the current chunk.
  cons : (m : ∞ Chunks) → Chunks

-- Inequality of chunks.

infix 4 _≥C_

data _≥C_ : Chunks → Chunks → Set where
  next  : ∀ {m m′} (m≥m′ :      m ≥C   m′ ) → next m ≥C next m′
  cons  : ∀ {m m′} (m≥m′ : ∞ (♭ m ≥C ♭ m′)) → cons m ≥C cons m′
  consˡ : ∀ {m m′} (m≥m′ :    ♭ m ≥C   m′ ) → cons m ≥C      m′

------------------------------------------------------------------------
-- Chunk transformers

tailC : Chunks → Chunks
tailC (next m) = next (tailC m)
tailC (cons m) = ♭ m

mutual

  evensC : Chunks → Chunks
  evensC (next m) = next (evensC m)
  evensC (cons m) = cons (♯ oddsC (♭ m))

  oddsC : Chunks → Chunks
  oddsC (next m) = next (oddsC m)
  oddsC (cons m) = evensC (♭ m)

infixr 5 _⋎C_

-- Note that care is taken to create as few and large chunks as
-- possible (see also _⋎W_).

_⋎C_ : Chunks → Chunks → Chunks
next m ⋎C next m′ = next (m ⋎C      m′)   -- Two chunks in, one out.
next m ⋎C cons m′ = next (m ⋎C cons m′)
cons m ⋎C      m′ = cons (♯ (m′ ⋎C ♭ m))

------------------------------------------------------------------------
-- Stream programs

-- StreamP m A encodes programs which generate streams with chunk
-- sizes given by m.

infixr 5 _∷_ _⋎_

data StreamP : Chunks → Set → Set₁ where
  [_]     : ∀ {m A} (xs : ∞ (StreamP m A)) → StreamP (next m) A
  _∷_     : ∀ {m A} (x : A) (xs : StreamP (♭ m) A) → StreamP (cons m) A
  tail    : ∀ {m A} (xs : StreamP m A) → StreamP (tailC m) A
  evens   : ∀ {m A} (xs : StreamP m A) → StreamP (evensC m) A
  odds    : ∀ {m A} (xs : StreamP m A) → StreamP (oddsC m) A
  _⋎_     : ∀ {m m′ A} (xs : StreamP m A) (ys : StreamP m′ A) →
            StreamP (m ⋎C m′) A
  map     : ∀ {m A B} (f : A → B) (xs : StreamP m A) → StreamP m B
  cast    : ∀ {m m′ A} (ok : m ≥C m′) (xs : StreamP m A) → StreamP m′ A

data StreamW : Chunks → Set → Set₁ where
  [_] : ∀ {m A} (xs : StreamP m A) → StreamW (next m) A
  _∷_ : ∀ {m A} (x : A) (xs : StreamW (♭ m) A) → StreamW (cons m) A

program : ∀ {m A} → StreamW m A → StreamP m A
program [ xs ]   = [ ♯ xs ]
program (x ∷ xs) = x ∷ program xs

tailW : ∀ {m A} → StreamW m A → StreamW (tailC m) A
tailW [ xs ]   = [ tail xs ]
tailW (x ∷ xs) = xs

mutual

  evensW : ∀ {m A} → StreamW m A → StreamW (evensC m) A
  evensW [ xs ]   = [ evens xs ]
  evensW (x ∷ xs) = x ∷ oddsW xs

  oddsW : ∀ {m A} → StreamW m A → StreamW (oddsC m) A
  oddsW [ xs ]   = [ odds xs ]
  oddsW (x ∷ xs) = evensW xs

infixr 5 _⋎W_

-- Note: Uses swapping of arguments.

_⋎W_ : ∀ {m m′ A} → StreamW m A → StreamW m′ A → StreamW (m ⋎C m′) A
[ xs ]   ⋎W [ ys ]   = [ xs ⋎ ys ]
[ xs ]   ⋎W (y ∷ ys) = [ xs ⋎ program (y ∷ ys) ]
(x ∷ xs) ⋎W ys       = x ∷ ys ⋎W xs

mapW : ∀ {m A B} → (A → B) → StreamW m A → StreamW m B
mapW f [ xs ]   = [ map f xs ]
mapW f (x ∷ xs) = f x ∷ mapW f xs

module Cast where

  infixr 6 _+_
  infixr 5 _++_

  _+_ : ℕ → Chunks → Chunks
  zero  + m = m
  suc n + m = cons (♯ (n + m))

  _++_ : ∀ {A n m} → Vec A n → StreamP m A → StreamP (n + m) A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  +ˡ : ∀ {m m′} n → m ≥C m′ → n + m ≥C m′
  +ˡ zero    m≥m′ = m≥m′
  +ˡ (suc n) m≥m′ = consˡ (+ˡ n m≥m′)

  castW : ∀ {n m m′ A} → m ≥C m′ → Vec A n → StreamW m A → StreamW m′ A
  castW {n} (next  m≥m′) xs       [ ys ]   = [ cast (+ˡ n m≥m′) (xs ++ ys) ]
  castW     (cons  m≥m′) []       (y ∷ ys) = y ∷ castW (♭ m≥m′) []        ys
  castW     (cons  m≥m′) (x ∷ xs) (y ∷ ys) = x ∷ castW (♭ m≥m′) (xs ∷ʳ y) ys
  castW     (consˡ m≥m′) xs       (y ∷ ys) = castW m≥m′ (xs ∷ʳ y) ys

whnf : ∀ {m A} → StreamP m A → StreamW m A
whnf [ xs ]         = [ ♭ xs ]
whnf (x ∷ xs)       = x ∷ whnf xs
whnf (tail xs)      = tailW (whnf xs)
whnf (evens xs)     = evensW (whnf xs)
whnf (odds xs)      = oddsW (whnf xs)
whnf (xs ⋎ ys)      = whnf xs ⋎W whnf ys
whnf (map f xs)     = mapW f (whnf xs)
whnf (cast m≥m′ xs) = Cast.castW m≥m′ [] (whnf xs)

mutual

  ⟦_⟧W : ∀ {m A} → StreamW m A → Stream A
  ⟦ [ xs ] ⟧W = ⟦ xs ⟧P
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧W

  ⟦_⟧P : ∀ {m A} → StreamP m A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- The Thue-Morse sequence

[ccn]ω : Chunks
[ccn]ω = cons (♯ cons (♯ next [ccn]ω))

[cn]²[ccn]ω : Chunks
[cn]²[ccn]ω = cons (♯ next (cons (♯ next [ccn]ω)))

[cn]³[ccn]ω : Chunks
[cn]³[ccn]ω = cons (♯ next [cn]²[ccn]ω)

lemma₁ : oddsC [ccn]ω ⋎C [ccn]ω ≥C [ccn]ω
lemma₁ = cons (♯ cons (♯ next (cons (♯ cons (♯ next lemma₁)))))

lemma : evensC [cn]³[ccn]ω ⋎C tailC [cn]³[ccn]ω ≥C [cn]²[ccn]ω
lemma = cons (♯ next (cons (♯ next (cons (♯ cons (♯ next lemma₁))))))

thueMorse : StreamP [cn]³[ccn]ω Bool
thueMorse =
  false ∷ [ ♯ cast lemma (map not (evens thueMorse) ⋎ tail thueMorse) ]
