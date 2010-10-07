------------------------------------------------------------------------
-- An implementation of the Thue-Morse sequence
------------------------------------------------------------------------

-- This module is a variant of ThueMorse. The difference is that, in
-- this module, the cast operation takes an inequality instead of an
-- equality, and that this module does not contain any correctness
-- proofs.

module ThueMorseLeq where

open import Coinduction
open import Data.Bool using (Bool; not); open Data.Bool.Bool
open import Data.Nat using (ℕ); open Data.Nat.ℕ
open import Data.Stream using (Stream; _≈_); open Data.Stream.Stream
open import Data.Vec using (Vec; _∷ʳ_); open Data.Vec.Vec

------------------------------------------------------------------------
-- Moduli of productivity

-- A modulus describes how a stream is generated. Note that an
-- infinite sequence of empty chunks is not allowed.

data Modulus : Set where
  -- Start the next chunk.
  next : (m :   Modulus) → Modulus
  -- Cons an element to the current chunk.
  cons : (m : ∞ Modulus) → Modulus

-- Inequality of moduli.

infix 4 _≥M_

data _≥M_ : Modulus → Modulus → Set where
  next  : ∀ {m m′} (m≥m′ :      m ≥M   m′ ) → next m ≥M next m′
  cons  : ∀ {m m′} (m≥m′ : ∞ (♭ m ≥M ♭ m′)) → cons m ≥M cons m′
  consˡ : ∀ {m m′} (m≥m′ :    ♭ m ≥M   m′ ) → cons m ≥M      m′

------------------------------------------------------------------------
-- Modulus transformers

tailM : Modulus → Modulus
tailM (next m) = next (tailM m)
tailM (cons m) = ♭ m

mutual

  evensM : Modulus → Modulus
  evensM (next m) = next (evensM m)
  evensM (cons m) = cons (♯ oddsM (♭ m))

  oddsM : Modulus → Modulus
  oddsM (next m) = next (oddsM m)
  oddsM (cons m) = evensM (♭ m)

infixr 5 _⋎M_

-- Note that care is taken to create as few and large chunks as
-- possible (see also _⋎W_).

_⋎M_ : Modulus → Modulus → Modulus
next m ⋎M next m′ = next (m ⋎M      m′)   -- Two chunks in, one out.
next m ⋎M cons m′ = next (m ⋎M cons m′)
cons m ⋎M      m′ = cons (♯ (m′ ⋎M ♭ m))

------------------------------------------------------------------------
-- Stream programs

-- StreamP m A encodes programs which generate streams with chunk
-- sizes given by m.

infixr 5 _∷_ _⋎_

data StreamP : Modulus → Set → Set₁ where
  [_]     : ∀ {m A} (xs : ∞ (StreamP m A)) → StreamP (next m) A
  _∷_     : ∀ {m A} (x : A) (xs : StreamP (♭ m) A) → StreamP (cons m) A
  tail    : ∀ {m A} (xs : StreamP m A) → StreamP (tailM m) A
  evens   : ∀ {m A} (xs : StreamP m A) → StreamP (evensM m) A
  odds    : ∀ {m A} (xs : StreamP m A) → StreamP (oddsM m) A
  _⋎_     : ∀ {m m′ A} (xs : StreamP m A) (ys : StreamP m′ A) →
            StreamP (m ⋎M m′) A
  map     : ∀ {m A B} (f : A → B) (xs : StreamP m A) → StreamP m B
  cast    : ∀ {m m′ A} (ok : m ≥M m′) (xs : StreamP m A) → StreamP m′ A

data StreamW : Modulus → Set → Set₁ where
  [_] : ∀ {m A} (xs : StreamP m A) → StreamW (next m) A
  _∷_ : ∀ {m A} (x : A) (xs : StreamW (♭ m) A) → StreamW (cons m) A

program : ∀ {m A} → StreamW m A → StreamP m A
program [ xs ]   = [ ♯ xs ]
program (x ∷ xs) = x ∷ program xs

tailW : ∀ {m A} → StreamW m A → StreamW (tailM m) A
tailW [ xs ]   = [ tail xs ]
tailW (x ∷ xs) = xs

mutual

  evensW : ∀ {m A} → StreamW m A → StreamW (evensM m) A
  evensW [ xs ]   = [ evens xs ]
  evensW (x ∷ xs) = x ∷ oddsW xs

  oddsW : ∀ {m A} → StreamW m A → StreamW (oddsM m) A
  oddsW [ xs ]   = [ odds xs ]
  oddsW (x ∷ xs) = evensW xs

infixr 5 _⋎W_

-- Note: Uses swapping of arguments.

_⋎W_ : ∀ {m m′ A} → StreamW m A → StreamW m′ A → StreamW (m ⋎M m′) A
[ xs ]   ⋎W [ ys ]   = [ xs ⋎ ys ]
[ xs ]   ⋎W (y ∷ ys) = [ xs ⋎ program (y ∷ ys) ]
(x ∷ xs) ⋎W ys       = x ∷ ys ⋎W xs

mapW : ∀ {m A B} → (A → B) → StreamW m A → StreamW m B
mapW f [ xs ]   = [ map f xs ]
mapW f (x ∷ xs) = f x ∷ mapW f xs

module Cast where

  infixr 6 _+_
  infixr 5 _++_

  _+_ : ℕ → Modulus → Modulus
  zero  + m = m
  suc n + m = cons (♯ (n + m))

  _++_ : ∀ {A n m} → Vec A n → StreamP m A → StreamP (n + m) A
  []       ++ ys = ys
  (x ∷ xs) ++ ys = x ∷ (xs ++ ys)

  +ˡ : ∀ {m m′} n → m ≥M m′ → n + m ≥M m′
  +ˡ zero    m≥m′ = m≥m′
  +ˡ (suc n) m≥m′ = consˡ (+ˡ n m≥m′)

  castW : ∀ {n m m′ A} → m ≥M m′ → Vec A n → StreamW m A → StreamW m′ A
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
whnf (cast m≈m′ xs) = Cast.castW m≈m′ [] (whnf xs)

mutual

  ⟦_⟧W : ∀ {m A} → StreamW m A → Stream A
  ⟦ [ xs ] ⟧W = ⟦ xs ⟧P
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧W

  ⟦_⟧P : ∀ {m A} → StreamP m A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- The Thue-Morse sequence

thueMorseM₂ : Modulus
thueMorseM₂ = cons (♯ cons (♯ next thueMorseM₂))

thueMorseM₁ : Modulus
thueMorseM₁ = cons (♯ next (cons (♯ next thueMorseM₂)))

thueMorseM : Modulus
thueMorseM = cons (♯ next thueMorseM₁)

lemma₁ : oddsM thueMorseM₂ ⋎M thueMorseM₂ ≥M thueMorseM₂
lemma₁ = cons (♯ cons (♯ next (cons (♯ cons (♯ next lemma₁)))))

lemma : evensM thueMorseM ⋎M tailM thueMorseM ≥M thueMorseM₁
lemma = cons (♯ next (cons (♯ next (cons (♯ cons (♯ next lemma₁))))))

thueMorse : StreamP thueMorseM Bool
thueMorse =
  false ∷ [ ♯ cast lemma (map not (evens thueMorse) ⋎ tail thueMorse) ]
