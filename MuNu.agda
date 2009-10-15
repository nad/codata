------------------------------------------------------------------------
-- An investigation of nested fixpoints of the form μX.νY.… in Agda
------------------------------------------------------------------------

module MuNu where

open import Coinduction
import Data.Colist as Colist
open import Data.Digit
open import Data.Empty
open import Data.List using (List; _∷_; [])
open import Data.Product
open import Data.Stream
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

-- Christophe Raffalli discusses (essentially) the type μO. νZ. Z + O
-- in his thesis. If Z is read as zero and O as one, then this type
-- contains bit sequences of the form (0^⋆1)^⋆0^ω.

-- It is interesting to note that currently it is not possible to
-- encode this type directly in Agda. One might believe that the
-- following definition should work. First we define the inner
-- greatest fixpoint:

data Z (O : Set) : Set where
  [0] : ∞ (Z O) → Z O
  [1] :    O    → Z O

-- Then we define the outer least fixpoint:

data O : Set where
  ↓ : Z O → O

-- However, it is still possible to define values of the form (01)^ω:

01^ω : O
01^ω = ↓ ([0] (♯ [1] 01^ω))

-- The reason is the way the termination/productivity checker works:
-- it accepts definitions by guarded corecursion as long as the guard
-- contains at least one occurrence of ♯_, no matter how the types
-- involved are defined. In effect ∞ has global reach. The mistake
-- done above was believing that O is defined to be a least fixpoint.
-- The type O really corresponds to νZ. μO. Z + O, i.e. (1^⋆0)^ω:

data O′ : Set where
  [0] : ∞ O′ → O′
  [1] :   O′ → O′

mutual

  O→O′ : O → O′
  O→O′ (↓ z) = ZO→O′ z

  ZO→O′ : Z O → O′
  ZO→O′ ([0] z) = [0] (♯ ZO→O′ (♭ z))
  ZO→O′ ([1] o) = [1] (O→O′ o)

mutual

  O′→O : O′ → O
  O′→O o = ↓ (O′→ZO o)

  O′→ZO : O′ → Z O
  O′→ZO ([0] o) = [0] (♯ O′→ZO (♭ o))
  O′→ZO ([1] o) = [1] (O′→O o)

-- If O had actually encoded the type μO. νZ. Z + O, then we could
-- have proved the following theorem:

mutual

  ⟦_⟧O : O → Stream Bit
  ⟦ ↓ z ⟧O = ⟦ z ⟧Z

  ⟦_⟧Z : Z O → Stream Bit
  ⟦ [0] z ⟧Z = 0b ∷ ♯ ⟦ ♭ z ⟧Z
  ⟦ [1] o ⟧Z = 1b ∷ ♯ ⟦   o ⟧O

Theorem : Set
Theorem = ∀ o → ¬ (head ⟦ o ⟧O ≡ 0b × head (tail ⟦ o ⟧O) ≡ 1b ×
                                      tail (tail ⟦ o ⟧O) ≈ ⟦ o ⟧O)

-- This would have been unfortunate, though:

inconsistency : Theorem → ⊥
inconsistency theorem = theorem 01^ω (refl , refl , proof)
  where
  proof : tail (tail ⟦ 01^ω ⟧O) ≈ ⟦ 01^ω ⟧O
  proof = 0b ∷ ♯ (1b ∷ ♯ proof)

-- Using the following elimination principle we can prove the theorem:

data ⇑ {O} (P : O → Set) : Z O → Set where
  [0] : ∀ {z} → ∞ (⇑ P (♭ z)) → ⇑ P ([0] z)
  [1] : ∀ {o} → P o           → ⇑ P ([1] o)

O-Elim : Set₁
O-Elim = (P : O → Set) → (∀ {z} → ⇑ P z → P (↓ z)) → (o : O) → P o

theorem : O-Elim → Theorem
theorem O-elim = O-elim P helper
  where
  P : O → Set
  P o = ¬ (head ⟦ o ⟧O ≡ 0b × head (tail ⟦ o ⟧O) ≡ 1b ×
                              tail (tail ⟦ o ⟧O) ≈ ⟦ o ⟧O)

  head-cong : ∀ {A} {xs ys : Stream A} → xs ≈ ys → head xs ≡ head ys
  head-cong (x ∷ xs≈) = refl

  tail-cong : ∀ {A} {xs ys : Stream A} → xs ≈ ys → tail xs ≈ tail ys
  tail-cong (x ∷ xs≈) = ♭ xs≈

  helper : ∀ {z} → ⇑ P z → P (↓ z)
  helper ([1] p) (()   , eq₂ , eq₃)
  helper ([0] p) (refl , eq₂ , eq₃) =
    hlp _ eq₂ (head-cong eq₃) (tail-cong eq₃) (♭ p)
    where
    hlp : ∀ z → head ⟦ z ⟧Z ≡ 1b →
                head (tail ⟦ z ⟧Z) ≡ 0b →
                tail (tail ⟦ z ⟧Z) ≈ ⟦ z ⟧Z →
                ⇑ P z → ⊥
    hlp .([0] _) ()  eq₂ eq₃ ([0] p)
    hlp .([1] _) eq₁ eq₂ eq₃ ([1] p) =
      p (eq₂ , head-cong eq₃ , tail-cong eq₃)

-- Fortunately it appears as if we cannot prove this elimination
-- principle. The following code is not accepted by the termination
-- checker:

{-
mutual

  O-elim : O-Elim
  O-elim P hyp (↓ z) = hyp (Z-elim P hyp z)

  Z-elim : (P : O → Set) →
           (∀ {z} → ⇑ P z → P (↓ z)) →
           (z : Z O) → ⇑ P z
  Z-elim P hyp ([0] z) = [0] (♯ Z-elim P hyp (♭ z))
  Z-elim P hyp ([1] o) = [1] (O-elim P hyp o)
-}

-- If hyp were known to be contractive, then the code above would be
-- correct (if not accepted by the termination checker). This is not
-- the case in theorem above.
