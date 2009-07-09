------------------------------------------------------------------------
-- An investigation of nested fixpoints of the form μX.νY.… in Agda
------------------------------------------------------------------------

module MuNu where

open import Coinduction
import Data.Colist as Colist
open import Data.Digit
open import Data.List using (List; _∷_; [])
open import Data.Product
open import Data.Stream
open import Relation.Nullary

-- Christophe Raffalli discusses the type μO. νZ. 0 Z + 1 O in his
-- thesis (read 0 X and 1 X as applications of the constructors 0 and
-- 1 to every element in the type X). This type contains bit sequences
-- of the form (0^⋆1)^⋆0^ω.

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
-- The type O really corresponds to νZ. μO. 0 Z + 1 O, i.e. (1^⋆0)^ω:

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

-- The type Z is (essentially) defined by Z O = ∞ (Z O) + O, and this
-- should be interpreted as Z O = νC.C + O. The type O is in turn
-- (essentially) defined by O = Z O where Z O = ∞ (Z O) + O, which can
-- be rewritten as O = ∞ O + O, and this should be interpreted as
-- O = νC.μI.C + I.
