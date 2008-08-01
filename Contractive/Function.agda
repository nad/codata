------------------------------------------------------------------------
-- Instantiation of Contractive for functions
------------------------------------------------------------------------

-- Taken from the paper.

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Contractive

module Contractive.Function
         {A B : Set}
         {_<_ : Rel A}
         (isWFO : IsWellFoundedOrder _<_)
         (dec : Decidable _<_)
         (proof-irrelevance :
            forall {a a'} (p₁ p₂ : a < a') -> p₁ ≡ p₂)
         where

open import Relation.Nullary
open import Relation.Unary
open import Data.Empty

ofe : OFE
ofe                    = record
  { carrier            = A
  ; domain             = A -> B
  ; _<_                = _<_
  ; isWellFoundedOrder = isWFO
  ; Eq                 = \a f g -> f a ≡ g a
  ; isEquivalence      = \a -> record
    { refl  = ≡-refl
    ; sym   = ≡-sym
    ; trans = ≡-trans
    }
  }

open OFE ofe

private

  limU : (A -> (A -> B)) -> A -> B
  limU f a' = f a' a'

  lim↓ : B -> forall a -> (forall x -> x < a -> A -> B) -> A -> B
  lim↓ b a f a' with dec a' a
  lim↓ b a f a' | yes a'<a = f a' a'<a a'
  lim↓ b a f a' | no  a'≮a = b

  isLimit↓ : forall b a {fam : Family (↓ a)} ->
             IsCoherent fam -> IsLimit fam (lim↓ b a fam)
  isLimit↓ b a {fam} coh {a'} a'<a with dec a' a
  isLimit↓ b a {fam} coh {a'} a'<a | no  a'≮a  = ⊥-elim (a'≮a a'<a)
  isLimit↓ b a {fam} coh {a'} a'<a | yes a'<a₂ =
    ≡-cong (\p -> fam a' p a') (proof-irrelevance a'<a a'<a₂)

-- The paper implicitly assumes that B is non-empty.

cofe : B -> COFE
cofe b = record
  { ofe      = ofe
  ; limU     = limU
  ; isLimitU = \_ _ -> ≡-refl
  ; lim↓     = lim↓ b
  ; isLimit↓ = isLimit↓ b
  }
