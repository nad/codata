------------------------------------------------------------------------
-- Instantiation of Contractive for functions
------------------------------------------------------------------------

-- Taken from the paper.

open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Contractive
open import Level

module Contractive.Function
         {A B : Set}
         {_<_ : Rel A zero}
         (isWFO : IsWellFoundedOrder _<_)
         (dec : Decidable _<_)
         (proof-irrelevance :
            ∀ {a a'} (p₁ p₂ : a < a') → p₁ ≡ p₂)
         where

open import Relation.Nullary
open import Relation.Unary
open import Data.Empty

ofe : OFE
ofe = record
  { Carrier            = A
  ; Domain             = A → B
  ; _<_                = _<_
  ; isWellFoundedOrder = isWFO
  ; Eq                 = λ a f g → f a ≡ g a
  ; isEquivalence      = λ _ → record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }

open OFE ofe hiding (_<_)

private

  limU : (A → (A → B)) → A → B
  limU f a' = f a' a'

  lim↓ : B → ∀ a → (∀ x → x < a → A → B) → A → B
  lim↓ b a f a' with dec a' a
  lim↓ b a f a' | yes a'<a = f a' a'<a a'
  lim↓ b a f a' | no  a'≮a = b

  isLimit↓ : ∀ b a {fam : Family (↓ a)} →
             IsCoherent fam → IsLimit fam (lim↓ b a fam)
  isLimit↓ b a {fam} coh {a'} a'<a with dec a' a
  isLimit↓ b a {fam} coh {a'} a'<a | no  a'≮a  = ⊥-elim (a'≮a a'<a)
  isLimit↓ b a {fam} coh {a'} a'<a | yes a'<a₂ =
    cong (λ p → fam a' p a') (proof-irrelevance a'<a a'<a₂)

-- The paper implicitly assumes that B is non-empty.

cofe : B → COFE
cofe b = record
  { ofe      = ofe
  ; limU     = limU
  ; isLimitU = λ _ _ → refl
  ; lim↓     = lim↓ b
  ; isLimit↓ = isLimit↓ b
  }
