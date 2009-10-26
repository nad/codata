------------------------------------------------------------------------
-- This module proves that the parser combinators correspond exactly
-- to decidable predicates of type List Bool → Bool (when the alphabet
-- is Bool)
------------------------------------------------------------------------

-- This result could be generalised to other alphabets.

module TotalParserCombinators.ExpressiveStrength where

open import Coinduction
open import Data.Bool
open import Data.Empty
open import Data.Function
open import Data.List
open import Data.List.Reverse
open import Data.Product
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Nullary.Decidable

import TotalParserCombinators
open TotalParserCombinators Bool _≟_

-- One direction of the correspondence has already been established:
-- For every parser there is an equivalent decidable predicate.

parser⇒pred : ∀ {n} (p : P n) →
              ∃ λ (f : List Bool → Bool) → ∀ s → s ∈ p ⇔ f s ≡ true
parser⇒pred p = (λ s → decToBool (s ∈? p))
              , λ s → (helper₁ s , helper₂ s)
  where
  helper₁ : ∀ s → s ∈ p → decToBool (s ∈? p) ≡ true
  helper₁ s s∈p with s ∈? p
  ... | yes _  = refl
  ... | no s∉p = ⊥-elim (s∉p s∈p)

  helper₂ : ∀ s → decToBool (s ∈? p) ≡ true → s ∈ p
  helper₂ s eq   with s ∈? p
  helper₂ s refl | yes s∈p = s∈p
  helper₂ s ()   | no  _

-- For every decidable predicate there is a corresponding parser.

pred⇒parser : (f : List Bool → Bool) →
              ∃ λ (p : P (f [])) → ∀ s → s ∈ p ⇔ f s ≡ true
pred⇒parser f = (p f , λ s → (p-sound f , p-complete f s))
  where
  extend : ∀ {A B} → (List A → B) → A → (List A → B)
  extend f x = λ xs → f (xs ∷ʳ x)

  accept-if-true : ∀ b → P b
  accept-if-true true  = ε
  accept-if-true false = ∅

  p : (f : List Bool → Bool) → P (f [])
  p f = ⟪ ♯ p (extend f true ) ⟫ · ♯? (tok true )
      ∣ ⟪ ♯ p (extend f false) ⟫ · ♯? (tok false)
      ∣ accept-if-true (f [])

  accept-if-true-sound :
    ∀ b {s} → s ∈ accept-if-true b → s ≡ [] × b ≡ true
  accept-if-true-sound true  ε  = (refl , refl)
  accept-if-true-sound false ()

  accept-if-true-complete : ∀ {b} → b ≡ true → [] ∈ accept-if-true b
  accept-if-true-complete refl = ε

  p-sound : ∀ f {s} → s ∈ p f → f s ≡ true
  p-sound f (∣ʳ s∈) with accept-if-true-sound (f []) s∈
  ... | (refl , eq) = eq
  p-sound f (∣ˡ (∣ˡ (s∈ · t∈))) with cast∈ refl (♭?♯? (f [ true  ])) t∈
  ... | tok = p-sound (extend f true ) s∈
  p-sound f (∣ˡ (∣ʳ (s∈ · t∈))) with cast∈ refl (♭?♯? (f [ false ])) t∈
  ... | tok = p-sound (extend f false) s∈

  p-complete′ : ∀ f {s} → Reverse s → f s ≡ true → s ∈ p f
  p-complete′ f [] eq =
    ∣ʳ {n₁ = false} $ accept-if-true-complete eq
  p-complete′ f (bs ∶ rs ∶ʳ true) eq =
    ∣ˡ {n₁ = false} $ ∣ˡ {n₁ = false} $
      p-complete′ (extend f true ) rs eq ·
      cast∈ refl (sym (♭?♯? (extend f true  []))) tok
  p-complete′ f (bs ∶ rs ∶ʳ false) eq =
    ∣ˡ {n₁ = false} $ ∣ʳ {n₁ = false} $
      p-complete′ (extend f false) rs eq ·
      cast∈ refl (sym (♭?♯? (extend f false []))) tok

  p-complete : ∀ f s → f s ≡ true → s ∈ p f
  p-complete f s eq = p-complete′ f (reverseView s) eq
