------------------------------------------------------------------------
-- An implementation of "A Unifying Approach to Recursive and
-- Co-recursive Definitions" by Pietro Di Gianantonio and Marino
-- Miculan
------------------------------------------------------------------------

-- See the paper for more explanations.

module Contractive where

open import Relation.Unary
open import Relation.Binary
import Relation.Binary.Reasoning.Setoid as EqR
open import Induction.WellFounded
open import Function
open import Level hiding (lift)

-- Well-founded orders.

record IsWellFoundedOrder {A} (_<_ : Rel A zero) : Set where
  field
    trans         : Transitive _<_
    isWellFounded : WellFounded _<_

-- Ordered families of equivalences.

record OFE : Set1 where
  field
    Carrier            : Set
    Domain             : Set
    _<_                : Rel Carrier zero
    isWellFoundedOrder : IsWellFoundedOrder _<_
    Eq                 : Carrier → Rel Domain zero
    isEquivalence      : ∀ a → IsEquivalence (Eq a)

  open IsWellFoundedOrder isWellFoundedOrder public
  open All isWellFounded public

  setoid : Carrier → Setoid _ _
  setoid a = record { Carrier       = Domain
                    ; _≈_           = Eq a
                    ; isEquivalence = isEquivalence a
                    }

  module EqReasoning {a : Carrier} where
    open EqR    (setoid a) public
    open Setoid (setoid a) public using (refl; sym)

  -- The set of predecessors of a.

  ↓ : Carrier → Carrier → Set
  ↓ a = λ a' → a' < a

  -- The intersection of all the equivalences.

  _≅_ : Rel Domain zero
  x ≅ y = ∀ a → Eq a x y

  Family : (Carrier → Set) → Set
  Family I = ∀ x → x ∈ I → Domain

  lift : ∀ {I} → (Carrier → Domain) → Family I
  lift P = λ x _ → P x

  IsCoherent : ∀ {I} → Family I → Set
  IsCoherent {I} fam = ∀ {a' a}
    (a'∈I : a' ∈ I) (a∈I : a ∈ I) → a' < a →
    Eq a' (fam a' a'∈I) (fam a a∈I)

  IsLimit : ∀ {I} → Family I → Domain → Set
  IsLimit {I} fam y = ∀ {a'}
    (a'∈I : a' ∈ I) → Eq a' (fam a' a'∈I) y

  IsContractive : (Domain → Domain) → Set
  IsContractive F = ∀ {x y a} →
    (∀ {a'} → a' < a → Eq a' x y) → Eq a (F x) (F y)

-- Complete ordered families of equivalences.

record COFE : Set1 where
  field
    ofe : OFE

  open OFE ofe

  field
    limU     : (Carrier → Domain) → Domain
    isLimitU : ∀ {fam} →
               IsCoherent {U} (lift fam) →
               IsLimit {U} (lift fam) (limU fam)

    lim↓     : ∀ a → Family (↓ a) → Domain
    isLimit↓ : ∀ a {fam : Family (↓ a)} →
               IsCoherent fam → IsLimit fam (lim↓ a fam)

  open OFE ofe public

-- Contractive functions over complete ordered families have
-- fixpoints.

record ContractiveFun (cofe : COFE) : Set where
  open COFE cofe
  field
    F             : Domain → Domain
    isContractive : IsContractive F

  open EqReasoning

  -- The fixpoint is the limit of the following family.

  fam : Carrier → Domain
  fam = wfRec _ (const Domain) (λ a rec → F (lim↓ a (λ _ → rec)))

  fixpoint : Domain
  fixpoint = limU fam

  -- I am not sure if this lemma can be proved without assuming some
  -- kind of proof irrelevance and/or extensionality. It is not
  -- central to the ideas developed here, though, so I leave it as a
  -- postulate.

  postulate unfold : ∀ a → fam a ≅ F (lim↓ a (lift fam))

  -- The family is coherent in several ways.

  fam-isCoherent-↓ : ∀ a → IsCoherent {↓ a} (lift fam)
  fam-isCoherent-↓ = wfRec _ P step
    where
    P : Carrier → Set
    P a = IsCoherent {↓ a} (lift fam)

    step : ∀ a → WfRec _<_ P a → P a
    step a rec {c} {b} c<a b<a c<b = begin
      fam c                  ≈⟨ unfold c c ⟩
      F (lim↓ c (lift fam))  ≈⟨ isContractive (λ {d} d<c → begin
         lim↓ c (lift fam)      ≈⟨ sym $ isLimit↓ c (rec c<a) d<c ⟩
         lift {↓ a} fam d
              (trans d<c c<a)   ≈⟨ isLimit↓ b (rec b<a) (trans d<c c<b) ⟩
         lim↓ b (lift fam)      ∎) ⟩
      F (lim↓ b (lift fam))  ≈⟨ sym $ unfold b c ⟩
      fam b                  ∎

  fam-isCoherent-U : IsCoherent {U} (lift fam)
  fam-isCoherent-U {a'} {a} _ _ = wfRec _ P step a a'
    where
    P : Carrier → Set
    P a = ∀ a' → a' < a → Eq a' (fam a') (fam a)

    step : ∀ a → WfRec _<_ P a → P a
    step a rec a' a'<a = begin
      fam a'                  ≈⟨ unfold a' a' ⟩
      F (lim↓ a' (lift fam))  ≈⟨ isContractive (λ {b} b<a' → begin
         lim↓ a' (lift fam)      ≈⟨ sym $ isLimit↓ a' (fam-isCoherent-↓ a') b<a' ⟩
         fam b                   ≈⟨ isLimit↓ a (fam-isCoherent-↓ a) (trans b<a' a'<a) ⟩
         lim↓ a  (lift fam)      ∎) ⟩
      F (lim↓ a  (lift fam))  ≈⟨ sym $ unfold a a' ⟩
      fam a                   ∎

  -- The fixpoint is a fixpoint.

  isFixpoint : fixpoint ≅ F fixpoint
  isFixpoint a = begin
    fixpoint               ≈⟨ sym $ isLimitU fam-isCoherent-U _ ⟩
    fam a                  ≈⟨ unfold a a ⟩
    F (lim↓ a (lift fam))  ≈⟨ isContractive (λ {a'} a'<a → begin
       lim↓ a (lift fam)      ≈⟨ sym $ isLimit↓ a (fam-isCoherent-↓ a) a'<a ⟩
       fam a'                 ≈⟨ isLimitU fam-isCoherent-U _ ⟩
       limU fam               ∎) ⟩
    F (limU fam)           ≈⟨ refl ⟩
    F fixpoint             ∎

  -- And it is unique.

  unique : ∀ x → x ≅ F x → x ≅ fixpoint
  unique x isFix = wfRec _ P step
    where
    P = λ a → Eq a x fixpoint

    step : ∀ a → WfRec _<_ P a → P a
    step a rec = begin
      x           ≈⟨ isFix a ⟩
      F x         ≈⟨ isContractive rec ⟩
      F fixpoint  ≈⟨ sym $ isFixpoint a ⟩
      fixpoint    ∎
