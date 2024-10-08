------------------------------------------------------------------------
-- Restricted hypotheses
------------------------------------------------------------------------

-- A restricted hypothesis is a hypothesis where both types are
-- sub/terms/ of either one of two given types.

open import RecursiveTypes.Syntax

module RecursiveTypes.Subterm.RestrictedHypothesis
         {n} (χ₁ χ₂ : Ty n) where

open import Function
open import Data.List as List
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties
import Data.List.Countdown as Countdown
import Data.List.Effectful
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties
import Data.List.Membership.Setoid
open import Data.Product as Prod
open import Data.Sum as Sum
open import Effect.Monad
open import Level
open import Relation.Nullary
open import Relation.Binary
import Relation.Binary.Construct.On as On
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open RawMonad (Data.List.Effectful.monad {ℓ = zero})

open import RecursiveTypes.Subterm as ST using (_⊑_; _∗)

------------------------------------------------------------------------
-- Restricted hypotheses

-- Types which are subterms of either χ₁ or χ₂.

Subterm : Ty n → Set
Subterm σ = σ ⊑ χ₁ ⊎ σ ⊑ χ₂

-- The Subterm predicate is anti-monotone.

anti-mono : ∀ {σ₁ σ₂} → σ₂ ⊑ σ₁ → Subterm σ₁ → Subterm σ₂
anti-mono σ₂⊑σ₁ = Sum.map (ST.trans σ₂⊑σ₁) (ST.trans σ₂⊑σ₁)

-- Hypotheses where both types are subterms.

RestrictedHyp : Set
RestrictedHyp = ∃ Subterm × ∃ Subterm

-- Computes the underlying hypothesis/es.

⟨_⟩ : RestrictedHyp → Hyp n
⟨_⟩ = Prod.map proj₁ proj₁

⟨_⟩⋆ : List RestrictedHyp → List (Hyp n)
⟨_⟩⋆ = List.map ⟨_⟩

-- Equality of restricted hypotheses (ignores the subterm proofs).

_≈_ : Rel RestrictedHyp zero
_≈_ = _≡_ on ⟨_⟩

-- List membership relation for restricted hypotheses.

open Data.List.Membership.Setoid
       (record { isEquivalence =
                   On.isEquivalence (⟨_⟩) PropEq.isEquivalence })
  using () renaming (_∈_ to _⟨∈⟩_)

------------------------------------------------------------------------
-- Computing all possible restricted hypotheses

-- Computes all the subterms of the given type.

subtermsOf : ∀ τ → (∀ {σ} → σ ⊑ τ → Subterm σ) → List (∃ Subterm)
subtermsOf τ f = List.map (Prod.map id f) (ST.subtermsOf τ)

subtermsOf-complete :
  ∀ {τ} (f : ∀ {σ} → σ ⊑ τ → Subterm σ) {σ} →
  σ ⊑ τ → ∃ λ σ⊑τ → (σ , f σ⊑τ) ∈ subtermsOf τ f
subtermsOf-complete f σ⊑τ =
  Prod.map id (λ ∈ → Inverse.to (map-∈↔ _) (_ , ∈ , refl)) $
    ST.subtermsOf-complete σ⊑τ

subtermsOf²-complete :
  ∀ {σ₁ τ₁ σ₂ τ₂}
  (f : ∀ {σ} → σ ⊑ τ₁ → Subterm σ)
  (g : ∀ {σ} → σ ⊑ τ₂ → Subterm σ) →
  (σ₁⊑τ₁ : σ₁ ⊑ τ₁) (σ₂⊑τ₂ : σ₂ ⊑ τ₂) →
  ((σ₁ , f σ₁⊑τ₁) ≲ (σ₂ , g σ₂⊑τ₂)) ⟨∈⟩
    (subtermsOf τ₁ f ⊗ subtermsOf τ₂ g)
subtermsOf²-complete f g σ₁⊑τ₁ σ₂⊑τ₂ =
  Any.map (PropEq.cong $ Prod.map proj₁ proj₁) $
    Inverse.to ⊗-∈↔
      ( proj₂ (subtermsOf-complete f σ₁⊑τ₁)
      , proj₂ (subtermsOf-complete g σ₂⊑τ₂)
      )

-- All subterms of χ₁.

⊑-χ₁ : List (∃ Subterm)
⊑-χ₁ = subtermsOf χ₁ inj₁

-- All subterms of χ₂.

⊑-χ₂ : List (∃ Subterm)
⊑-χ₂ = subtermsOf χ₂ inj₂

-- All possible restricted hypotheses.

restrictedHyps : List RestrictedHyp
restrictedHyps = (⊑-χ₁ ⊗ ⊑-χ₂) ++ (⊑-χ₂ ⊗ ⊑-χ₁) ++
                 (⊑-χ₁ ⊗ ⊑-χ₁) ++ (⊑-χ₂ ⊗ ⊑-χ₂)

complete : ∀ h → h ⟨∈⟩ restrictedHyps
complete ((σ , inj₁ σ⊑χ₁) ≲ (τ , inj₂ τ⊑χ₂)) =
  Inverse.to ++↔ (inj₁ $
  subtermsOf²-complete inj₁ inj₂ σ⊑χ₁ τ⊑χ₂)
complete ((σ , inj₂ σ⊑χ₂) ≲ (τ , inj₁ τ⊑χ₁)) =
  Inverse.to (++↔ {xs = ⊑-χ₁ ⊗ ⊑-χ₂}) (inj₂ $
  Inverse.to ++↔                      (inj₁ $
  subtermsOf²-complete inj₂ inj₁ σ⊑χ₂ τ⊑χ₁))
complete ((σ , inj₁ σ⊑χ₁) ≲ (τ , inj₁ τ⊑χ₁)) =
  Inverse.to (++↔ {xs = ⊑-χ₁ ⊗ ⊑-χ₂}) (inj₂ $
  Inverse.to (++↔ {xs = ⊑-χ₂ ⊗ ⊑-χ₁}) (inj₂ $
  Inverse.to ++↔                      (inj₁ $
  subtermsOf²-complete inj₁ inj₁ σ⊑χ₁ τ⊑χ₁)))
complete ((σ , inj₂ σ⊑χ₂) ≲ (τ , inj₂ τ⊑χ₂)) =
  Inverse.to (++↔ {xs = ⊑-χ₁ ⊗ ⊑-χ₂}) (inj₂ $
  Inverse.to (++↔ {xs = ⊑-χ₂ ⊗ ⊑-χ₁}) (inj₂ $
  Inverse.to (++↔ {xs = ⊑-χ₁ ⊗ ⊑-χ₁}) (inj₂ $
  subtermsOf²-complete inj₂ inj₂ σ⊑χ₂ τ⊑χ₂)))

------------------------------------------------------------------------
-- A countdown structure for restricted hypotheses

-- Equality of restricted hypotheses can be decided.

_≟_ : Decidable (_≡_ {A = Hyp n})
( σ₁ ≲  σ₂) ≟ (τ₁ ≲ τ₂) with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
(.τ₁ ≲ .τ₂) ≟ (τ₁ ≲ τ₂) | yes refl | yes refl = yes refl
... | no σ₁≢τ₁ | _ = no (σ₁≢τ₁ ∘ PropEq.cong proj₁)
... | _ | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ PropEq.cong proj₂)

isDecEquivalence : IsDecEquivalence _≈_
isDecEquivalence =
  On.isDecEquivalence ⟨_⟩ $
    DecSetoid.isDecEquivalence (PropEq.decSetoid _≟_)

-- The countdown data structure can be used to keep track of (an upper
-- bound of) the number of hypotheses which have not been inserted
-- into a given list of hypotheses yet.

private
  open module C =
    Countdown (record { isDecEquivalence = isDecEquivalence })
    public hiding (empty; emptyFromList)

-- An initialised countdown structure.

empty : [] ⊕ length restrictedHyps
empty = C.emptyFromList restrictedHyps complete
