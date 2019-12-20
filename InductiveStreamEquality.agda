------------------------------------------------------------------------
-- A sound, inductive approximation of stream equality
------------------------------------------------------------------------

-- The point of this module is to give a short (not entirely faithful)
-- illustration of the technique used to establish soundness of
-- RecursiveTypes.Subtyping.Axiomatic.Inductive._⊢_≤_ with respect to
-- RecursiveTypes.Subtyping.Axiomatic.Coinductive._≤_.

module InductiveStreamEquality {A : Set} where

open import Codata.Musical.Notation
open import Codata.Musical.Stream hiding (_∈_; lookup)
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

infixr 5 _∷_
infix  4 _⊢_≈_ _≈P_ _≈W_

------------------------------------------------------------------------
-- An approximation of stream equality

-- Streams do not need to be regular, so _⊢_≈_ is not complete with
-- respect to _≈_.

data _⊢_≈_ (H : List (Stream A × Stream A)) :
           Stream A → Stream A → Set where
  _∷_   : ∀ x {xs ys} →
          (x ∷ xs , x ∷ ys) ∷ H ⊢ ♭ xs ≈ ♭ ys →
          H ⊢ x ∷ xs ≈ x ∷ ys
  hyp   : ∀ {xs ys} → (xs , ys) ∈ H → H ⊢ xs ≈ ys
  trans : ∀ {xs ys zs} → H ⊢ xs ≈ ys → H ⊢ ys ≈ zs → H ⊢ xs ≈ zs

-- Example.

repeat-refl : (x : A) → [] ⊢ repeat x ≈ repeat x
repeat-refl x = x ∷ hyp (here refl)

------------------------------------------------------------------------
-- Soundness

Valid : (Stream A → Stream A → Set) → Stream A × Stream A → Set
Valid _R_ (xs , ys) = xs R ys

-- Programs and WHNFs.

mutual

  data _≈P_ : Stream A → Stream A → Set where
    sound : ∀ {A xs ys} → All (Valid _≈W_) A → A ⊢ xs ≈ ys → xs ≈P ys
    trans : ∀ {xs ys zs} → xs ≈P ys → ys ≈P zs → xs ≈P zs

  data _≈W_ : Stream A → Stream A → Set where
    _∷_ : ∀ x {xs ys} → ∞ (♭ xs ≈P ♭ ys) → x ∷ xs ≈W x ∷ ys

transW : ∀ {xs ys zs} → xs ≈W ys → ys ≈W zs → xs ≈W zs
transW (x ∷ xs≈ys) (.x ∷ ys≈zs) = x ∷ ♯ trans (♭ xs≈ys) (♭ ys≈zs)

soundW : ∀ {A xs ys} → All (Valid _≈W_) A → A ⊢ xs ≈ ys → xs ≈W ys
soundW valid (hyp h)             = All.lookup valid h
soundW valid (trans xs≈ys ys≈zs) = transW (soundW valid xs≈ys)
                                          (soundW valid ys≈zs)
soundW valid (x ∷ xs≈ys)         = proof
  where
  proof : _ ≈W _
  proof = x ∷ ♯ sound (proof ∷ valid) xs≈ys

whnf : ∀ {xs ys} → xs ≈P ys → xs ≈W ys
whnf (sound valid xs≈ys) = soundW valid xs≈ys
whnf (trans xs≈ys ys≈zs) = transW (whnf xs≈ys) (whnf ys≈zs)

-- The programs and WHNFs are sound with respect to _≈_.

mutual

  ⟦_⟧W : ∀ {xs ys} → xs ≈W ys → xs ≈ ys
  ⟦ x ∷ xs≈ys ⟧W = refl ∷ ♯ ⟦ ♭ xs≈ys ⟧P

  ⟦_⟧P : ∀ {xs ys} → xs ≈P ys → xs ≈ ys
  ⟦ xs≈ys ⟧P = ⟦ whnf xs≈ys ⟧W

-- The programs and WHNFs are also complete with respect to _≈_.

mutual

  completeP : ∀ {xs ys} → xs ≈ ys → xs ≈P ys
  completeP xs≈ys = sound (completeW xs≈ys ∷ []) (hyp (here refl))

  completeW : ∀ {xs ys} → xs ≈ ys → xs ≈W ys
  completeW (refl ∷ xs≈ys) = _ ∷ ♯ completeP (♭ xs≈ys)

-- Finally we get the intended soundness result for _⊢_≈_.

reallySound : ∀ {A xs ys} → All (Valid _≈_) A → A ⊢ xs ≈ ys → xs ≈ ys
reallySound valid xs≈ys =
  ⟦ sound (All.map (λ {p} → done p) valid) xs≈ys ⟧P
  where
  done : ∀ p → Valid _≈_ p → Valid _≈W_ p
  done (xs , ys) = completeW
