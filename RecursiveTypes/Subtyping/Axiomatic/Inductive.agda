------------------------------------------------------------------------
-- Inductive axiomatisation of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Axiomatic.Inductive where

open import Coinduction
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Any as Any using (_∈_; here; there)
open import Data.List.All as All using (All; []; _∷_; lookup)
open import Relation.Unary using (Pred; _⊆_)

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
open import RecursiveTypes.Semantics
open import RecursiveTypes.Subtyping.Axiomatic.Coinductive
  hiding (sound; complete)

------------------------------------------------------------------------
-- Definition

infixr 10 _⟶_
infix  6  _≲_
infix  4  _⊢_≤_
infixr 2  _≤⟨_⟩_
infix  2  _∎

-- Hypotheses.

record Hyp : Set where
  field
    n₁ : ℕ
    n₂ : ℕ
    σ₁ : Ty n₁
    σ₂ : Ty n₂

_≲_ : ∀ {n₁ n₂} (σ₁ : Ty n₁) (σ₂ : Ty n₂) → Hyp
σ₁ ≲ σ₂ = record { σ₁ = σ₁; σ₂ = σ₂ }

-- This inductive subtyping relation is parameterised on a list of
-- hypotheses. Note Brandt and Henglein's unusual definition of _⟶_.

data _⊢_≤_ (A : List Hyp) : ∀ {m n} → Ty m → Ty n → Set where
  -- Structural rules.
  ⊥   : ∀ {m n} {τ : Ty n} → A ⊢ ⊥ {m} ≤ τ
  ⊤   : ∀ {m n} {σ : Ty m} → A ⊢ σ ≤ ⊤ {n}
  _⟶_ : ∀ {m n} {σ₁ σ₂ : Ty m} {τ₁ τ₂ : Ty n} →
        let H = σ₁ ⟶ σ₂ ≲ τ₁ ⟶ τ₂ in
        (τ₁≤σ₁ : H ∷ A ⊢ τ₁ ≤ σ₁) (σ₂≤τ₂ : H ∷ A ⊢ σ₂ ≤ τ₂) →
        A ⊢ σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂

  -- Rules for folding and unfolding ν.
  unfold : ∀ {n} (τ₁ τ₂ : Ty (suc n)) →
           let τ = ν τ₁ ⟶ τ₂ in A ⊢ τ ≤ τ₁ ⟶ τ₂ [0≔ τ ]
  fold   : ∀ {n} (τ₁ τ₂ : Ty (suc n)) →
           let τ = ν τ₁ ⟶ τ₂ in A ⊢ τ₁ ⟶ τ₂ [0≔ τ ] ≤ τ

  -- Reflexivity.
  _∎ : ∀ {n} (τ : Ty n) → A ⊢ τ ≤ τ

  -- Transitivity.
  _≤⟨_⟩_ : ∀ {m n k} (τ₁ : Ty m) {τ₂ : Ty n} {τ₃ : Ty k}
           (τ₁≤τ₂ : A ⊢ τ₁ ≤ τ₂) (τ₂≤τ₃ : A ⊢ τ₂ ≤ τ₃) → A ⊢ τ₁ ≤ τ₃

  -- Hypothesis.
  hyp : ∀ {m n} {σ : Ty m} {τ : Ty n}
        (σ≤τ : σ ≲ τ ∈ A) → A ⊢ σ ≤ τ

------------------------------------------------------------------------
-- Correctness

-- A hypothesis is valid if there is a corresponding proof.

Valid : (∀ {m n} → Ty m → Ty n → Set) → Pred Hyp
Valid _≤_ σ₁≲σ₂ = σ₁ ≤ σ₂
  where open Hyp σ₁≲σ₂

module Soundness where

  -- The soundness proof uses my trick to show that the code is
  -- productive.

  infix 4 _≤Prog_ _≤WHNF_

  mutual

    -- Soundness proof programs.

    data _≤Prog_ : ∀ {m n} → Ty m → Ty n → Set where
      sound : ∀ {A m n} {σ : Ty m} {τ : Ty n} →
              (valid : All (Valid _≤WHNF_) A) (σ≤τ : A ⊢ σ ≤ τ) →
              σ ≤Prog τ

    -- Weak head normal forms of soundness proof programs. Note that
    -- _⟶_ takes (suspended) /programs/ as arguments, while _≤⟨_⟩_
    -- takes /WHNFs/.

    data _≤WHNF_ : ∀ {m n} → Ty m → Ty n → Set where
      _↓     : ∀ {m n} {σ : Ty m} {τ : Ty n} (σ≤τ : σ ≤ τ) → σ ≤WHNF τ
      _⟶_    : ∀ {m n} {σ₁ σ₂ : Ty m} {τ₁ τ₂ : Ty n}
               (τ₁≤σ₁ : ∞ (τ₁ ≤Prog σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤Prog τ₂)) →
               σ₁ ⟶ σ₂ ≤WHNF τ₁ ⟶ τ₂
      _≤⟨_⟩_ : ∀ {m n k} (τ₁ : Ty m) {τ₂ : Ty n} {τ₃ : Ty k}
               (τ₁≤τ₂ : τ₁ ≤WHNF τ₂) (τ₂≤τ₃ : τ₂ ≤WHNF τ₃) → τ₁ ≤WHNF τ₃

  -- Computes the WHNF of a soundness program. Note the circular, but
  -- productive, definition of proof below.

  whnf : ∀ {m n} {σ : Ty m} {τ : Ty n} →
         σ ≤Prog τ → σ ≤WHNF τ
  whnf (sound {A} valid σ≤τ) = w-s σ≤τ
    where
    w-s : ∀ {m n} {σ : Ty m} {τ : Ty n} →
          A ⊢ σ ≤ τ → σ ≤WHNF τ
    w-s ⊥                     = ⊥            ↓
    w-s ⊤                     = ⊤            ↓
    w-s (unfold τ₁ τ₂)        = unfold τ₁ τ₂ ↓
    w-s (fold   τ₁ τ₂)        = fold   τ₁ τ₂ ↓
    w-s (τ ∎)                 = (τ ∎)        ↓
    w-s (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ w-s τ₁≤τ₂ ⟩ w-s τ₂≤τ₃
    w-s (hyp σ≤τ)             = lookup σ≤τ valid
    w-s (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = proof
      where proof = ♯ sound (proof ∷ valid) τ₁≤σ₁ ⟶
                    ♯ sound (proof ∷ valid) σ₂≤τ₂

  -- Computes actual proofs.

  mutual

    value : ∀ {m n} {σ : Ty m} {τ : Ty n} →
            σ ≤WHNF τ → σ ≤ τ
    value (σ≤τ ↓)               = σ≤τ
    value (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = ♯ ⟦ ♭ τ₁≤σ₁ ⟧≤ ⟶ ♯ ⟦ ♭ σ₂≤τ₂ ⟧≤
    value (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ value τ₁≤τ₂ ⟩ value τ₂≤τ₃

    ⟦_⟧≤ : ∀ {m n} {σ : Ty m} {τ : Ty n} →
           σ ≤Prog τ → σ ≤ τ
    ⟦ σ≤τ ⟧≤ = value (whnf σ≤τ)

-- The definition above is sound with respect to the others.

sound : ∀ {A m n} {σ : Ty m} {τ : Ty n} →
        A ⊢ σ ≤ τ → All (Valid _≤_) A → σ ≤ τ
sound σ≤τ valid = ⟦ S.sound (All.map _↓ valid) σ≤τ ⟧≤
  where open module S = Soundness
