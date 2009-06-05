{-# OPTIONS --no-termination-check #-}

------------------------------------------------------------------------
-- Inductive axiomatisation of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Axiomatic.Inductive where

open import Coinduction
open import Data.Empty using (⊥-elim)
open import Data.Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.List.Any as Any using (_∈_; _∉_)
open import Data.List.All as All using (All; []; _∷_)
open import Data.Product renaming (_,_ to _≲_)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary
open import Relation.Unary using (Pred)
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
open import RecursiveTypes.Subtyping.Semantic.Coinductive as Sem
  using (_≤Coind_)
open import RecursiveTypes.Subtyping.Axiomatic.Coinductive as Ax
  using (_≤_; ⊥; ⊤; _⟶_; unfold; fold; _∎; _≤⟨_⟩_)

------------------------------------------------------------------------
-- Definition

infixr 10 _⟶_
infix  4  _⊢_≤_
infixr 2  _≤⟨_⟩_
infix  2  _∎

-- Hypotheses.

Hyp : ℕ → Set
Hyp n = Ty n × Ty n

-- This inductive subtyping relation is parameterised on a list of
-- hypotheses. Note Brandt and Henglein's unusual definition of _⟶_.

data _⊢_≤_ {n} (A : List (Hyp n)) : Ty n → Ty n → Set where
  -- Structural rules.
  ⊥   : ∀ {τ} → A ⊢ ⊥ ≤ τ
  ⊤   : ∀ {σ} → A ⊢ σ ≤ ⊤
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂} →
        let H = σ₁ ⟶ σ₂ ≲ τ₁ ⟶ τ₂ in
        (τ₁≤σ₁ : H ∷ A ⊢ τ₁ ≤ σ₁) (σ₂≤τ₂ : H ∷ A ⊢ σ₂ ≤ τ₂) →
        A ⊢ σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂

  -- Rules for folding and unfolding ν.
  unfold : ∀ {τ₁ τ₂} → A ⊢ ν τ₁ ⟶ τ₂ ≤ unfold[ν τ₁ ⟶ τ₂ ]
  fold   : ∀ {τ₁ τ₂} → A ⊢ unfold[ν τ₁ ⟶ τ₂ ] ≤ ν τ₁ ⟶ τ₂

  -- Reflexivity.
  _∎ : ∀ τ → A ⊢ τ ≤ τ

  -- Transitivity.
  _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
           (τ₁≤τ₂ : A ⊢ τ₁ ≤ τ₂) (τ₂≤τ₃ : A ⊢ τ₂ ≤ τ₃) → A ⊢ τ₁ ≤ τ₃

  -- Hypothesis.
  hyp : ∀ {σ τ} (σ≤τ : (σ ≲ τ) ∈ A) → A ⊢ σ ≤ τ

------------------------------------------------------------------------
-- Soundness

-- A hypothesis is valid if there is a corresponding proof.
--
-- This definition is lazy in order to simplify the definition of
-- sound below.

Valid : ∀ {n} → (Ty n → Ty n → Set) → Pred (Hyp n)
Valid _≤_ σ₁≲σ₂ = proj₁ σ₁≲σ₂ ≤ proj₂ σ₁≲σ₂

module Soundness where

  -- The soundness proof uses my trick to show that the code is
  -- productive.

  infix 4 _≤Prog_ _≤WHNF_

  mutual

    -- Soundness proof programs.

    data _≤Prog_ {n} : Ty n → Ty n → Set where
      sound : ∀ {A σ τ} →
              (valid : All (Valid _≤WHNF_) A) (σ≤τ : A ⊢ σ ≤ τ) →
              σ ≤Prog τ

    -- Weak head normal forms of soundness proof programs. Note that
    -- _⟶_ takes (suspended) /programs/ as arguments, while _≤⟨_⟩_
    -- takes /WHNFs/.

    data _≤WHNF_ {n} : Ty n → Ty n → Set where
      _↓     : ∀ {σ τ} (σ≤τ : σ ≤ τ) → σ ≤WHNF τ
      _⟶_    : ∀ {σ₁ σ₂ τ₁ τ₂}
               (τ₁≤σ₁ : ∞ (τ₁ ≤Prog σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤Prog τ₂)) →
               σ₁ ⟶ σ₂ ≤WHNF τ₁ ⟶ τ₂
      _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
               (τ₁≤τ₂ : τ₁ ≤WHNF τ₂) (τ₂≤τ₃ : τ₂ ≤WHNF τ₃) → τ₁ ≤WHNF τ₃

  -- Computes the WHNF of a soundness program. Note the circular, but
  -- productive, definition of proof below.

  whnf : ∀ {n} {σ τ : Ty n} →
         σ ≤Prog τ → σ ≤WHNF τ
  whnf (sound {A} valid σ≤τ) = w-s σ≤τ
    where
    w-s : ∀ {σ τ} → A ⊢ σ ≤ τ → σ ≤WHNF τ
    w-s ⊥                     = ⊥      ↓
    w-s ⊤                     = ⊤      ↓
    w-s unfold                = unfold ↓
    w-s fold                  = fold   ↓
    w-s (τ ∎)                 = (τ ∎)  ↓
    w-s (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ w-s τ₁≤τ₂ ⟩ w-s τ₂≤τ₃
    w-s (hyp σ≤τ)             = All.lookup σ≤τ valid
    w-s (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = proof
      where proof = ♯ sound (proof ∷ valid) τ₁≤σ₁ ⟶
                    ♯ sound (proof ∷ valid) σ₂≤τ₂

  -- Computes actual proofs.

  mutual

    value : ∀ {n} {σ τ : Ty n} →
            σ ≤WHNF τ → σ ≤ τ
    value (σ≤τ ↓)               = σ≤τ
    value (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = ♯ ⟦ ♭ τ₁≤σ₁ ⟧≤ ⟶ ♯ ⟦ ♭ σ₂≤τ₂ ⟧≤
    value (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ value τ₁≤τ₂ ⟩ value τ₂≤τ₃

    ⟦_⟧≤ : ∀ {n} {σ τ : Ty n} →
           σ ≤Prog τ → σ ≤ τ
    ⟦ σ≤τ ⟧≤ = value (whnf σ≤τ)

-- The definition above is sound with respect to the others.

sound : ∀ {n A} {σ τ : Ty n} →
        A ⊢ σ ≤ τ → All (Valid _≤_) A → σ ≤ τ
sound σ≤τ valid = ⟦ S.sound (All.map _↓ valid) σ≤τ ⟧≤
  where open module S = Soundness

------------------------------------------------------------------------
-- The relation is decidable

module Decidable where

  infix 4 _⊢_≲?_ _⊢_≤?_ _⊢_≤?′_

  _≟_ : ∀ {n} → Decidable (_≡_ {Hyp n})
  ( σ₁ ≲  σ₂) ≟ (τ₁ ≲ τ₂) with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
  (.τ₁ ≲ .τ₂) ≟ (τ₁ ≲ τ₂) | yes refl | yes refl = yes refl
  ... | no σ₁≢τ₁ | _ = no (σ₁≢τ₁ ∘ cong proj₁)
  ... | _ | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ cong proj₂)

  _⊢_≲?_ : ∀ {n} A (σ₁ σ₂ : Ty n) → Dec ((σ₁ ≲ σ₂) ∈ A)
  A ⊢ σ₁ ≲? σ₂ = Any.any (_≟_ (σ₁ ≲ σ₂)) A

  -- The proof below can perhaps be optimised (see Gapeyev, Levin and
  -- Pierce's "Recursive Subtyping Revealed" from ICFP '00).

  mutual

   _⊢_≤?_ : ∀ {n} A (σ τ : Ty n) → A ⊢ σ ≤ τ ⊎ (¬ σ ≤Coind τ)
   A ⊢ σ ≤? τ with A ⊢ σ ≲? τ
   ... | yes σ≤τ = inj₁ (hyp σ≤τ)
   ... | no  _   = A ⊢ σ ≤?′ τ

   _⊢_≤?′_ : ∀ {n} A (σ τ : Ty n) → A ⊢ σ ≤ τ ⊎ (¬ σ ≤Coind τ)
   A ⊢ ⊥ ≤?′ τ = inj₁ ⊥
   A ⊢ σ ≤?′ ⊤ = inj₁ ⊤

   A ⊢ var x ≤?′ var  y with var x ≡? var y
   A ⊢ var x ≤?′ var .x | yes refl = inj₁ (var x ∎)
   A ⊢ var x ≤?′ var  y | no  x≠y  = inj₂ (x≠y ∘ Sem.var:≤∞⟶≡)

   A ⊢ σ₁ ⟶ σ₂ ≤?′ τ₁ ⟶ τ₂ with H ∷ A ⊢ τ₁ ≤? σ₁ | H ∷ A ⊢ σ₂ ≤? τ₂
                           where H = σ₁ ⟶ σ₂ ≲ τ₁ ⟶ τ₂
   ... | inj₂ ≰  | _       = inj₂ (≰ ∘  Sem.left-proj)
   ... | _       | inj₂ ≰  = inj₂ (≰ ∘ Sem.right-proj)
   ... | inj₁ ≤₁ | inj₁ ≤₂ = inj₁ (≤₁ ⟶ ≤₂)

   A ⊢ ν σ₁ ⟶ σ₂ ≤?′ τ =
     Sum.map (λ ≤τ → ν σ₁ ⟶ σ₂           ≤⟨ unfold ⟩
                     unfold[ν σ₁ ⟶ σ₂ ]  ≤⟨ ≤τ ⟩
                     τ                   ∎)
             (λ ≰τ ≤τ → ≰τ (Sem.trans Sem.fold ≤τ))
             (A ⊢ unfold[ν σ₁ ⟶ σ₂ ] ≤? τ)
   A ⊢ σ ≤?′ ν τ₁ ⟶ τ₂ =
     Sum.map (λ σ≤ → σ                   ≤⟨ σ≤ ⟩
                     unfold[ν τ₁ ⟶ τ₂ ]  ≤⟨ fold ⟩
                     ν τ₁ ⟶ τ₂           ∎)
             (λ σ≰ σ≤ → σ≰ (Sem.trans σ≤ Sem.unfold))
             (A ⊢ σ ≤? unfold[ν τ₁ ⟶ τ₂ ])

   A ⊢ ⊤       ≤?′ ⊥       = inj₂ (λ ())
   A ⊢ ⊤       ≤?′ var x   = inj₂ (λ ())
   A ⊢ ⊤       ≤?′ τ₁ ⟶ τ₂ = inj₂ (λ ())
   A ⊢ var x   ≤?′ ⊥       = inj₂ (λ ())
   A ⊢ var x   ≤?′ τ₁ ⟶ τ₂ = inj₂ (λ ())
   A ⊢ σ₁ ⟶ σ₂ ≤?′ ⊥       = inj₂ (λ ())
   A ⊢ σ₁ ⟶ σ₂ ≤?′ var x   = inj₂ (λ ())

infix 4 []⊢_≤?_ _≤?_

-- The definition above is decidable (when the set of assumptions is
-- empty).

[]⊢_≤?_ : ∀ {n} (σ τ : Ty n) → Dec ([] ⊢ σ ≤ τ)
[]⊢ σ ≤? τ with [] ⊢ σ ≤? τ
           where open Decidable
... | inj₁ σ≤τ = yes σ≤τ
... | inj₂ σ≰τ = no (σ≰τ ∘ Ax.sound ∘ flip sound [])

-- The other relations are also decidable.

_≤?_ : ∀ {n} (σ τ : Ty n) → Dec (σ ≤ τ)
σ ≤? τ with [] ⊢ σ ≤? τ
       where open Decidable
... | inj₁ σ≤τ = yes (sound σ≤τ [])
... | inj₂ σ≰τ = no (σ≰τ ∘ Ax.sound)

------------------------------------------------------------------------
-- Completeness

-- The definition above is complete with respect to the others.

complete : ∀ {n A} {σ τ : Ty n} →
           σ ≤ τ → A ⊢ σ ≤ τ
complete {A = A} {σ} {τ} σ≤τ with A ⊢ σ ≤? τ
                             where open Decidable
... | inj₁ ⊢σ≤τ = ⊢σ≤τ
... | inj₂ σ≰τ  = ⊥-elim (σ≰τ (Ax.sound σ≤τ))
