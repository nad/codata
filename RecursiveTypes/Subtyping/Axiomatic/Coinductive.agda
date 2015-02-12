------------------------------------------------------------------------
-- Coinductive axiomatisation of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Axiomatic.Coinductive where

import Data.Empty as E
open import Data.Fin using (Fin; zero; suc)
open import Data.Nat using (ℕ; zero; suc)
open import Coinduction hiding (unfold)
open import Relation.Nullary

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
open import RecursiveTypes.Semantics
open import RecursiveTypes.Subtyping.Semantic.Coinductive as Sem
  using (_≤∞P_; _≤Coind_; ⟦_⟧P; ⌜_⌝; ⊥; ⊤; var; _⟶_; _≤⟨_⟩_)

------------------------------------------------------------------------
-- Definition

-- This definition uses mixed induction and coinduction. Induction is
-- used for rules like transitivity, whereas coinduction is used for
-- structural rules. Benjamin Pierce observed in Types and Programming
-- Languages that coinductive inference systems cannot be
-- "declarative" (including rules like transitivity); they can be
-- "algorithmic" (syntax-directed), though. However, by mixing
-- induction and coinduction one can combine the benefits of
-- coinduction and declarative inference systems.

infixr 10 _⟶_
infix  4  _≤_
infix  3  _∎
infixr 2  _≤⟨_⟩_

data _≤_ {n} : Ty n → Ty n → Set where
  -- Structural rules. Note that the rule for _⟶_ is coinductive.
  ⊥   : ∀ {τ} → ⊥ ≤ τ
  ⊤   : ∀ {σ} → σ ≤ ⊤
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂} (τ₁≤σ₁ : ∞ (τ₁ ≤ σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤ τ₂)) →
        σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂

  -- Rules for folding and unfolding μ.
  unfold : ∀ {τ₁ τ₂} → μ τ₁ ⟶ τ₂ ≤ unfold[μ τ₁ ⟶ τ₂ ]
  fold   : ∀ {τ₁ τ₂} → unfold[μ τ₁ ⟶ τ₂ ] ≤ μ τ₁ ⟶ τ₂

  -- Reflexivity.
  _∎ : ∀ τ → τ ≤ τ

  -- Transitivity.
  _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃} (τ₁≤τ₂ : τ₁ ≤ τ₂) (τ₂≤τ₃ : τ₂ ≤ τ₃) → τ₁ ≤ τ₃

------------------------------------------------------------------------
-- Equivalence

-- The axiomatisation is equivalent to the semantic definitions of
-- subtyping.

soundP : ∀ {n} {σ τ : Ty n} → σ ≤ τ → ⟦ σ ⟧ ≤∞P ⟦ τ ⟧
soundP ⊥                     = ⊥
soundP ⊤                     = ⊤
soundP (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = ♯ soundP (♭ τ₁≤σ₁) ⟶ ♯ soundP (♭ σ₂≤τ₂)
soundP unfold                = ⌜ Sem.unfold  ⌝
soundP fold                  = ⌜ Sem.fold    ⌝
soundP (τ ∎)                 = ⌜ Sem.refl∞ _ ⌝
soundP (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = _ ≤⟨ soundP τ₁≤τ₂ ⟩ soundP τ₂≤τ₃

sound : ∀ {n} {σ τ : Ty n} → σ ≤ τ → σ ≤Coind τ
sound σ≤τ = ⟦ soundP σ≤τ ⟧P

complete : ∀ {n} (σ τ : Ty n) → σ ≤Coind τ → σ ≤ τ
complete ⊥         _         _ = ⊥
complete _         ⊤         _ = ⊤
complete ⊤         ⊥         ()
complete ⊤         (var x)   ()
complete ⊤         (σ ⟶ τ)   ()
complete ⊤         (μ σ ⟶ τ) ()
complete (var x)   ⊥         ()
complete (var x)   (var .x)  var = var x ∎
complete (var x)   (σ ⟶ τ)   ()
complete (var x)   (μ σ ⟶ τ) ()
complete (σ₁ ⟶ σ₂) ⊥         ()
complete (σ₁ ⟶ σ₂) (var x)   ()
complete (σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  ♯ complete τ₁ σ₁ (♭ τ₁≤σ₁) ⟶ ♯ complete σ₂ τ₂ (♭ σ₂≤τ₂)
complete (σ₁ ⟶ σ₂) (μ τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  σ₁ ⟶ σ₂             ≤⟨ ♯ complete _ _ (♭ τ₁≤σ₁) ⟶
                         ♯ complete _ _ (♭ σ₂≤τ₂) ⟩
  unfold[μ τ₁ ⟶ τ₂ ]  ≤⟨ fold ⟩
  μ τ₁ ⟶ τ₂           ∎
complete (μ σ₁ ⟶ σ₂) ⊥         ()
complete (μ σ₁ ⟶ σ₂) (var x)   ()
complete (μ σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  μ σ₁ ⟶ σ₂           ≤⟨ unfold ⟩
  unfold[μ σ₁ ⟶ σ₂ ]  ≤⟨ ♯ complete _ _ (♭ τ₁≤σ₁) ⟶
                         ♯ complete _ _ (♭ σ₂≤τ₂) ⟩
  (τ₁ ⟶ τ₂)           ∎
complete (μ σ₁ ⟶ σ₂) (μ τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  μ σ₁ ⟶ σ₂           ≤⟨ unfold ⟩
  unfold[μ σ₁ ⟶ σ₂ ]  ≤⟨ ♯ complete _ _ (♭ τ₁≤σ₁) ⟶
                         ♯ complete _ _ (♭ σ₂≤τ₂) ⟩
  unfold[μ τ₁ ⟶ τ₂ ]  ≤⟨ fold ⟩
  μ τ₁ ⟶ τ₂           ∎

------------------------------------------------------------------------
-- The reflexivity constructor is essential

-- Minor point: the constructor _∎ cannot be omitted. In
-- RecursiveTypes.Subtyping.Axiomatic.Incorrect it is shown that
-- _≤⟨_⟩_ is also essential.

module ∎-Is-Essential where

  infixr 10 _⟶_
  infix  4  _≤′_
  infixr 2  _≤⟨_⟩_

  data _≤′_ {n} : Ty n → Ty n → Set where
    ⊥   : ∀ {τ} → ⊥ ≤′ τ
    ⊤   : ∀ {σ} → σ ≤′ ⊤
    _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
          (τ₁≤σ₁ : ∞ (τ₁ ≤′ σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤′ τ₂)) →
          σ₁ ⟶ σ₂ ≤′ τ₁ ⟶ τ₂

    unfold : ∀ {τ₁ τ₂} → μ τ₁ ⟶ τ₂ ≤′ unfold[μ τ₁ ⟶ τ₂ ]
    fold   : ∀ {τ₁ τ₂} → unfold[μ τ₁ ⟶ τ₂ ] ≤′ μ τ₁ ⟶ τ₂

    _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
             (τ₁≤τ₂ : τ₁ ≤′ τ₂) (τ₂≤τ₃ : τ₂ ≤′ τ₃) → τ₁ ≤′ τ₃

  sound′ : ∀ {n} {σ τ : Ty n} → σ ≤′ τ → σ ≤ τ
  sound′ ⊥                    = ⊥
  sound′ ⊤                    = ⊤
  sound′ (τ₁≤σ₁ ⟶ σ₂≤τ₂)      = ♯ sound′ (♭ τ₁≤σ₁) ⟶ ♯ sound′ (♭ σ₂≤τ₂)
  sound′ unfold               = unfold
  sound′ fold                 = fold
  sound′ (_ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = _ ≤⟨ sound′ τ₁≤τ₂ ⟩ sound′ τ₂≤τ₃

  x : Ty 1
  x = var zero

  x≰′x : ¬ x ≤′ x
  x≰′x (.x ≤⟨ x≤′σ ⟩ σ≤x) = helper x≤′σ σ≤x
    where
    helper : ∀ {σ} → x ≤′ σ → σ ≤′ x → E.⊥
    helper (.x ≤⟨ x≤σ₁ ⟩ σ₁≤σ₂) σ₂≤′x = helper x≤σ₁ (_ ≤⟨ σ₁≤σ₂ ⟩ σ₂≤′x)
    helper ⊤                    ⊤≤′x  with sound (sound′ ⊤≤′x)
    ... | ()

  incomplete : ¬ (∀ {n} {σ τ : Ty n} → σ ≤ τ → σ ≤′ τ)
  incomplete hyp with x≰′x (hyp (x ∎))
  ... | ()
