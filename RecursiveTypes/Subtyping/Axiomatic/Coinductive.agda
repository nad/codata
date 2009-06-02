------------------------------------------------------------------------
-- Coinductive axiomatisation of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Axiomatic.Coinductive where

open import Data.Nat using (ℕ; zero; suc)
open import Coinduction

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
open import RecursiveTypes.Semantics
open import RecursiveTypes.Subtyping.Semantic.Coinductive as Sem
  using (_≤∞Prog_; _≤Coind_; ⟦_⟧≤∞; ⊥; ⊤; var; _⟶_; _∎; _≤⟨_⟩_)

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
infixr 2  _≤⟨_⟩_
infix  2  _∎

data _≤_ : ∀ {m n} → Ty m → Ty n → Set where
  -- Structural rules. Note that the rule for _⟶_ is coinductive.
  ⊥   : ∀ {m n} {τ : Ty n} → ⊥ {m} ≤ τ
  ⊤   : ∀ {m n} {σ : Ty m} → σ ≤ ⊤ {n}
  _⟶_ : ∀ {m n} {σ₁ σ₂ : Ty m} {τ₁ τ₂ : Ty n}
        (τ₁≤σ₁ : ∞ (τ₁ ≤ σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤ τ₂)) →
        σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂

  -- Rules for folding and unfolding ν.
  unfold : ∀ {n} {τ₁ τ₂ : Ty (suc n)} → ν τ₁ ⟶ τ₂ ≤ unfold[ν τ₁ ⟶ τ₂ ]
  fold   : ∀ {n} {τ₁ τ₂ : Ty (suc n)} → unfold[ν τ₁ ⟶ τ₂ ] ≤ ν τ₁ ⟶ τ₂

  -- Reflexivity.
  _∎ : ∀ {n} (τ : Ty n) → τ ≤ τ

  -- Transitivity.
  _≤⟨_⟩_ : ∀ {m n k} (τ₁ : Ty m) {τ₂ : Ty n} {τ₃ : Ty k}
           (τ₁≤τ₂ : τ₁ ≤ τ₂) (τ₂≤τ₃ : τ₂ ≤ τ₃) → τ₁ ≤ τ₃

------------------------------------------------------------------------
-- Equivalence

-- The axiomatisation is equivalent to the semantic definitions of
-- subtyping.

sound′ : ∀ {m n} {σ : Ty m} {τ : Ty n} → σ ≤ τ → ⟦ σ ⟧ ≤∞Prog ⟦ τ ⟧
sound′ ⊥                     = ⊥
sound′ ⊤                     = ⊤
sound′ (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = ♯ sound′ (♭ τ₁≤σ₁) ⟶ ♯ sound′ (♭ σ₂≤τ₂)
sound′ unfold                = Sem.prog Sem.unfold
sound′ fold                  = Sem.prog Sem.fold
sound′ (τ ∎)                 = _ ∎
sound′ (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = _ ≤⟨ sound′ τ₁≤τ₂ ⟩ sound′ τ₂≤τ₃

sound : ∀ {m n} {σ : Ty m} {τ : Ty n} → σ ≤ τ → σ ≤Coind τ
sound σ≤τ = ⟦ sound′ σ≤τ ⟧≤∞

complete : ∀ {m n} (σ : Ty m) (τ : Ty n) → σ ≤Coind τ → σ ≤ τ
complete ⊥         _         _ = ⊥
complete _         ⊤         _ = ⊤
complete ⊤         ⊥         ()
complete ⊤         (var x)   ()
complete ⊤         (σ ⟶ τ)   ()
complete ⊤         (ν σ ⟶ τ) ()
complete (var x)   ⊥         ()
complete (var x)   (var .x)  var = var x ∎
complete (var x)   (σ ⟶ τ)   ()
complete (var x)   (ν σ ⟶ τ) ()
complete (σ₁ ⟶ σ₂) ⊥         ()
complete (σ₁ ⟶ σ₂) (var x)   ()
complete (σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  ♯ complete τ₁ σ₁ (♭ τ₁≤σ₁) ⟶ ♯ complete σ₂ τ₂ (♭ σ₂≤τ₂)
complete (σ₁ ⟶ σ₂) (ν τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  σ₁ ⟶ σ₂             ≤⟨ ♯ complete _ _ (♭ τ₁≤σ₁) ⟶
                         ♯ complete _ _ (♭ σ₂≤τ₂) ⟩
  unfold[ν τ₁ ⟶ τ₂ ]  ≤⟨ fold ⟩
  ν τ₁ ⟶ τ₂           ∎
complete (ν σ₁ ⟶ σ₂) ⊥         ()
complete (ν σ₁ ⟶ σ₂) (var x)   ()
complete (ν σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  ν σ₁ ⟶ σ₂           ≤⟨ unfold ⟩
  unfold[ν σ₁ ⟶ σ₂ ]  ≤⟨ ♯ complete _ _ (♭ τ₁≤σ₁) ⟶
                         ♯ complete _ _ (♭ σ₂≤τ₂) ⟩
  (τ₁ ⟶ τ₂)           ∎
complete (ν σ₁ ⟶ σ₂) (ν τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) =
  ν σ₁ ⟶ σ₂           ≤⟨ unfold ⟩
  unfold[ν σ₁ ⟶ σ₂ ]  ≤⟨ ♯ complete _ _ (♭ τ₁≤σ₁) ⟶
                         ♯ complete _ _ (♭ σ₂≤τ₂) ⟩
  unfold[ν τ₁ ⟶ τ₂ ]  ≤⟨ fold ⟩
  ν τ₁ ⟶ τ₂           ∎
