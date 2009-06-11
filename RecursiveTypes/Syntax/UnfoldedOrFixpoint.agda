------------------------------------------------------------------------
-- A view of the syntax
------------------------------------------------------------------------

module RecursiveTypes.Syntax.UnfoldedOrFixpoint where

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution

-- Unfolded types, i.e. types where the outermost construction is
-- not a fixpoint.

infixr 10 _⟶_

data Unfolded {n} : Ty n → Set where
  ⊥   : Unfolded ⊥
  ⊤   : Unfolded ⊤
  var : ∀ x → Unfolded (var x)
  _⟶_ : (τ₁ τ₂ : Ty n) → Unfolded (τ₁ ⟶ τ₂)

-- A view of types as either unfolded (U) or fixpoints (Μ).

data U∨Μ {n} : Ty n → Set where
  unfolded : ∀ {σ} (u : Unfolded σ) → U∨Μ σ
  fixpoint : ∀ {τ₁ τ₂} (u : U∨Μ unfold[μ τ₁ ⟶ τ₂ ]) → U∨Μ (μ τ₁ ⟶ τ₂)

u∨μ : ∀ {n} (σ : Ty n) → U∨Μ σ
u∨μ ⊥           = unfolded ⊥
u∨μ ⊤           = unfolded ⊤
u∨μ (var x)     = unfolded (var x)
u∨μ (τ₁ ⟶ τ₂)   = unfolded (τ₁ ⟶ τ₂)
u∨μ (μ τ₁ ⟶ τ₂) =
  fixpoint (unfolded ((τ₁ [0≔ μ τ₁ ⟶ τ₂ ]) ⟶ (τ₂ [0≔ μ τ₁ ⟶ τ₂ ])))

u∨μ⁻¹ : ∀ {n} {σ : Ty n} → U∨Μ σ → Ty n
u∨μ⁻¹ {σ = σ} _ = σ
