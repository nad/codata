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

-- A view of types as either unfolded (U) or fixpoints (Ν).

data U∨Ν {n} : Ty n → Set where
  unfolded : ∀ {σ} (u : Unfolded σ) → U∨Ν σ
  fixpoint : ∀ {τ₁ τ₂} (u : U∨Ν unfold[ν τ₁ ⟶ τ₂ ]) → U∨Ν (ν τ₁ ⟶ τ₂)

u∨ν : ∀ {n} (σ : Ty n) → U∨Ν σ
u∨ν ⊥           = unfolded ⊥
u∨ν ⊤           = unfolded ⊤
u∨ν (var x)     = unfolded (var x)
u∨ν (τ₁ ⟶ τ₂)   = unfolded (τ₁ ⟶ τ₂)
u∨ν (ν τ₁ ⟶ τ₂) =
  fixpoint (unfolded ((τ₁ [0≔ ν τ₁ ⟶ τ₂ ]) ⟶ (τ₂ [0≔ ν τ₁ ⟶ τ₂ ])))

u∨ν⁻¹ : ∀ {n} {σ : Ty n} → U∨Ν σ → Ty n
u∨ν⁻¹ {σ = σ} _ = σ
