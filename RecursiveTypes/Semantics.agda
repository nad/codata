------------------------------------------------------------------------
-- Semantics
------------------------------------------------------------------------

module RecursiveTypes.Semantics where

open import Codata.Musical.Notation

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution

-- The semantics of a recursive type, i.e. its possibly infinite
-- unfolding.

⟦_⟧ : ∀ {n} → Ty n → Tree n
⟦ ⊥ ⟧       = ⊥
⟦ ⊤ ⟧       = ⊤
⟦ var x ⟧   = var x
⟦ σ ⟶ τ ⟧   = ♯ ⟦ σ ⟧         ⟶ ♯ ⟦ τ ⟧
⟦ μ σ ⟶ τ ⟧ = ♯ ⟦ σ [0≔ χ ] ⟧ ⟶ ♯ ⟦ τ [0≔ χ ] ⟧
              where χ = μ σ ⟶ τ
