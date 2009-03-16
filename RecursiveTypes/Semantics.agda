------------------------------------------------------------------------
-- Semantics
------------------------------------------------------------------------

module RecursiveTypes.Semantics where

open import Coinduction

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
open TySubst

-- The semantics of a recursive type, i.e. its possibly infinite
-- unfolding.

⟦_⟧ : ∀ {n} → Ty n → Tree n
⟦ ⊥ ⟧       = ⊥
⟦ ⊤ ⟧       = ⊤
⟦ var x ⟧   = var x
⟦ σ ⟶ τ ⟧   = ♯ ⟦ σ ⟧         ⟶ ♯ ⟦ τ ⟧
⟦ ν σ ⟶ τ ⟧ = ♯ ⟦ σ [0≔ χ ] ⟧ ⟶ ♯ ⟦ τ [0≔ χ ] ⟧
              where χ = ν σ ⟶ τ
