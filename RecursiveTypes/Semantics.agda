------------------------------------------------------------------------
-- Semantics
------------------------------------------------------------------------

module RecursiveTypes.Semantics where

open import Coinduction
open import Data.Fin.Substitution
open import Data.Nat
open import Data.Function hiding (id)

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution

-- The semantics of a recursive type, i.e. its possibly infinite
-- unfolding.

⟦_⟧ : ∀ {n k} → Ty n k → Tree n
⟦ ⊥ ⟧         = ⊥
⟦ ⊤ ⟧         = ⊤
⟦ var x ⟧     = var x
⟦ σ ⟶ τ ⟧     = ♯ ⟦ σ ⟧ ⟶ ♯ ⟦ τ ⟧
⟦ μ (σ ⟶ τ) ⟧ = ♯ ⟦ forget σ / sub (μ (σ ⟶ τ)) ⟧ ⟶
                ♯ ⟦ forget τ / sub (μ (σ ⟶ τ)) ⟧
