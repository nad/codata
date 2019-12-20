------------------------------------------------------------------------
-- An example
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Example where

open import Codata.Musical.Notation
open import Data.Fin
open import Data.Nat

open import RecursiveTypes.Syntax
open import RecursiveTypes.Subtyping.Semantic.Coinductive

-- σ = μX. X ⟶ X.

σ : Ty 0
σ = μ var zero ⟶ var zero

-- τ = μX. (X ⟶ ⊥) ⟶ ⊤.

τ : Ty 0
τ = μ (var zero ⟶ ⊥) ⟶ ⊤

-- σ is a subtype of τ.

σ≤τ : σ ≤Coind τ
σ≤τ = ♯ (♯ σ≤τ ⟶ ♯ ⊥) ⟶ ♯ ⊤
