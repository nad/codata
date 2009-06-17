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

data Sub? : Guarded → ℕ → ℕ → Set where
  guarded   : ∀ {n} → Sub? guarded n n
  unguarded : ∀ {m n} (ρ : Sub (flip₁ Ty guarded) m n) →
              Sub? unguarded m n

sub! : ∀ {g m n} → Sub? g m n → Sub (flip₁ Ty guarded) m n
sub! guarded       = id
sub! (unguarded ρ) = ρ

sub? : ∀ g {n} → Sub? g n n
sub? guarded   = guarded
sub? unguarded = unguarded id

⟦_⟧′ : ∀ {g m n} → Ty m g → Sub? g m n → Tree n
⟦ ⊥ ⟧′     _       = ⊥
⟦ ⊤ ⟧′     _       = ⊤
⟦ var x ⟧′ guarded = var x
⟦ σ ⟶ τ ⟧′ ρ       = ♯ ⟦ forget σ / sub! ρ ⟧′ guarded ⟶
                     ♯ ⟦ forget τ / sub! ρ ⟧′ guarded
⟦ μ σ ⟧′   ρ       = ⟦ σ ⟧′ (unguarded (sub (μ σ) ⊙ sub! ρ))

⟦_⟧ : ∀ {g n} → Ty n g → Tree n
⟦ σ ⟧ = ⟦ σ ⟧′ (sub? _)
