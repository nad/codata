------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------

-- Using Conor McBride's technique from "Type-Preserving Renaming and
-- Substitution".

module RecursiveTypes.Substitution where

open import Data.Nat
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec as Vec
import Data.Vec.Properties as VecProp
open import Data.Function
open import Relation.Binary.PropositionalEquality

open import RecursiveTypes.Syntax

-- Substitutions of Ts for variables.

module Subst (T : ℕ → Set)
             (vr : ∀ {n} → Fin n → T n)
             (wk : ∀ {n} → T n → T (suc n))
             (ty : ∀ {n} → T n → Ty n)
             where

  infix  9 _↑
  infixl 8 _/_
  infix 8 _[0≔_]

  -- A Sub m n, when applied to something with at most m variables,
  -- yields something with at most n variables.

  Sub : ℕ → ℕ → Set
  Sub m n = Vec (T n) m

  -- Weakening of substitutions.

  wkˢ : ∀ {m n} → Sub m n → Sub m (suc n)
  wkˢ = map wk

  -- Lifting.

  _↑ : ∀ {m n} → Sub m n → Sub (suc m) (suc n)
  ρ ↑ = vr zero ∷ wkˢ ρ

  -- The identity substitution.

  idˢ : ∀ {n} → Sub n n
  idˢ {zero}  = []
  idˢ {suc n} = idˢ ↑

  -- A substitution which only replaces the first variable.

  sub : ∀ {n} → T n → Sub (suc n) n
  sub t = t ∷ idˢ

  -- Application of a substitution to a recursive type.

  _/_ : ∀ {m n} → Ty m → Sub m n → Ty n
  ⊥       / ρ = ⊥
  ⊤       / ρ = ⊤
  var x   / ρ = ty (lookup x ρ)
  σ ⟶ τ   / ρ = (σ / ρ) ⟶ (τ / ρ)
  ν σ ⟶ τ / ρ = ν (σ / ρ ↑) ⟶ (τ / ρ ↑)

  -- Weakening of a recursive type.

  weaken : ∀ {n} → Ty n → Ty (suc n)
  weaken τ = τ / wkˢ idˢ

  -- σ [0≔ τ ] replaces all occurrences of variable 0 in σ with τ.

  _[0≔_] : ∀ {n} → Ty (suc n) → T n → Ty n
  σ [0≔ τ ] = σ / sub τ

-- Variable substitutions.

module VarSubst = Subst Fin id  suc             var

-- Type substitutions.

module TySubst  = Subst Ty  var VarSubst.weaken id
