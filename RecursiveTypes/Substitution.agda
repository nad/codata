------------------------------------------------------------------------
-- Substitutions
------------------------------------------------------------------------

module RecursiveTypes.Substitution where

open import Data.Fin.Substitution
open import Data.Fin.Substitution.Lemmas
open import Data.Nat
open import Data.Vec
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl; sym; cong₂)
open PropEq.≡-Reasoning
open import Data.Star using (Star; ε; _◅_; _▻_)

open import RecursiveTypes.Syntax

-- Code for applying substitutions.

module TyApp {T} (l : Lift T Ty) where
  open Lift l hiding (var)

  -- Applies a substitution to a recursive type.

  infixl 8 _/_

  _/_ : ∀ {m n} → Ty m → Sub T m n → Ty n
  ⊥       / ρ = ⊥
  ⊤       / ρ = ⊤
  var x   / ρ = lift (lookup x ρ)
  σ ⟶ τ   / ρ = (σ / ρ) ⟶ (τ / ρ)
  ν σ ⟶ τ / ρ = ν (σ / ρ ↑) ⟶ (τ / ρ ↑)

  open Application (record { _/_ = _/_ }) using (_/✶_)

  -- Some lemmas about _/_.

  ⊥-/✶-↑✶ : ∀ k {m n} (ρs : Subs T m n) → ⊥ /✶ ρs ↑✶ k ≡ ⊥
  ⊥-/✶-↑✶ k ε        = refl
  ⊥-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (⊥-/✶-↑✶ k ρs) refl

  ⊤-/✶-↑✶ : ∀ k {m n} (ρs : Subs T m n) → ⊤ /✶ ρs ↑✶ k ≡ ⊤
  ⊤-/✶-↑✶ k ε        = refl
  ⊤-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (⊤-/✶-↑✶ k ρs) refl

  ⟶-/✶-↑✶ : ∀ k {m n σ τ} (ρs : Subs T m n) →
            σ ⟶ τ /✶ ρs ↑✶ k ≡ (σ /✶ ρs ↑✶ k) ⟶ (τ /✶ ρs ↑✶ k)
  ⟶-/✶-↑✶ k ε        = refl
  ⟶-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (⟶-/✶-↑✶ k ρs) refl

  ν⟶-/✶-↑✶ : ∀ k {m n σ τ} (ρs : Subs T m n) →
             ν σ ⟶ τ /✶ ρs ↑✶ k ≡
             ν (σ /✶ ρs ↑✶ suc k) ⟶ (τ /✶ ρs ↑✶ suc k)
  ν⟶-/✶-↑✶ k ε        = refl
  ν⟶-/✶-↑✶ k (ρ ◅ ρs) = cong₂ _/_ (ν⟶-/✶-↑✶ k ρs) refl

tySubst : TermSubst Ty
tySubst = record { var = var; app = TyApp._/_ }

open TermSubst tySubst hiding (var)

-- σ [0≔ τ ] replaces all occurrences of variable 0 in σ with τ.

infix 8 _[0≔_]

_[0≔_] : ∀ {n} → Ty (suc n) → Ty n → Ty n
σ [0≔ τ ] = σ / sub τ

-- Substitution lemmas.

tyLemmas : TermLemmas Ty
tyLemmas = record
  { termSubst = tySubst
  ; app-var   = refl
  ; /✶-↑✶     = Lemma./✶-↑✶
  }
  where
  module Lemma {T₁ T₂} {lift₁ : Lift T₁ Ty} {lift₂ : Lift T₂ Ty} where

    open Lifted lift₁ using () renaming (_↑✶_ to _↑✶₁_; _/✶_ to _/✶₁_)
    open Lifted lift₂ using () renaming (_↑✶_ to _↑✶₂_; _/✶_ to _/✶₂_)

    /✶-↑✶ : ∀ {m n} (ρs₁ : Subs T₁ m n) (ρs₂ : Subs T₂ m n) →
            (∀ k {x} → var x /✶₁ ρs₁ ↑✶₁ k ≡ var x /✶₂ ρs₂ ↑✶₂ k) →
            ∀ k {t} → t /✶₁ ρs₁ ↑✶₁ k ≡ t /✶₂ ρs₂ ↑✶₂ k
    /✶-↑✶ ρs₁ ρs₂ hyp k {⊥} = begin
      ⊥ /✶₁ ρs₁ ↑✶₁ k  ≡⟨ TyApp.⊥-/✶-↑✶ _ k ρs₁ ⟩
      ⊥                ≡⟨ sym (TyApp.⊥-/✶-↑✶ _ k ρs₂) ⟩
      ⊥ /✶₂ ρs₂ ↑✶₂ k  ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k {⊤} = begin
      ⊤ /✶₁ ρs₁ ↑✶₁ k  ≡⟨ TyApp.⊤-/✶-↑✶ _ k ρs₁ ⟩
      ⊤                ≡⟨ sym (TyApp.⊤-/✶-↑✶ _ k ρs₂) ⟩
      ⊤ /✶₂ ρs₂ ↑✶₂ k  ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k {var x} = hyp k
    /✶-↑✶ ρs₁ ρs₂ hyp k {σ ⟶ τ} = begin
      σ ⟶ τ /✶₁ ρs₁ ↑✶₁ k                    ≡⟨ TyApp.⟶-/✶-↑✶ _ k ρs₁ ⟩
      (σ /✶₁ ρs₁ ↑✶₁ k) ⟶ (τ /✶₁ ρs₁ ↑✶₁ k)  ≡⟨ cong₂ _⟶_ (/✶-↑✶ ρs₁ ρs₂ hyp k)
                                                          (/✶-↑✶ ρs₁ ρs₂ hyp k) ⟩
      (σ /✶₂ ρs₂ ↑✶₂ k) ⟶ (τ /✶₂ ρs₂ ↑✶₂ k)  ≡⟨ sym (TyApp.⟶-/✶-↑✶ _ k ρs₂) ⟩
      σ ⟶ τ /✶₂ ρs₂ ↑✶₂ k                    ∎
    /✶-↑✶ ρs₁ ρs₂ hyp k {ν σ ⟶ τ} = begin
      ν σ ⟶ τ /✶₁ ρs₁ ↑✶₁ k                            ≡⟨ TyApp.ν⟶-/✶-↑✶ _ k ρs₁ ⟩
      ν (σ /✶₁ ρs₁ ↑✶₁ suc k) ⟶ (τ /✶₁ ρs₁ ↑✶₁ suc k)  ≡⟨ cong₂ ν_⟶_ (/✶-↑✶ ρs₁ ρs₂ hyp (suc k))
                                                                     (/✶-↑✶ ρs₁ ρs₂ hyp (suc k)) ⟩
      ν (σ /✶₂ ρs₂ ↑✶₂ suc k) ⟶ (τ /✶₂ ρs₂ ↑✶₂ suc k)  ≡⟨ sym (TyApp.ν⟶-/✶-↑✶ _ k ρs₂) ⟩
      ν σ ⟶ τ /✶₂ ρs₂ ↑✶₂ k                            ∎

open TermLemmas tyLemmas public hiding (var)
