------------------------------------------------------------------------
-- The two coinductive definitions of subtyping are equivalent

module RecursiveTypes.Equivalence where

import Data.Nat as Nat; open Nat using (ℕ; zero; suc)
open import Coinduction
open import Data.Function

open import RecursiveTypes

mutual

  ≤∞⇒≤↓ : ∀ {n} {σ τ : Tree n} → σ ≤∞ τ → σ ≤↓ τ
  ≤∞⇒≤↓ le              zero    = ⊥
  ≤∞⇒≤↓ ⊥               (suc k) = ⊥
  ≤∞⇒≤↓ ⊤               (suc k) = ⊤
  ≤∞⇒≤↓ var             (suc k) = refl
  ≤∞⇒≤↓ (τ₁≤σ₁ ⟶ σ₂≤τ₂) (suc k) = ≤∞⇒≤↑ (♭ τ₁≤σ₁) k ⟶ ≤∞⇒≤↓ (♭ σ₂≤τ₂) k

  ≤∞⇒≤↑ : ∀ {n} {σ τ : Tree n} → σ ≤∞ τ → σ ≤↑ τ
  ≤∞⇒≤↑ le              zero    = ⊤
  ≤∞⇒≤↑ ⊥               (suc k) = ⊥
  ≤∞⇒≤↑ ⊤               (suc k) = ⊤
  ≤∞⇒≤↑ var             (suc k) = refl
  ≤∞⇒≤↑ (τ₁≤σ₁ ⟶ σ₂≤τ₂) (suc k) = ≤∞⇒≤↓ (♭ τ₁≤σ₁) k ⟶ ≤∞⇒≤↑ (♭ σ₂≤τ₂) k

domain : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : FinTree n} →
        (σ₁ ⟶ σ₂) ≤Fin (τ₁ ⟶ τ₂) → σ₂ ≤Fin τ₂
domain refl            = refl
domain (τ₁≤σ₁ ⟶ σ₂≤τ₂) = σ₂≤τ₂

codomain : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : FinTree n} →
       (σ₁ ⟶ σ₂) ≤Fin (τ₁ ⟶ τ₂) → τ₁ ≤Fin σ₁
codomain refl            = refl
codomain (τ₁≤σ₁ ⟶ σ₂≤τ₂) = τ₁≤σ₁

mutual

  ≤↑⇒≤∞ : ∀ {n} (σ τ : Tree n) → σ ≤↓ τ → σ ≤∞ τ
  ≤↑⇒≤∞ ⊥ τ le = ⊥
  ≤↑⇒≤∞ ⊤ ⊥ le with le 1
  ... | ()
  ≤↑⇒≤∞ ⊤ ⊤ le = ⊤
  ≤↑⇒≤∞ ⊤ (var x) le with le 1
  ... | ()
  ≤↑⇒≤∞ ⊤ (σ ⟶ τ) le with le 1
  ... | ()
  ≤↑⇒≤∞ (var x) ⊥ le with le 1
  ... | ()
  ≤↑⇒≤∞ (var x) ⊤ le = ⊤
  ≤↑⇒≤∞ (var x) (var x′) le with le 1
  ≤↑⇒≤∞ (var x) (var .x) le | refl = var
  ≤↑⇒≤∞ (var x) (σ ⟶ τ) le with le 1
  ... | ()
  ≤↑⇒≤∞ (σ₁ ⟶ τ₁) ⊥ le with le 1
  ... | ()
  ≤↑⇒≤∞ (σ₁ ⟶ τ₁) ⊤ le = ⊤
  ≤↑⇒≤∞ (σ₁ ⟶ τ₁) (var x) le with le 1
  ... | ()
  ≤↑⇒≤∞ (σ₁ ⟶ τ₁) (σ₂ ⟶ τ₂) le = ₁ ⟶ ₂
    where
    ₁ ~ ♯ ≤↓⇒≤∞ (♭ σ₂) (♭ σ₁) (codomain ∘ le ∘ suc)
    ₂ ~ ♯ ≤↑⇒≤∞ (♭ τ₁) (♭ τ₂) (domain   ∘ le ∘ suc)

  ≤↓⇒≤∞ : ∀ {n} (σ τ : Tree n) → σ ≤↑ τ → σ ≤∞ τ
  ≤↓⇒≤∞ ⊥ τ le = ⊥
  ≤↓⇒≤∞ ⊤ ⊥ le with le 1
  ... | ()
  ≤↓⇒≤∞ ⊤ ⊤ le = ⊤
  ≤↓⇒≤∞ ⊤ (var x) le with le 1
  ... | ()
  ≤↓⇒≤∞ ⊤ (σ ⟶ τ) le with le 1
  ... | ()
  ≤↓⇒≤∞ (var x) ⊥ le with le 1
  ... | ()
  ≤↓⇒≤∞ (var x) ⊤ le = ⊤
  ≤↓⇒≤∞ (var x) (var x′) le with le 1
  ≤↓⇒≤∞ (var x) (var .x) le | refl = var
  ≤↓⇒≤∞ (var x) (σ ⟶ τ) le with le 1
  ... | ()
  ≤↓⇒≤∞ (σ₁ ⟶ τ₁) ⊥ le with le 1
  ... | ()
  ≤↓⇒≤∞ (σ₁ ⟶ τ₁) ⊤ le = ⊤
  ≤↓⇒≤∞ (σ₁ ⟶ τ₁) (var x) le with le 1
  ... | ()
  ≤↓⇒≤∞ (σ₁ ⟶ τ₁) (σ₂ ⟶ τ₂) le = ₁ ⟶ ₂
    where
    ₁ ~ ♯ ≤↑⇒≤∞ (♭ σ₂) (♭ σ₁) (codomain ∘ le ∘ suc)
    ₂ ~ ♯ ≤↓⇒≤∞ (♭ τ₁) (♭ τ₂) (domain   ∘ le ∘ suc)

AC⇒Coind : ∀ {n} {σ τ : Ty n} → σ ≤AC τ → σ ≤Coind τ
AC⇒Coind = ≤↑⇒≤∞ _ _

Coind⇒AC : ∀ {n} {σ τ : Ty n} → σ ≤Coind τ → σ ≤AC τ
Coind⇒AC = ≤∞⇒≤↓
