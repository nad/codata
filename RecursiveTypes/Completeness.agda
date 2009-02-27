------------------------------------------------------------------------
-- Completeness

module RecursiveTypes.Completeness where

-- import Data.Nat as Nat; open Nat using (ℕ; zero; suc; _+_)
-- import Data.Fin as Fin; open Fin using (Fin; zero; suc)
-- import Data.Vec as Vec; open Vec using (Vec; []; _∷_)
-- open import Data.Function
open import Coinduction
-- open import Relation.Binary.PropositionalEquality

open import RecursiveTypes
-- open TySubst

complete : ∀ {n} (σ τ : Ty n) → σ ≤Coind τ → σ ≤ τ
complete ⊥           _           _               = ⊥
complete _           ⊤           _               = ⊤
complete ⊤           ⊥           ()
complete ⊤           (var x)     ()
complete ⊤           (σ ⟶ τ)     ()
complete ⊤           (ν σ ⟶ τ)   ()
complete (var x)     ⊥           ()
complete (var x)     (var .x)    var             = var
complete (var x)     (σ ⟶ τ)     ()
complete (var x)     (ν σ ⟶ τ)   ()
complete (σ₁ ⟶ σ₂)   ⊥           ()
complete (σ₁ ⟶ σ₂)   (var x)     ()
complete (σ₁ ⟶ σ₂)   (τ₁ ⟶ τ₂)   (τ₁≤σ₁ ⟶ σ₂≤τ₂) = complete₁ ⟶ complete₂
                                                   where complete₁ ~ ♯ complete τ₁ σ₁ (♭ τ₁≤σ₁)
                                                         complete₂ ~ ♯ complete σ₂ τ₂ (♭ σ₂≤τ₂)
complete (σ₁ ⟶ σ₂)   (ν τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) = σ₁ ⟶ σ₂                                      ≤⟨ complete₁ ⟶ complete₂ ⟩
                                                   (τ₁ [0≔ ν τ₁ ⟶ τ₂ ]) ⟶ (τ₂ [0≔ ν τ₁ ⟶ τ₂ ])  ≤⟨ fold τ₁ τ₂ ⟩
                                                   ν τ₁ ⟶ τ₂                                    ∎
                                                   where complete₁ ~ ♯ complete (τ₁ [0≔ ν τ₁ ⟶ τ₂ ]) σ₁ {!♭ τ₁≤σ₁!}
                                                         complete₂ ~ ♯ complete σ₂ (τ₂ [0≔ ν τ₁ ⟶ τ₂ ]) {!♭ σ₂≤τ₂!}

complete (ν σ₁ ⟶ σ₂) ⊥           ()
complete (ν σ₁ ⟶ σ₂) (var x)     ()
complete (ν σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂)   (τ₁≤σ₁ ⟶ σ₂≤τ₂) = {!!}
complete (ν σ₁ ⟶ σ₂) (ν τ₁ ⟶ τ₂) (τ₁≤σ₁ ⟶ σ₂≤τ₂) = {!!}
