------------------------------------------------------------------------
-- Soundness

module RecursiveTypes.Soundness where

import Data.Nat as Nat; open Nat using (ℕ; zero; suc; _+_)
import Data.Fin as Fin; open Fin using (Fin; zero; suc)
import Data.Vec as Vec; open Vec using (Vec; []; _∷_)
open import Data.Function
open import Coinduction
open import Relation.Binary.PropositionalEquality

open import RecursiveTypes
open TySubst

------------------------------------------------------------------------
-- A lemma relating environments and substitutions

envToSub : ∀ {m n} → Env m n → Sub (n + m) m
envToSub ∅       = idˢ
envToSub (γ ▻ σ) = σ / envToSub γ ∷ envToSub γ

infixl 5 _▻_

data Env⁺ (m n : ℕ) : ℕ → Set where
  ∅   : Env⁺ m n 0
  _▻_ : ∀ {k} (γ : Env⁺ m n k) (σ : Ty (k + n + m)) → Env⁺ m n (suc k)

infixl 5 _⊕_

_⊕_ : ∀ {m n k} → Env m n → Env⁺ m n k → Env m (k + n)
γ₁ ⊕ ∅        = γ₁
γ₁ ⊕ (γ₂ ▻ σ) = (γ₁ ⊕ γ₂) ▻ σ

un⁺ : ∀ {k m n} → Env m n → Env⁺ m n k → Env m k
un⁺             γ₁ ∅        = ∅
un⁺ {k = suc k} γ₁ (γ₂ ▻ σ) = un⁺ γ₁ γ₂ ▻ σ / envToSub γ₁ ↑⋆ k

weaken-lemma : ∀ {m n} (γ : Env m n) {σ} τ →
               tree (γ ▻ σ) (VarSubst.weaken τ) ≈∞ tree γ τ
weaken-lemma γ ⊥           = ⊥
weaken-lemma γ ⊤           = ⊤
weaken-lemma γ (var x)     = {!var!}
weaken-lemma γ (τ₁ ⟶ τ₂)   = weaken-lemma′₁ ⟶ weaken-lemma′₂
                             where weaken-lemma′₁ ~ ♯ weaken-lemma γ τ₁
                                   weaken-lemma′₂ ~ ♯ weaken-lemma γ τ₂
weaken-lemma γ (ν τ₁ ⟶ τ₂) = weaken-lemma′₁ ⟶ weaken-lemma′₂
                             where weaken-lemma′₁ ~ ♯ {!!}
                                   weaken-lemma′₂ ~ ♯ {!!}

envToTree : ∀ {m n} → Env m (suc n) → Tree m
envToTree (γ ▻ τ) = tree γ τ

un⁺-⊕-lemma : ∀ {k m n}
              (γ₁ : Env m n) (γ₂ : Env⁺ m n k) (σ : Ty (k + n + m)) →
              envToTree (un⁺ γ₁ (γ₂ ▻ σ)) ≈∞ envToTree (γ₁ ⊕ γ₂ ▻ σ)
un⁺-⊕-lemma γ₁ γ₂ ⊥           = ⊥
un⁺-⊕-lemma γ₁ γ₂ ⊤           = ⊤
un⁺-⊕-lemma γ₁ γ₂ (σ₁ ⟶ σ₂)   = un⁺-⊕-lemma₁ ⟶ un⁺-⊕-lemma₂
                                where un⁺-⊕-lemma₁ ~ ♯ un⁺-⊕-lemma γ₁ γ₂ σ₁
                                      un⁺-⊕-lemma₂ ~ ♯ un⁺-⊕-lemma γ₁ γ₂ σ₂
un⁺-⊕-lemma γ₁ γ₂ (ν σ₁ ⟶ σ₂) = un⁺-⊕-lemma₁ ⟶ un⁺-⊕-lemma₂
                                where un⁺-⊕-lemma₁ ~ ♯ un⁺-⊕-lemma γ₁ (γ₂ ▻ ν σ₁ ⟶ σ₂) σ₁
                                      un⁺-⊕-lemma₂ ~ ♯ un⁺-⊕-lemma γ₁ (γ₂ ▻ ν σ₁ ⟶ σ₂) σ₂
un⁺-⊕-lemma ∅        ∅        (var x)       = subst (λ σ → tree ∅ σ ≈∞ var x)
                                                    (sym $ id-lemma′ x) var
un⁺-⊕-lemma (γ₁ ▻ σ) ∅        (var zero)    = un⁺-⊕-lemma γ₁ ∅ σ
un⁺-⊕-lemma (γ₁ ▻ σ) ∅        (var (suc x)) = un⁺-⊕-lemma γ₁ ∅ (var x)
un⁺-⊕-lemma γ₁       (γ₂ ▻ σ) (var zero)    = un⁺-⊕-lemma γ₁ γ₂ σ
un⁺-⊕-lemma γ₁       (γ₂ ▻ σ) (var (suc x)) = {!un⁺-⊕-lemma γ₁ γ₂ (var x)!}

env-sub-lemma : ∀ {n} (σ : Ty (suc n)) (τ : Ty n) →
                ⟦ σ [0≔ τ ] ⟧ ≈∞ tree (∅ ▻ τ) σ
env-sub-lemma σ τ = subst (λ χ → tree ∅ (σ / sub χ) ≈∞ tree (∅ ▻ τ) σ)
                         (id-lemma τ)
                         (un⁺-⊕-lemma (∅ ▻ τ) ∅ σ)

------------------------------------------------------------------------
-- Soundness

-- trans : ∀ {n} → Transitive (_≤Coind_ {n})
-- trans le₁ le₂ = {!!}

sound : ∀ {n} {σ τ : Ty n} → σ ≤ τ → σ ≤Coind τ
sound ⊥                     = ⊥
sound ⊤                     = ⊤
sound var                   = var
sound (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = sound₁ ⟶ sound₂
                              where sound₁ ~ ♯ sound (♭ τ₁≤σ₁)
                                    sound₂ ~ ♯ sound (♭ σ₂≤τ₂)
sound (unfold τ₁ τ₂)        = sound₁ ⟶ sound₂
                              where sound₁ ~ ♯ refl≤∞ (env-sub-lemma τ₁ (ν τ₁ ⟶ τ₂))
                                    sound₂ ~ ♯ refl≤∞ (sym≈∞ $ env-sub-lemma τ₂ (ν τ₁ ⟶ τ₂))
sound (fold τ₁ τ₂)          = sound₁ ⟶ sound₂
                              where sound₁ ~ ♯ refl≤∞ (sym≈∞ $ env-sub-lemma τ₁ (ν τ₁ ⟶ τ₂))
                                    sound₂ ~ ♯ refl≤∞ (env-sub-lemma τ₂ (ν τ₁ ⟶ τ₂))
sound (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = {!!} -- trans {i = τ₁} (sound τ₁≤τ₂) (sound τ₂≤τ₃)
