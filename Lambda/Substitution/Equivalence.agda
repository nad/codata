------------------------------------------------------------------------
-- The semantics given in OneSemantics and TwoSemantics are equivalent
------------------------------------------------------------------------

module Lambda.Substitution.Equivalence where

open import Codata.Musical.Notation

open import Lambda.Syntax
open WHNF
open import Lambda.Substitution.OneSemantics
open import Lambda.Substitution.TwoSemantics

⇒⟶⇓ : ∀ {n t} {v : Value n} → t ⇒ val v → t ⇓ v
⇒⟶⇓ val                 = val
⇒⟶⇓ (app t₁⇓ t₂⇓ t₁t₂⇒) = app (⇒⟶⇓ t₁⇓) (⇒⟶⇓ t₂⇓) (⇒⟶⇓ t₁t₂⇒)

⇒⊥⟶⇑ : ∀ {n} {t : Tm n} → t ⇒ ⊥ → t ⇑
⇒⊥⟶⇑ (·ˡ t₁⇑)            = ·ˡ (♯ (⇒⊥⟶⇑ (♭ t₁⇑)))
⇒⊥⟶⇑ (·ʳ t₁⇓ t₂⇑)        = ·ʳ (⇒⟶⇓ t₁⇓) (♯ (⇒⊥⟶⇑ (♭ t₂⇑)))
⇒⊥⟶⇑ (app t₁⇓ t₂⇓ t₁t₂⇒) = app (⇒⟶⇓ t₁⇓) (⇒⟶⇓ t₂⇓) (♯ (⇒⊥⟶⇑ (♭ t₁t₂⇒)))

⇓⟶⇒ : ∀ {n t} {v : Value n} → t ⇓ v → t ⇒ val v
⇓⟶⇒ val                 = val
⇓⟶⇒ (app t₁⇓ t₂⇓ t₁t₂⇓) = app (⇓⟶⇒ t₁⇓) (⇓⟶⇒ t₂⇓) (⇓⟶⇒ t₁t₂⇓)

⇑⟶⇒⊥ : ∀ {n} {t : Tm n} → t ⇑ → t ⇒ ⊥
⇑⟶⇒⊥ (·ˡ t₁⇑)            = ·ˡ (♯ (⇑⟶⇒⊥ (♭ t₁⇑)))
⇑⟶⇒⊥ (·ʳ t₁⇓ t₂⇑)        = ·ʳ (⇓⟶⇒ t₁⇓) (♯ (⇑⟶⇒⊥ (♭ t₂⇑)))
⇑⟶⇒⊥ (app t₁⇓ t₂⇓ t₁t₂⇓) = app (⇓⟶⇒ t₁⇓) (⇓⟶⇒ t₂⇓) (♯ (⇑⟶⇒⊥ (♭ t₁t₂⇓)))
