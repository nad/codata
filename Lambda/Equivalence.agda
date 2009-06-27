------------------------------------------------------------------------
-- The semantics given in OneSemantics and TwoSemantics are equivalent
------------------------------------------------------------------------

module Lambda.Equivalence where

open import Coinduction

open import Lambda.Syntax
open import Lambda.OneSemantics
open import Lambda.TwoSemantics

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
