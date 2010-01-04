------------------------------------------------------------------------
-- Some lemmas used by the other modules in this directory
------------------------------------------------------------------------

module Hinze.Lemmas where

open import Stream.Programs
open import Stream.Equality

open import Coinduction hiding (∞)
open import Relation.Binary.PropositionalEquality
open import Function using (_∘_; flip)

------------------------------------------------------------------------
-- Some lemmas from Section 2.3 of Hinze's paper

-- See also Stream.Equality.≊-η.

⋎-∞ : ∀ {A} (x : A) → x ∞ ⋎ x ∞ ≊ x ∞
⋎-∞ x = refl ≺ ♯ ⋎-∞ x

⋎-map : ∀ {A B} (⊟ : A → B) s t →
        ⊟ · s ⋎ ⊟ · t ≊ ⊟ · (s ⋎ t)
⋎-map ⊟ s t with whnf s
⋎-map ⊟ s t | x ≺ s′ = refl ≺ ♯ ⋎-map ⊟ t s′

abide-law : ∀ {A B C} (⊞ : A → B → C) s₁ s₂ t₁ t₂ →
            s₁ ⟨ ⊞ ⟩ s₂ ⋎ t₁ ⟨ ⊞ ⟩ t₂ ≊ (s₁ ⋎ t₁) ⟨ ⊞ ⟩ (s₂ ⋎ t₂)
abide-law ⊞ s₁ s₂ t₁ t₂ with whnf s₁ | whnf s₂
abide-law ⊞ s₁ s₂ t₁ t₂ | x₁ ≺ s₁′ | x₂ ≺ s₂′ =
  refl ≺ ♯ abide-law ⊞ t₁ t₂ s₁′ s₂′

------------------------------------------------------------------------
-- Other lemmas

tailP-cong : ∀ {A} (xs ys : Prog A) →
             xs ≊ ys → tailP xs ≊ tailP ys
tailP-cong xs ys xs≈ys with whnf xs | whnf ys | ≅⇒≃ xs≈ys
tailP-cong xs ys xs≈ys | x ≺ xs′ | y ≺ ys′ | x≡y ≺ xs≈ys′ = xs≈ys′

map-fusion : ∀ {A B C} (f : B → C) (g : A → B) xs →
             f · g · xs ≊ (f ∘ g) · xs
map-fusion f g xs with whnf xs
map-fusion f g xs | x ≺ xs′ = refl ≺ ♯ map-fusion f g xs′

zip-const-is-map : ∀ {A B C} (_∙_ : A → B → C) xs y →
                   xs ⟨ _∙_ ⟩ y ∞ ≊ (λ x → x ∙ y) · xs
zip-const-is-map _∙_ xs y with whnf xs
zip-const-is-map _∙_ xs y | x ≺ xs′ =
  refl ≺ ♯ zip-const-is-map _∙_ xs′ y

zip-flip : ∀ {A B C} (∙ : A → B → C) s t →
           s ⟨ ∙ ⟩ t ≊ t ⟨ flip ∙ ⟩ s
zip-flip ∙ s t with whnf s | whnf t
zip-flip ∙ s t | x ≺ s′ | y ≺ t′ = refl ≺ ♯ zip-flip ∙ s′ t′

zip-⋎-const : ∀ {A B C} (∙ : A → B → C) s t x →
              (s ⋎ t) ⟨ ∙ ⟩ x ∞ ≊ s ⟨ ∙ ⟩ x ∞ ⋎ t ⟨ ∙ ⟩ x ∞
zip-⋎-const _∙_ s t x =
  (s ⋎ t) ⟨ _∙_ ⟩ x ∞
                                         ≊⟨ zip-const-is-map _ (s ⋎ t) _ ⟩
  (λ y → y ∙ x) · (s ⋎ t)
                                         ≊⟨ ≅-sym (⋎-map (λ y → y ∙ x) s t) ⟩
  (λ y → y ∙ x) · s ⋎ (λ y → y ∙ x) · t
                                         ≊⟨ ≅-sym (⋎-cong (s ⟨ _∙_ ⟩ x ∞) ((λ y → y ∙ x) · s)
                                                          (zip-const-is-map _∙_ s x)
                                                      _ _ (zip-const-is-map _∙_ t x)) ⟩
  s ⟨ _∙_ ⟩ x ∞ ⋎ t ⟨ _∙_ ⟩ x ∞
                                         ∎

zip-const-⋎ : ∀ {A B C} (∙ : A → B → C) x s t →
              x ∞ ⟨ ∙ ⟩ (s ⋎ t) ≊ x ∞ ⟨ ∙ ⟩ s ⋎ x ∞ ⟨ ∙ ⟩ t
zip-const-⋎ ∙ x s t =
  x ∞ ⟨ ∙ ⟩ (s ⋎ t)
                                       ≊⟨ zip-flip ∙ (x ∞) (s ⋎ t) ⟩
  (s ⋎ t) ⟨ flip ∙ ⟩ x ∞
                                       ≊⟨ zip-⋎-const (flip ∙) s t x ⟩
  s ⟨ flip ∙ ⟩ x ∞ ⋎ t ⟨ flip ∙ ⟩ x ∞
                                       ≊⟨ ≅-sym (⋎-cong (x ∞ ⟨ ∙ ⟩ s) (s ⟨ flip ∙ ⟩ x ∞)
                                                        (zip-flip ∙ (x ∞) s)
                                                    _ _ (zip-flip ∙ (x ∞) t)) ⟩
  x ∞ ⟨ ∙ ⟩ s ⋎ x ∞ ⟨ ∙ ⟩ t
                                       ∎
