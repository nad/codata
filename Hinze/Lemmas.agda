------------------------------------------------------------------------
-- Some lemmas used by the other modules in this directory
------------------------------------------------------------------------

module Hinze.Lemmas where

open import Stream.Programs
open import Stream.Equality

open import Coinduction hiding (∞)
open import Relation.Binary.PropositionalEquality
open import Data.Function using (_∘_; flip)

------------------------------------------------------------------------
-- Some lemmas from Section 2.3 of Hinze's paper

-- See also Stream.Equality.≊-η.

⋎-∞ : ∀ {A} (x : A) → x ∞ ⋎ x ∞ ≊ x ∞
⋎-∞ x = ↓ refl ≺ ⋎-∞′
  where ⋎-∞′ ~ ♯₁ ⋎-∞ x

⋎-map : ∀ {A B} (⊟ : A → B) s t →
        ⊟ · s ⋎ ⊟ · t ≊ ⊟ · (s ⋎ t)
⋎-map ⊟ s t with P⇒′ s
⋎-map ⊟ s t | x ≺ s′ = ↓ refl ≺ ⋎-map′
  where ⋎-map′ ~ ♯₁ ⋎-map ⊟ t (♭₁ s′)

abide-law : ∀ {A B C} (⊞ : A → B → C) s₁ s₂ t₁ t₂ →
            s₁ ⟨ ⊞ ⟩ s₂ ⋎ t₁ ⟨ ⊞ ⟩ t₂ ≊ (s₁ ⋎ t₁) ⟨ ⊞ ⟩ (s₂ ⋎ t₂)
abide-law ⊞ s₁ s₂ t₁ t₂ with P⇒′ s₁ | P⇒′ s₂
abide-law ⊞ s₁ s₂ t₁ t₂ | x₁ ≺ s₁′ | x₂ ≺ s₂′ = ↓ refl ≺ abide-law′
  where abide-law′ ~ ♯₁ abide-law ⊞ t₁ t₂ (♭₁ s₁′) (♭₁ s₂′)

------------------------------------------------------------------------
-- Other lemmas

tailP-cong : ∀ {A} (xs ys : StreamProg A) →
             xs ≊ ys → tailP xs ≊ tailP ys
tailP-cong xs ys xs≈ys with P⇒′ xs | P⇒′ ys | ≅⇒≃ xs≈ys
tailP-cong xs ys xs≈ys | x ≺ xs′ | y ≺ ys′ | x≡y ≺ xs≈ys′ = ♭₁ xs≈ys′

map-fusion : ∀ {A B C} (f : B → C) (g : A → B) xs →
             f · g · xs ≊ (f ∘ g) · xs
map-fusion f g xs with P⇒′ xs
map-fusion f g xs | x ≺ xs′ = ↓ refl ≺ map-fusion′
  where map-fusion′ ~ ♯₁ map-fusion f g (♭₁ xs′)

zip-const-is-map : ∀ {A B C} (_∙_ : A → B → C) xs y →
                   xs ⟨ _∙_ ⟩ y ∞ ≊ (λ x → x ∙ y) · xs
zip-const-is-map _∙_ xs y with P⇒′ xs
zip-const-is-map _∙_ xs y | x ≺ xs′ = ↓ refl ≺ zip-const-is-map′
  where zip-const-is-map′ ~ ♯₁ zip-const-is-map _∙_ (♭₁ xs′) y

zip-flip : ∀ {A B C} (∙ : A → B → C) s t →
           s ⟨ ∙ ⟩ t ≊ t ⟨ flip ∙ ⟩ s
zip-flip ∙ s t with P⇒′ s | P⇒′ t
zip-flip ∙ s t | x ≺ s′ | y ≺ t′ = ↓ refl ≺ zip-flip′
  where zip-flip′ ~ ♯₁ zip-flip ∙ (♭₁ s′) (♭₁ t′)

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
