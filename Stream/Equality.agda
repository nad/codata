------------------------------------------------------------------------
-- A stream equality universe
------------------------------------------------------------------------

module Stream.Equality where

open import Coinduction
open import Stream hiding (_⋎_)
open import Stream.Programs
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Data.Vec using (Vec; []; _∷_)

infixr 5 _≺_
infix  4 ↓_
infix  3 _≃_ _≅_ _≊_ _∎
infixr 2 _≊⟨_⟩_ _≡⟨_⟩_

mutual

  _≊_ : ∀ {A} (xs ys : StreamProg A) → Set1
  xs ≊ ys = P⇒ xs ≅ P⇒ ys

  data _≃_ {A} : (xs ys : Stream A) → Set1 where
    _≺_ : ∀ {x y xs ys}
          (x≡ : x ≡ y) (xs≈ : ∞₁ (♭ xs ≅ ♭ ys)) → x ≺ xs ≃ y ≺ ys

  data _≅_ {A} : (xs ys : Stream A) → Set1 where
    ↓_           : ∀ {xs ys} (xs≈ : xs ≃ ys) → xs ≅ ys
    _≊⟨_⟩_       : ∀ xs {ys zs}
                   (xs≈ys : P⇒ xs ≅ ys) (ys≈zs : ys ≅ zs) → P⇒ xs ≅ zs
    _≡⟨_⟩_       : ∀ xs {ys zs}
                   (xs≡ys : P⇒ xs ≡ ys) (ys≈zs : ys ≅ zs) → P⇒ xs ≅ zs
    ≅-sym        : ∀ {xs ys} (xs≈ys : xs ≅ ys) → ys ≅ xs
    ·-cong       : ∀ {B}
                   (f : B → A) xs ys (xs≈ys : xs ≊ ys) →
                   f · xs ≊ f · ys
    ⟨_⟩-cong     : ∀ {B C} (_∙_ : B → C → A)
                   xs xs′ (xs≈xs′ : xs ≊ xs′)
                   ys ys′ (ys≈ys′ : ys ≊ ys′) →
                   xs ⟨ _∙_ ⟩ ys ≊ xs′ ⟨ _∙_ ⟩ ys′
    ⋎-cong       : ∀ xs xs′ (xs≈xs′ : xs ≊ xs′)
                          ys ys′ (ys≈ys′ : ys ≊ ys′) →
                   xs ⋎ ys ≊ xs′ ⋎ ys′
    ≺≺-cong      : ∀ {n}
                   (xs xs′ : Vec A n) (xs≡xs′ : xs ≡ xs′)
                   ys ys′ (ys≈ys′ : ys ≊ ys′) →
                   xs ≺≺ ys ≊ xs′ ≺≺ ys′

≅⇒≃ : ∀ {A} {xs ys : Stream A} → xs ≅ ys → xs ≃ ys
≅⇒≃ (↓ xs≈)                    = xs≈
≅⇒≃ (xs ≊⟨ xs≈ys ⟩ ys≈zs)      with P⇒′ xs | ≅⇒≃ xs≈ys | ≅⇒≃ ys≈zs
≅⇒≃ (xs ≊⟨ xs≈ys ⟩ ys≈zs)      | x ≺ xs′ | x≡y ≺ xs≈ys′ | y≡z ≺ ys≈zs′ =
                                 trans x≡y y≡z ≺ ♯₁ (♭₁ xs′ ≊⟨ ♭₁ xs≈ys′ ⟩ ♭₁ ys≈zs′)
≅⇒≃ (xs ≡⟨ refl ⟩ ys≈zs)       = ≅⇒≃ ys≈zs
≅⇒≃ (≅-sym xs≈ys)              with ≅⇒≃ xs≈ys
≅⇒≃ (≅-sym xs≈ys)              | x≡y ≺ xs≈ys′ = sym x≡y ≺ ♯₁ ≅-sym (♭₁ xs≈ys′)
≅⇒≃ (·-cong f xs ys xs≈ys)     with P⇒′ xs | P⇒′ ys | ≅⇒≃ xs≈ys
≅⇒≃ (·-cong f xs ys xs≈ys)     | x ≺ xs′ | y ≺ ys′ | x≡y ≺ xs≈ys′ =
                                 cong f x≡y ≺ ♯₁ ·-cong f (♭₁ xs′) (♭₁ ys′) (♭₁ xs≈ys′)
≅⇒≃ (⟨ ∙ ⟩-cong xs xs′ xs≈xs′
                ys ys′ ys≈ys′) with P⇒′ xs | P⇒′ xs′ | ≅⇒≃ xs≈xs′
                                  | P⇒′ ys | P⇒′ ys′ | ≅⇒≃ ys≈ys′
≅⇒≃ (⟨ ∙ ⟩-cong xs xs′ xs≈xs′
                ys ys′ ys≈ys′) | _ ≺ _   | _ ≺ _   | x≡y  ≺ xs≈ys
                               | _ ≺ xs″ | _ ≺ ys″ | x≡y′ ≺ xs≈ys′ =
                                 cong₂ ∙ x≡y x≡y′ ≺
                                 ♯₁ ⟨ ∙ ⟩-cong _ _ (♭₁ xs≈ys) (♭₁ xs″) (♭₁ ys″) (♭₁ xs≈ys′)
≅⇒≃ (⋎-cong xs xs′ xs≈xs′
            ys ys′ ys≈ys′)     with P⇒′ xs | P⇒′ xs′ | ≅⇒≃ xs≈xs′
≅⇒≃ (⋎-cong xs xs′ xs≈xs′
            ys ys′ ys≈ys′)     | _ ≺ _ | _ ≺ _ | x≡y ≺ txs≈txs′ =
                                 x≡y ≺ ♯₁ ⋎-cong ys ys′ ys≈ys′ _ _ (♭₁ txs≈txs′)
≅⇒≃ (≺≺-cong [] [] refl
             ys ys′ ys≈ys′)    = ≅⇒≃ ys≈ys′
≅⇒≃ (≺≺-cong
      (x ∷ xs) .(_ ∷ _) refl
      ys ys′ ys≈ys′)           = refl ≺ ♯₁ ≺≺-cong xs xs refl ys ys′ ys≈ys′

mutual

  ≃⇒≈ : ∀ {A} {xs ys : Stream A} → xs ≃ ys → xs ≈ ys
  ≃⇒≈ (refl ≺ xs≈) = _ ≺ ≃⇒≈′ where ≃⇒≈′ ~ ♯ ≅⇒≈ (♭₁ xs≈)

  ≅⇒≈ : ∀ {A} {xs ys : Stream A} → xs ≅ ys → xs ≈ ys
  ≅⇒≈ xs≈ = ≃⇒≈ (≅⇒≃ xs≈)

≊⇒≈ : ∀ {A} {xs ys : StreamProg A} → xs ≊ ys → P⇒ xs ≈ P⇒ ys
≊⇒≈ = ≅⇒≈

≈⇒≅ : ∀ {A} {xs ys : Stream A} → xs ≈ ys → xs ≅ ys
≈⇒≅ (x ≺ xs≈) = ↓ refl ≺ ≈⇒≅′ where ≈⇒≅′ ~ ♯₁ ≈⇒≅ (♭ xs≈)

_∎ : ∀ {A} (xs : StreamProg A) → xs ≊ xs
xs ∎ = ≈⇒≅ (Setoid.refl (Stream.setoid _))

≊-η : ∀ {A} (xs : StreamProg A) → xs ≊ ↓ headP xs ≺′ tailP xs
≊-η xs with P⇒′ xs
≊-η xs | x ≺ xs′ = ↓ refl ≺ ♯₁ (♭₁ xs′ ∎)
