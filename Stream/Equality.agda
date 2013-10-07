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
infix  3 _≃_ _≅_ _≊_ _∎
infixr 2 _≊⟨_⟩_ _≡⟨_⟩_

mutual

  _≊_ : ∀ {A} (xs ys : Prog A) → Set1
  xs ≊ ys = ⟦ xs ⟧ ≅ ⟦ ys ⟧

  data _≅_ {A} : (xs ys : Stream A) → Set1 where
    _≺_          : ∀ {x y xs ys}
                   (x≡ : x ≡ y) (xs≈ : ∞ (♭ xs ≅ ♭ ys)) →
                   x ≺ xs ≅ y ≺ ys
    _≊⟨_⟩_       : ∀ xs {ys zs}
                   (xs≈ys : ⟦ xs ⟧ ≅ ys) (ys≈zs : ys ≅ zs) → ⟦ xs ⟧ ≅ zs
    _≡⟨_⟩_       : ∀ xs {ys zs}
                   (xs≡ys : ⟦ xs ⟧ ≡ ys) (ys≈zs : ys ≅ zs) → ⟦ xs ⟧ ≅ zs
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

data _≃_ {A} : (xs ys : Stream A) → Set1 where
  _≺_ : ∀ {x y xs ys}
        (x≡ : x ≡ y) (xs≈ : ♭ xs ≅ ♭ ys) → x ≺ xs ≃ y ≺ ys

≅⇒≃ : ∀ {A} {xs ys : Stream A} → xs ≅ ys → xs ≃ ys
≅⇒≃ (x≡ ≺ xs≈)                 = x≡ ≺ ♭ xs≈
≅⇒≃ (xs ≊⟨ xs≈ys ⟩ ys≈zs)      with whnf xs | ≅⇒≃ xs≈ys | ≅⇒≃ ys≈zs
≅⇒≃ (xs ≊⟨ xs≈ys ⟩ ys≈zs)      | x ≺ xs′ | x≡y ≺ xs≈ys′ | y≡z ≺ ys≈zs′ =
                                 trans x≡y y≡z ≺ (xs′ ≊⟨ xs≈ys′ ⟩ ys≈zs′)
≅⇒≃ (xs ≡⟨ refl ⟩ ys≈zs)       = ≅⇒≃ ys≈zs
≅⇒≃ (≅-sym xs≈ys)              with ≅⇒≃ xs≈ys
≅⇒≃ (≅-sym xs≈ys)              | x≡y ≺ xs≈ys′ = sym x≡y ≺ ≅-sym xs≈ys′
≅⇒≃ (·-cong f xs ys xs≈ys)     with whnf xs | whnf ys | ≅⇒≃ xs≈ys
≅⇒≃ (·-cong f xs ys xs≈ys)     | x ≺ xs′ | y ≺ ys′ | x≡y ≺ xs≈ys′ =
                                 cong f x≡y ≺ ·-cong f xs′ ys′ xs≈ys′
≅⇒≃ (⟨ ∙ ⟩-cong xs xs′ xs≈xs′
                ys ys′ ys≈ys′) with whnf xs | whnf xs′ | ≅⇒≃ xs≈xs′
                                  | whnf ys | whnf ys′ | ≅⇒≃ ys≈ys′
≅⇒≃ (⟨ ∙ ⟩-cong xs xs′ xs≈xs′
                ys ys′ ys≈ys′) | _ ≺ txs | _ ≺ txs′ | x≡y  ≺ txs≈txs′
                               | _ ≺ tys | _ ≺ tys′ | x≡y′ ≺ tys≈tys′ =
                                 cong₂ ∙ x≡y x≡y′ ≺
                                 ⟨ ∙ ⟩-cong txs txs′ txs≈txs′
                                            tys tys′ tys≈tys′
≅⇒≃ (⋎-cong xs xs′ xs≈xs′
            ys ys′ ys≈ys′)     with whnf xs | whnf xs′ | ≅⇒≃ xs≈xs′
≅⇒≃ (⋎-cong xs xs′ xs≈xs′
            ys ys′ ys≈ys′)     | _ ≺ txs | _ ≺ txs′ | x≡y ≺ txs≈txs′ =
                                 x≡y ≺ ⋎-cong ys  ys′  ys≈ys′
                                              txs txs′ txs≈txs′
≅⇒≃ (≺≺-cong [] [] refl
             ys ys′ ys≈ys′)    = ≅⇒≃ ys≈ys′
≅⇒≃ (≺≺-cong
      (x ∷ xs) .(_ ∷ _) refl
      ys ys′ ys≈ys′)           = refl ≺ ≺≺-cong xs xs refl ys ys′ ys≈ys′

mutual

  ≃⇒≈ : ∀ {A} {xs ys : Stream A} → xs ≃ ys → xs ≈ ys
  ≃⇒≈ (refl ≺ xs≈) = refl ≺ ♯ ≅⇒≈ xs≈

  ≅⇒≈ : ∀ {A} {xs ys : Stream A} → xs ≅ ys → xs ≈ ys
  ≅⇒≈ xs≈ = ≃⇒≈ (≅⇒≃ xs≈)

≊⇒≈ : ∀ {A} {xs ys : Prog A} → xs ≊ ys → ⟦ xs ⟧ ≈ ⟦ ys ⟧
≊⇒≈ = ≅⇒≈

≈⇒≅ : ∀ {A} {xs ys : Stream A} → xs ≈ ys → xs ≅ ys
≈⇒≅ (refl ≺ xs≈) = refl ≺ ♯ ≈⇒≅ (♭ xs≈)

_∎ : ∀ {A} (xs : Prog A) → xs ≊ xs
xs ∎ = ≈⇒≅ (Setoid.refl (Stream.setoid _))

≊-η : ∀ {A} (xs : Prog A) → xs ≊ headP xs ≺ ♯ tailP xs
≊-η xs with whnf xs
≊-η xs | x ≺ xs′ = refl ≺ ♯ (xs′ ∎)
