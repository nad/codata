------------------------------------------------------------------------
-- A stream equality universe
------------------------------------------------------------------------

module Stream.Equality where

open import Stream
open import Stream.Programs
open import Relation.Binary.PropositionalEquality

infixr 5 _≺_
infix  4 ↓_
infix  3 _≃_ _≅_ _≊_ _∎ _▯
infixr 2 _≈⟨_⟩_ _≊⟨_⟩_ _≡⟨_⟩_ _≣⟨_⟩_

mutual

  _≊_ : forall {A} (xs ys : StreamProg A) -> Set1
  xs ≊ ys = P⇒ xs ≅ P⇒ ys

  codata _≃_ {A} (xs ys : Stream A) : Set1 where
    _≺_ : (x≡ : head xs ≡ head ys) (xs≈ : tail xs ≅ tail ys) ->
          xs ≃ ys

  data _≅_ {A} : (xs ys : Stream A) -> Set1 where
    ↓_           : forall {xs ys} (xs≈ : xs ≃ ys) -> xs ≅ ys
    _≈⟨_⟩_       : forall xs {ys zs}
                   (xs≈ys : xs ≅ ys) (ys≈zs : ys ≅ zs) -> xs ≅ zs
    _≊⟨_⟩_       : forall xs {ys zs}
                   (xs≈ys : P⇒ xs ≅ ys) (ys≈zs : ys ≅ zs) -> P⇒ xs ≅ zs
    _≡⟨_⟩_       : forall xs {ys zs}
                   (xs≡ys : xs ≡ ys) (ys≈zs : ys ≅ zs) -> xs ≅ zs
    _≣⟨_⟩_       : forall xs {ys zs}
                   (xs≡ys : P⇒ xs ≡ ys) (ys≈zs : ys ≅ zs) -> P⇒ xs ≅ zs
    sym′         : forall {xs ys} (xs≈ys : xs ≅ ys) -> ys ≅ xs
    $-cong       : forall {B}
                   (f : B -> A) xs ys (xs≈ys : xs ≊ ys) ->
                   f $ xs ≊ f $ ys
    ⟨_⟩-cong     : forall {B C} (_∙_ : B -> C -> A)
                   xs xs′ (xs≈xs′ : xs ≊ xs′)
                   ys ys′ (ys≈ys′ : ys ≊ ys′) ->
                   xs ⟨ _∙_ ⟩ ys ≊ xs′ ⟨ _∙_ ⟩ ys′

≅⇒≃ : forall {A} {xs ys : Stream A} -> xs ≅ ys -> xs ≃ ys
≅⇒≃ (↓ xs≈)                    = xs≈
≅⇒≃ (xs ≈⟨ xs≈ys ⟩ ys≈zs)      with ≅⇒≃ xs≈ys | ≅⇒≃ ys≈zs
≅⇒≃ (xs ≈⟨ xs≈ys ⟩ ys≈zs)      | x≡y ≺ xs≈ys′ | y≡z ≺ ys≈zs′ =
                                 ≡-trans x≡y y≡z ≺ (tail xs ≈⟨ xs≈ys′ ⟩ ys≈zs′)
≅⇒≃ (xs ≊⟨ xs≈ys ⟩ ys≈zs)      with P⇒′ xs | ≅⇒≃ xs≈ys | ≅⇒≃ ys≈zs
≅⇒≃ (xs ≊⟨ xs≈ys ⟩ ys≈zs)      | x ≺ xs′ | x≡y ≺ xs≈ys′ | y≡z ≺ ys≈zs′ =
                                 ≡-trans x≡y y≡z ≺ (xs′ ≊⟨ xs≈ys′ ⟩ ys≈zs′)
≅⇒≃ (xs ≡⟨ ≡-refl ⟩ ys≈zs)     = ≅⇒≃ ys≈zs
≅⇒≃ (xs ≣⟨ ≡-refl ⟩ ys≈zs)     = ≅⇒≃ ys≈zs
≅⇒≃ (sym′ xs≈ys)               with ≅⇒≃ xs≈ys
≅⇒≃ (sym′ xs≈ys)               | x≡y ≺ xs≈ys′ = ≡-sym x≡y ≺ sym′ xs≈ys′
≅⇒≃ ($-cong f xs ys xs≈ys)     with P⇒′ xs | P⇒′ ys | ≅⇒≃ xs≈ys
≅⇒≃ ($-cong f xs ys xs≈ys)     | x ≺ xs′ | y ≺ ys′ | x≡y ≺ xs≈ys′ =
                                 ≡-cong f x≡y ≺ $-cong f xs′ ys′ xs≈ys′
≅⇒≃ (⟨ ∙ ⟩-cong xs xs′ xs≈xs′
                ys ys′ ys≈ys′) with P⇒′ xs | P⇒′ xs′ | ≅⇒≃ xs≈xs′
                                  | P⇒′ ys | P⇒′ ys′ | ≅⇒≃ ys≈ys′
≅⇒≃ (⟨ ∙ ⟩-cong xs xs′ xs≈xs′
                ys ys′ ys≈ys′) | _ ≺ _ | _ ≺ _ | x≡y  ≺ xs≈ys
                               | _ ≺ _ | _ ≺ _ | x≡y′ ≺ xs≈ys′ =
                                 ≡-cong₂ ∙ x≡y x≡y′ ≺
                                 ⟨ ∙ ⟩-cong _ _ xs≈ys _ _ xs≈ys′

≃⇒≈ : forall {A} {xs ys : Stream A} -> xs ≃ ys -> xs ≈ ys
≃⇒≈ (x≡ ≺ xs≈) ~ x≡ ≺ ≃⇒≈ (≅⇒≃ xs≈)

≅⇒≈ : forall {A} {xs ys : Stream A} -> xs ≅ ys -> xs ≈ ys
≅⇒≈ xs≈ = ≃⇒≈ (≅⇒≃ xs≈)

≊⇒≈ : forall {A} {xs ys : StreamProg A} -> xs ≊ ys -> P⇒ xs ≈ P⇒ ys
≊⇒≈ = ≅⇒≈

≈⇒≅ : forall {A} {xs ys : Stream A} -> xs ≈ ys -> xs ≅ ys
≈⇒≅ (x≡ ≺ xs≈) ~ ↓ x≡ ≺ ≈⇒≅ xs≈

_∎ : forall {A} (xs : Stream A) -> xs ≅ xs
xs ∎ = ≈⇒≅ refl

_▯ : forall {A} (xs : StreamProg A) -> xs ≊ xs
xs ▯ = P⇒ xs ∎
