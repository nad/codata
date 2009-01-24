------------------------------------------------------------------------
-- A formalisation of some definitions and laws from Section 2.4 of
-- Ralf Hinze's paper "Streams and Unique Fixed Points"
------------------------------------------------------------------------

-- Note: Using the approach of Stream.Programs and Stream.Equality the
-- proofs look just like Hinze's, but they are based on guarded
-- coinduction rather than relying (directly) on universality.

-- Also note that the formalisation can be simplified by defining the
-- streams differently. See Hinze.Simplified.

module Hinze.Section2-4 where

open import Stream.Programs
open import Stream.Equality
open import Stream.Pointwise
open import Hinze.Lemmas

open import Coinduction hiding (∞)
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (_≡⟨_⟩_ to _=⟨_⟩_; _∎ to _QED)
open import Algebra.Structures
import Data.Nat.Properties as Nat
private
  module CS = IsCommutativeSemiring _ Nat.isCommutativeSemiring
open import Data.Product

------------------------------------------------------------------------
-- Definitions

nat : StreamProg ℕ
nat = ↓ 0 ≺ nat′
  where nat′ ~ ♯₁ (nat ⟨ _+_ ⟩ 1 ∞)

2*nat   = 2 ∞ ⟨ _*_ ⟩ nat
2*nat+1 = 2*nat ⟨ _+_ ⟩ 1 ∞

fac : StreamProg ℕ
fac = ↓ 1 ≺ fac′
  where fac′ ~ ♯₁ ((nat ⟨ _+_ ⟩ 1 ∞) ⟨ _*_ ⟩ fac)

fib : StreamProg ℕ
fib = ↓ 0 ≺ fib′
  where fib′ ~ ♯₁ (fib ⟨ _+_ ⟩ (↓ 1 ≺ ♯₁ fib))

bin : StreamProg ℕ
bin = ↓ 0 ≺ bin′
  where bin′ ~ ♯₁ ((2 ∞ ⟨ _*_ ⟩ bin) ⟨ _+_ ⟩ 1 ∞ ⋎
                   (2 ∞ ⟨ _*_ ⟩ bin) ⟨ _+_ ⟩ 2 ∞)

------------------------------------------------------------------------
-- Laws and properties

const-is-∞ : ∀ {A} {x : A} {xs} →
             xs ≊ ↓ x ≺′ xs → xs ≊ x ∞
const-is-∞ {x = x} {xs} eq =
  xs
              ≊⟨ eq ⟩
  ↓ x ≺′ xs
              ≊⟨ ↓ refl ≺ coih ⟩
  ↓ x ≺′ x ∞
              ≡⟨ refl ⟩
  x ∞
              ∎
  where coih ~ ♯₁ const-is-∞ eq

nat-lemma₁ : ↓ 0 ≺′ 2*nat+1 ⋎ 2*nat ⟨ _+_ ⟩ 2 ∞ ≊ 2*nat ⋎ 2*nat+1
nat-lemma₁ =
  ↓ 0 ≺′ 2*nat+1 ⋎ 2*nat ⟨ _+_ ⟩ 2 ∞
                                                  ≊⟨ ↓ refl ≺ ♯₁ ⋎-cong 2*nat+1 2*nat+1 (2*nat+1 ∎)
                                                                        (2*nat ⟨ _+_ ⟩ 2 ∞)
                                                                        (2 ∞ ⟨ _*_ ⟩ (nat ⟨ _+_ ⟩ 1 ∞))
                                                                        (lemma (2 ∞) nat) ⟩
  ↓ 0 ≺′ 2*nat+1 ⋎ 2 ∞ ⟨ _*_ ⟩ (nat ⟨ _+_ ⟩ 1 ∞)
                                                  ≡⟨ refl ⟩
  2*nat ⋎ 2*nat+1
                                                  ∎
  where
  lemma : ∀ s t →
          (s ⟨ _*_ ⟩ t) ⟨ _+_ ⟩ s ≊ s ⟨ _*_ ⟩ (t ⟨ _+_ ⟩ 1 ∞)
  lemma = pointwise 2 (λ s t → (s ⟨ _*_ ⟩ t) ⟨ _+_ ⟩ s)
                      (λ s t → s ⟨ _*_ ⟩ (t ⟨ _+_ ⟩ 1 ∞))
                      (λ m n → sym (begin
                         m * (n + 1)
                                        =⟨ proj₁ CS.distrib m n 1 ⟩
                         m * n + m * 1
                                        =⟨ cong (_+_ (m * n)) (proj₂ CS.*-identity m) ⟩
                         m * n + m
                                        QED))

nat-lemma₂ : nat ≊ 2*nat ⋎ 2*nat+1
nat-lemma₂ =
  nat
                                        ≊⟨ ≊-η nat ⟩
  ↓ 0 ≺′ nat ⟨ _+_ ⟩ 1 ∞
                                        ≊⟨ ↓ refl ≺ coih ⟩
  ↓ 0 ≺′ (2*nat ⋎ 2*nat+1) ⟨ _+_ ⟩ 1 ∞
                                        ≊⟨ ↓ refl ≺ ♯₁ zip-⋎-const _+_ 2*nat 2*nat+1 1 ⟩
  ↓ 0 ≺′ 2*nat+1 ⋎ 2*nat+1 ⟨ _+_ ⟩ 1 ∞
                                        ≊⟨ ↓ refl ≺ ♯₁ ⋎-cong 2*nat+1 2*nat+1 (2*nat+1 ∎)
                                                              (2*nat+1 ⟨ _+_ ⟩ 1 ∞)
                                                              (2*nat ⟨ _+_ ⟩ 2 ∞) (lemma 2*nat) ⟩
  ↓ 0 ≺′ 2*nat+1 ⋎ 2*nat ⟨ _+_ ⟩ 2 ∞
                                        ≊⟨ nat-lemma₁ ⟩
  2*nat ⋎ 2*nat+1
                                        ∎
  where
  coih ~ ♯₁ ⟨ _+_ ⟩-cong nat (2*nat ⋎ 2*nat+1) nat-lemma₂
                         (1 ∞) (1 ∞) (1 ∞ ∎)

  lemma : ∀ s → (s ⟨ _+_ ⟩ 1 ∞) ⟨ _+_ ⟩ 1 ∞ ≊ s ⟨ _+_ ⟩ 2 ∞
  lemma = pointwise 1 (λ s → (s ⟨ _+_ ⟩ 1 ∞) ⟨ _+_ ⟩ 1 ∞)
                      (λ s → s ⟨ _+_ ⟩ 2 ∞)
                      (λ n → CS.+-assoc n 1 1)

nat≊bin : nat ≊ bin
nat≊bin =
  nat
                                          ≊⟨ nat-lemma₂ ⟩
  2*nat ⋎ 2*nat+1
                                          ≊⟨ ≅-sym nat-lemma₁ ⟩
  ↓ 0 ≺′ 2*nat+1 ⋎ 2*nat ⟨ _+_ ⟩ 2 ∞
                                          ≊⟨ ↓ refl ≺ coih ⟩
  ↓ 0 ≺′ (2 ∞ ⟨ _*_ ⟩ bin) ⟨ _+_ ⟩ 1 ∞ ⋎
         (2 ∞ ⟨ _*_ ⟩ bin) ⟨ _+_ ⟩ 2 ∞
                                          ≊⟨ ≅-sym (≊-η bin) ⟩
  bin
                                          ∎
  where
  coih ~ ♯₁ ⋎-cong 2*nat+1 ((2 ∞ ⟨ _*_ ⟩ bin) ⟨ _+_ ⟩ 1 ∞)
                   (⟨ _+_ ⟩-cong 2*nat (2 ∞ ⟨ _*_ ⟩ bin)
                                 (⟨ _*_ ⟩-cong (2 ∞) (2 ∞) (2 ∞ ∎)
                                               nat bin nat≊bin)
                                 (1 ∞) (1 ∞) (1 ∞ ∎))
                   (2*nat ⟨ _+_ ⟩ 2 ∞)
                   ((2 ∞ ⟨ _*_ ⟩ bin) ⟨ _+_ ⟩ 2 ∞)
                   (⟨ _+_ ⟩-cong 2*nat (2 ∞ ⟨ _*_ ⟩ bin)
                                 (⟨ _*_ ⟩-cong (2 ∞) (2 ∞) (2 ∞ ∎)
                                               nat bin nat≊bin)
                                 (2 ∞) (2 ∞) (2 ∞ ∎))

iterate-fusion
  : ∀ {A B} (h : A → B) (f₁ : A → A) (f₂ : B → B) →
    (∀ x → h (f₁ x) ≡ f₂ (h x)) →
    ∀ x → h · iterate f₁ x ≊ iterate f₂ (h x)
iterate-fusion h f₁ f₂ hyp x =
  h · iterate f₁ x
                                  ≡⟨ refl ⟩
  ↓ h x ≺′ h · iterate f₁ (f₁ x)
                                  ≊⟨ ↓ refl ≺ coih ⟩
  ↓ h x ≺′ iterate f₂ (h (f₁ x))
                                  ≡⟨ cong (λ y → P⇒ (↓ h x ≺′ iterate f₂ y)) (hyp x) ⟩
  ↓ h x ≺′ iterate f₂ (f₂ (h x))
                                  ≡⟨ refl ⟩
  iterate f₂ (h x)
                                  ∎
  where coih ~ ♯₁ iterate-fusion h f₁ f₂ hyp (f₁ x)

nat-iterate : nat ≊ iterate suc 0
nat-iterate =
  nat
                              ≊⟨ ≊-η nat ⟩
  ↓ 0 ≺′ nat ⟨ _+_ ⟩ 1 ∞
                              ≊⟨ ↓ refl ≺ ♯₁ pointwise 1 (λ s → s ⟨ _+_ ⟩ 1 ∞) (_·_ suc)
                                                         (λ x → CS.+-comm x 1) nat ⟩
  ↓ 0 ≺′ suc · nat
                              ≊⟨ ↓ refl ≺ coih ⟩
  ↓ 0 ≺′ suc · iterate suc 0
                              ≊⟨ ↓ refl ≺ ♯₁ iterate-fusion suc suc suc (λ _ → refl) 0 ⟩
  ↓ 0 ≺′ iterate suc 1
                              ≡⟨ refl ⟩
  iterate suc 0
                              ∎
  where coih ~ ♯₁ ·-cong suc nat (iterate suc 0) nat-iterate
