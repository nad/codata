------------------------------------------------------------------------
-- A simplification of Hinze.Section2-4
------------------------------------------------------------------------

module Hinze.Simplified.Section2-4 where

open import Stream.Programs
open import Stream.Equality
open import Stream.Pointwise
open import Hinze.Lemmas

open import Coinduction hiding (∞)
open import Data.Nat renaming (suc to 1+)
open import Data.Function using (_∘_)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (_≡⟨_⟩_ to _=⟨_⟩_; _∎ to _QED)
open import Algebra.Structures
import Data.Nat.Properties as Nat
private
  module CS = IsCommutativeSemiring _ Nat.isCommutativeSemiring
open import Data.Product

------------------------------------------------------------------------
-- Abbreviations

2* : ℕ → ℕ
2* n = 2 * n

1+2* : ℕ → ℕ
1+2* n = 1 + 2 * n

2+2* : ℕ → ℕ
2+2* n = 2 + 2 * n

------------------------------------------------------------------------
-- Definitions

nat : StreamProg ℕ
nat = ↓ 0 ≺ nat′
  where nat′ ~ ♯₁ (1+ · nat)

fac : StreamProg ℕ
fac = ↓ 1 ≺ fac′
  where fac′ ~ ♯₁ (1+ · nat ⟨ _*_ ⟩ fac)

fib : StreamProg ℕ
fib = ↓ 0 ≺ fib′
  where fib′ ~ ♯₁ (fib ⟨ _+_ ⟩ (↓ 1 ≺ ♯₁ fib))

bin : StreamProg ℕ
bin = ↓ 0 ≺ bin′
  where bin′ ~ ♯₁ (1+2* · bin ⋎ 2+2* · bin)

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

nat-lemma₁ : ↓ 0 ≺′ 1+2* · nat ⋎ 2+2* · nat ≊ 2* · nat ⋎ 1+2* · nat
nat-lemma₁ =
  ↓ 0 ≺′ 1+2* · nat ⋎ 2+2* · nat
                                     ≊⟨ ↓ refl ≺ ♯₁ ⋎-cong
                                          (1+2* · nat) (1+2* · nat) (1+2* · nat ∎)
                                          (2+2* · nat) (2* · 1+ · nat) (lemma 2 nat) ⟩
  ↓ 0 ≺′ 1+2* · nat ⋎ 2* · 1+ · nat
                                     ≡⟨ refl ⟩
  2* · nat ⋎ 1+2* · nat
                                     ∎
  where
  lemma : ∀ m s → (λ n → m + m * n) · s ≊ _*_ m · 1+ · s
  lemma m = pointwise 1 (λ s → (λ n → m + m * n) · s)
                        (λ s → _*_ m · 1+ · s)
                        (λ n → sym (begin
                           m * (1 + n)
                                          =⟨ proj₁ CS.distrib m 1 n ⟩
                           m * 1 + m * n
                                          =⟨ cong (λ x → x + m * n)
                                                  (proj₂ CS.*-identity m) ⟩
                           m + m * n
                                          QED))

nat-lemma₂ : nat ≊ 2* · nat ⋎ 1+2* · nat
nat-lemma₂ =
  nat
                                          ≊⟨ ≊-η nat ⟩
  ↓ 0 ≺′ 1+ · nat
                                          ≊⟨ ↓ refl ≺ coih ⟩
  ↓ 0 ≺′ 1+ · (2* · nat ⋎ 1+2* · nat)
                                          ≊⟨ ≅-sym (↓ refl ≺ ♯₁ ⋎-map 1+ (2* · nat) (1+2* · nat)) ⟩
  ↓ 0 ≺′ 1+ · 2* · nat ⋎ 1+ · 1+2* · nat
                                          ≊⟨ ↓ refl ≺ ♯₁ ⋎-cong (1+ ·   2* · nat) (1+2* · nat)
                                                                (map-fusion 1+   2* nat)
                                                                (1+ · 1+2* · nat) (2+2* · nat)
                                                                (map-fusion 1+ 1+2* nat) ⟩
  ↓ 0 ≺′ 1+2* · nat ⋎ 2+2* · nat
                                          ≊⟨ nat-lemma₁ ⟩
  2* · nat ⋎ 1+2* · nat
                                          ∎
  where coih ~ ♯₁ ·-cong 1+ nat (2* · nat ⋎ 1+2* · nat) nat-lemma₂

nat≊bin : nat ≊ bin
nat≊bin =
  nat
                                  ≊⟨ nat-lemma₂ ⟩
  2* · nat ⋎ 1+2* · nat
                                  ≊⟨ ≅-sym nat-lemma₁ ⟩
  ↓ 0 ≺′ 1+2* · nat ⋎ 2+2* · nat
                                  ≊⟨ ↓ refl ≺ coih ⟩
  ↓ 0 ≺′ 1+2* · bin ⋎ 2+2* · bin
                                  ≊⟨ ≅-sym (≊-η bin) ⟩
  bin
                                  ∎
  where
  coih ~ ♯₁ ⋎-cong (1+2* · nat) (1+2* · bin)
                   (·-cong 1+2* nat bin nat≊bin)
                   (2+2* · nat) (2+2* · bin)
                   (·-cong 2+2* nat bin nat≊bin)

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

nat-iterate : nat ≊ iterate 1+ 0
nat-iterate =
  nat
                            ≊⟨ ≊-η nat ⟩
  ↓ 0 ≺′ 1+ · nat
                            ≊⟨ ↓ refl ≺ coih ⟩
  ↓ 0 ≺′ 1+ · iterate 1+ 0
                            ≊⟨ ↓ refl ≺ ♯₁ iterate-fusion 1+ 1+ 1+ (λ _ → refl) 0 ⟩
  ↓ 0 ≺′ iterate 1+ 1
                            ≡⟨ refl ⟩
  iterate 1+ 0
                            ∎
  where coih ~ ♯₁ ·-cong 1+ nat (iterate 1+ 0) nat-iterate