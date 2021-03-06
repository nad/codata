------------------------------------------------------------------------
-- A simplification of Hinze.Section3
------------------------------------------------------------------------

module Hinze.Simplified.Section3 where

open import Stream.Programs
open import Stream.Equality
open import Stream.Pointwise
open import Hinze.Simplified.Section2-4
open import Hinze.Lemmas

open import Codata.Musical.Notation hiding (∞)
open import Data.Product
open import Data.Bool
open import Data.Vec hiding (_⋎_)
open import Data.Nat renaming (suc to 1+)
import Data.Nat.Properties as Nat
import Relation.Binary.PropositionalEquality as P
open import Algebra.Structures
private
  module CS = IsCommutativeSemiring Nat.+-*-isCommutativeSemiring

------------------------------------------------------------------------
-- Abbreviations

2^ : ℕ → ℕ
2^ n = 2 ^ n

2*2^ : ℕ → ℕ
2*2^ n = 2 * 2 ^ n

------------------------------------------------------------------------
-- Definitions

pot : Prog Bool
pot = true ≺ ♯ (pot ⋎ false ∞)

msb : Prog ℕ
msb = 1 ≺ ♯ (2* · msb ⋎ 2* · msb)

ones′ : Prog ℕ
ones′ = 1 ≺ ♯ (ones′ ⋎ 1+ · ones′)

ones : Prog ℕ
ones = 0 ≺♯ ones′

carry : Prog ℕ
carry = 0 ≺ ♯ (1+ · carry ⋎ 0 ∞)

carry-folded : carry ≊ 0 ∞ ⋎ 1+ · carry
carry-folded = carry ∎

turn-length : ℕ → ℕ
turn-length 0      = 0
turn-length (1+ n) = ℓ + 1+ ℓ
  where ℓ = turn-length n

turn : (n : ℕ) → Vec ℕ (turn-length n)
turn 0      = []
turn (1+ n) = turn n ++ [ n ] ++ turn n

tree : ℕ → Prog ℕ
tree n = n ≺ ♯ (turn n ≺≺ tree (1+ n))

frac : Prog ℕ
frac = 0 ≺ ♯ (frac ⋎ 1+ · nat)

frac-folded : frac ≊ nat ⋎ frac
frac-folded = frac ∎

god : Prog ℕ
god = 1+2* · frac

------------------------------------------------------------------------
-- Laws and properties

carry-god-nat : 2^ · carry ⟨ _*_ ⟩ god ≊ tailP nat
carry-god-nat =
  2^ · carry ⟨ _*_ ⟩ god
                                 ≊⟨ ⟨ _*_ ⟩-cong (2^ · carry) (1 ∞ ⋎ 2* · 2^ · carry) lemma
                                                 god (1+2* · nat ⋎ god) (≅-sym (⋎-map 1+2* nat frac)) ⟩
  (1 ∞ ⋎ 2* · 2^ · carry)
         ⟨ _*_ ⟩
    (1+2* · nat ⋎ god)
                                 ≊⟨ ≅-sym (abide-law _*_ (1 ∞) (1+2* · nat) (2* · 2^ · carry) god) ⟩
    1 ∞ ⟨ _*_ ⟩ 1+2* · nat
              ⋎
  2* · 2^ · carry ⟨ _*_ ⟩ god
                                 ≊⟨ ⋎-cong (1 ∞ ⟨ _*_ ⟩ 1+2* · nat) (1+2* · nat)
                                           (pointwise 1 (λ s → 1 ∞ ⟨ _*_ ⟩ s) (λ s → s)
                                                        (λ n → proj₁ CS.*-identity n) (1+2* · nat))
                                           (2* · 2^ · carry ⟨ _*_ ⟩ god) (2* · (2^ · carry ⟨ _*_ ⟩ god))
                                           (pointwise 2 (λ s t → 2* · s ⟨ _*_ ⟩ t)
                                                        (λ s t → 2* · (s ⟨ _*_ ⟩ t))
                                                        (CS.*-assoc 2) (2^ · carry) god) ⟩
           1+2* · nat
               ⋎
  2* · (2^ · carry ⟨ _*_ ⟩ god)
                                 ≊⟨ P.refl ≺ coih ⟩
  1+2* · nat ⋎ 2* · tailP nat
                                 ≊⟨ ≅-sym (tailP-cong nat (2* · nat ⋎ 1+2* · nat) nat-lemma₂) ⟩
  tailP nat
                                 ∎
  where
  coih = ♯ ⋎-cong (2* · (2^ · carry ⟨ _*_ ⟩ god)) (2* · tailP nat)
                  (·-cong 2* (2^ · carry ⟨ _*_ ⟩ god) (tailP nat)
                          carry-god-nat)
                  (tailP (1+2* · nat)) (tailP (1+2* · nat)) (tailP (1+2* · nat) ∎)

  lemma =
    2^ · carry
                                ≡⟨ P.refl ⟩
    2^ · (0 ∞ ⋎ 1+ · carry)
                                ≊⟨ ≅-sym (⋎-map 2^ (0 ∞) (1+ · carry)) ⟩
    2^ · 0 ∞ ⋎ 2^ · 1+ · carry
                                ≊⟨ ⋎-cong (2^ · 0 ∞) (1 ∞)
                                          (pointwise 0 (2^ · 0 ∞) (1 ∞) P.refl)
                                          (2^ · 1+ · carry) (2* · 2^ · carry)
                                          (pointwise 1 (λ s → 2^ · 1+ · s)
                                                       (λ s → 2* · 2^ · s)
                                                       (λ _ → P.refl) carry) ⟩
    (1 ∞ ⋎ 2* · 2^ · carry)
                                ∎
