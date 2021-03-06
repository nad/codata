------------------------------------------------------------------------
-- A formalisation of some definitions and laws from Section 3 of Ralf
-- Hinze's paper "Streams and Unique Fixed Points"
------------------------------------------------------------------------

module Hinze.Section3 where

open import Stream.Programs
open import Stream.Equality
open import Stream.Pointwise
open import Hinze.Section2-4
open import Hinze.Lemmas

open import Codata.Musical.Notation hiding (∞)
open import Data.Product
open import Data.Bool
open import Data.Vec hiding (_⋎_)
open import Data.Nat
import Data.Nat.Properties as Nat
import Relation.Binary.PropositionalEquality as P
open import Algebra.Structures
private
  module CS = IsCommutativeSemiring Nat.+-*-isCommutativeSemiring

------------------------------------------------------------------------
-- Definitions

pot : Prog Bool
pot = true ≺ ♯ (pot ⋎ false ∞)

msb : Prog ℕ
msb = 1 ≺ ♯ (2 ∞ ⟨ _*_ ⟩ msb ⋎ 2 ∞ ⟨ _*_ ⟩ msb)

ones′ : Prog ℕ
ones′ = 1 ≺ ♯ (ones′ ⋎ ones′ ⟨ _+_ ⟩ 1 ∞)

ones : Prog ℕ
ones = 0 ≺♯ ones′

carry : Prog ℕ
carry = 0 ≺ ♯ (carry ⟨ _+_ ⟩ 1 ∞ ⋎ 0 ∞)

carry-folded : carry ≊ 0 ∞ ⋎ carry ⟨ _+_ ⟩ 1 ∞
carry-folded = carry ∎

2^carry : Prog ℕ
2^carry = 2 ∞ ⟨ _^_ ⟩ carry

turn-length : ℕ → ℕ
turn-length zero    = zero
turn-length (suc n) = ℓ + suc ℓ
  where ℓ = turn-length n

turn : (n : ℕ) → Vec ℕ (turn-length n)
turn zero    = []
turn (suc n) = turn n ++ [ n ] ++ turn n

tree : ℕ → Prog ℕ
tree n = n ≺ ♯ (turn n ≺≺ tree (suc n))

frac : Prog ℕ
frac = 0 ≺ ♯ (frac ⋎ nat ⟨ _+_ ⟩ 1 ∞)

frac-folded : frac ≊ nat ⋎ frac
frac-folded = frac ∎

god : Prog ℕ
god = (2 ∞ ⟨ _*_ ⟩ frac) ⟨ _+_ ⟩ 1 ∞

------------------------------------------------------------------------
-- Laws and properties

god-lemma : god ≊ 2*nat+1 ⋎ god
god-lemma =
  god
                                          ≡⟨ P.refl ⟩
  (2 ∞ ⟨ _*_ ⟩ (nat ⋎ frac)) ⟨ _+_ ⟩ 1 ∞
                                          ≊⟨ ⟨ _+_ ⟩-cong (2 ∞ ⟨ _*_ ⟩ (nat ⋎ frac))
                                                          (2*nat ⋎ 2 ∞ ⟨ _*_ ⟩ frac)
                                                          (zip-const-⋎ _*_ 2 nat frac)
                                                          (1 ∞) (1 ∞) (1 ∞ ∎)  ⟩
  (2*nat ⋎ 2 ∞ ⟨ _*_ ⟩ frac) ⟨ _+_ ⟩ 1 ∞
                                          ≊⟨ zip-⋎-const _+_ 2*nat (2 ∞ ⟨ _*_ ⟩ frac) 1 ⟩
  2*nat+1 ⋎ god
                                          ∎

carry-god-nat : 2^carry ⟨ _*_ ⟩ god ≊ tailP nat
carry-god-nat =
  2^carry ⟨ _*_ ⟩ god
                                                           ≡⟨ P.refl ⟩
  (2 ∞ ⟨ _^_ ⟩ (0 ∞ ⋎ carry ⟨ _+_ ⟩ 1 ∞)) ⟨ _*_ ⟩ god
                                                           ≊⟨ ⟨ _*_ ⟩-cong (2 ∞ ⟨ _^_ ⟩ (0 ∞ ⋎ carry ⟨ _+_ ⟩ 1 ∞))
                                                                           (1 ∞ ⋎ 2 ∞ ⟨ _*_ ⟩ 2^carry) lemma
                                                                           god (2*nat+1 ⋎ god) god-lemma ⟩
  (1 ∞ ⋎ 2 ∞ ⟨ _*_ ⟩ 2^carry) ⟨ _*_ ⟩ (2*nat+1 ⋎ god)
                                                           ≊⟨ ≅-sym (abide-law _*_ (1 ∞) 2*nat+1
                                                                                   (2 ∞ ⟨ _*_ ⟩ 2^carry) god) ⟩
  1 ∞ ⟨ _*_ ⟩ 2*nat+1 ⋎ (2 ∞ ⟨ _*_ ⟩ 2^carry) ⟨ _*_ ⟩ god
                                                           ≊⟨ ⋎-cong (1 ∞ ⟨ _*_ ⟩ 2*nat+1) 2*nat+1
                                                                     (pointwise 1 (λ s → 1 ∞ ⟨ _*_ ⟩ s) (λ s → s)
                                                                                  (proj₁ CS.*-identity) 2*nat+1)
                                                                     ((2 ∞ ⟨ _*_ ⟩ 2^carry) ⟨ _*_ ⟩ god)
                                                                     (2 ∞ ⟨ _*_ ⟩ (2^carry ⟨ _*_ ⟩ god))
                                                                     (pointwise 3 (λ s t u → (s ⟨ _*_ ⟩ t) ⟨ _*_ ⟩ u)
                                                                                  (λ s t u → s ⟨ _*_ ⟩ (t ⟨ _*_ ⟩ u))
                                                                                  CS.*-assoc (2 ∞) 2^carry god) ⟩
  2*nat+1 ⋎ 2 ∞ ⟨ _*_ ⟩ (2^carry ⟨ _*_ ⟩ god)
                                                           ≊⟨ P.refl ≺ coih ⟩
  2*nat+1 ⋎ 2 ∞ ⟨ _*_ ⟩ tailP nat
                                                           ≊⟨ ≅-sym (tailP-cong nat (2*nat ⋎ 2*nat+1) nat-lemma₂) ⟩
  tailP nat
                                                           ∎
  where
  coih = ♯ ⋎-cong (2 ∞ ⟨ _*_ ⟩ (2^carry ⟨ _*_ ⟩ god))
                  (2 ∞ ⟨ _*_ ⟩ (tailP nat))
                  (⟨ _*_ ⟩-cong (2 ∞) (2 ∞) (2 ∞ ∎)
                                (2^carry ⟨ _*_ ⟩ god) (tailP nat)
                                carry-god-nat)
                  (tailP 2*nat+1) (tailP 2*nat+1) (tailP 2*nat+1 ∎)

  lemma =
    2^carry
                                                       ≡⟨ P.refl ⟩
    2 ∞ ⟨ _^_ ⟩ (0 ∞ ⋎ carry ⟨ _+_ ⟩ 1 ∞)
                                                       ≊⟨ zip-const-⋎ _^_ 2 (0 ∞) (carry ⟨ _+_ ⟩ 1 ∞) ⟩
    2 ∞ ⟨ _^_ ⟩ 0 ∞ ⋎ 2 ∞ ⟨ _^_ ⟩ (carry ⟨ _+_ ⟩ 1 ∞)
                                                       ≊⟨ ⋎-cong (2 ∞ ⟨ _^_ ⟩ 0 ∞) (1 ∞)
                                                                 (pointwise 0 (2 ∞ ⟨ _^_ ⟩ 0 ∞) (1 ∞) P.refl)
                                                                 (2 ∞ ⟨ _^_ ⟩ (carry ⟨ _+_ ⟩ 1 ∞))
                                                                 (2 ∞ ⟨ _*_ ⟩ 2^carry)
                                                                 (pointwise 1 (λ s → 2 ∞ ⟨ _^_ ⟩ (s ⟨ _+_ ⟩ 1 ∞))
                                                                              (λ s → 2 ∞ ⟨ _*_ ⟩ (2 ∞ ⟨ _^_ ⟩ s))
                                                                              (λ x → P.cong (_^_ 2) (CS.+-comm x 1))
                                                                              carry) ⟩
    1 ∞ ⋎ 2 ∞ ⟨ _*_ ⟩ 2^carry
                                                       ∎
