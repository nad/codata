------------------------------------------------------------------------
-- A solution to a problem posed by Venanzio Capretta
------------------------------------------------------------------------

module VenanziosProblem where

open import Coinduction
open import Data.Nat
open import Data.Stream as Stream using (Stream; _⋎_; evens; odds; _≈_)
open Stream.Stream; open Stream._≈_
open import Relation.Binary

private
  module S {A} = Setoid (Stream.setoid A)

------------------------------------------------------------------------
-- Problem formulation

-- The problem concerns functions satisfying a certain equation:

rhs : {A : Set} → (Stream A → Stream A) → Stream A → Stream A
rhs φ s = s ⋎ φ (evens (φ s))

SatisfiesEquation : {A : Set} → (Stream A → Stream A) → Set
SatisfiesEquation φ = ∀ s → φ s ≈ rhs φ s

-- The statement of the problem:

Statement : Set₁
Statement = {A : Set} {φ₁ φ₂ : Stream A → Stream A} →
            SatisfiesEquation φ₁ → SatisfiesEquation φ₂ →
            ∀ s → φ₁ s ≈ φ₂ s

------------------------------------------------------------------------
-- Solution

module Solution {A : Set} where

  infixr 5 _∷_
  infix  4 _∣_∣_≈P_ _∣_∣_≈W_
  infix  2 _∎
  infixr 2 _≈⟨_⟩_

  -- Let us first define a small language of equality proofs.
  --
  -- m ∣ n ∣ xs ≈P ys means that xs and ys, which are streams
  -- generated in chunks of size 1 + m, where the outer chunk has size
  -- n, are equal.

  mutual

    -- Weak head normal forms of programs.

    data _∣_∣_≈W_ : ℕ → ℕ → Stream A → Stream A → Set where
      reset : ∀ {xs₁ xs₂ m} (xs₁≈xs₂ : ∞ (m ∣ suc m ∣ xs₁ ≈P xs₂)) →
              m ∣ 0 ∣ xs₁ ≈W xs₂
      _∷_   : ∀ x {xs₁ xs₂ m n} (xs₁≈xs₂ : m ∣ n ∣ ♭ xs₁ ≈W ♭ xs₂) →
              m ∣ suc n ∣ x ∷ xs₁ ≈W x ∷ xs₂

    -- Programs.

    data _∣_∣_≈P_ : ℕ → ℕ → Stream A → Stream A → Set where

      -- WHNFs are programs.
      ↑          : ∀ {m n xs₁ xs₂} (xs₁≈xs₂ : m ∣ n ∣ xs₁ ≈W xs₂) →
                   m ∣ n ∣ xs₁ ≈P xs₂

      -- Various congruences.
      _∷_        : ∀ x {xs₁ xs₂ m n} (xs₁≈xs₂ : m ∣ n ∣ ♭ xs₁ ≈P ♭ xs₂) →
                   m ∣ suc n ∣ x ∷ xs₁ ≈P x ∷ xs₂
      _⋎-cong_   : ∀ {xs₁ xs₂ ys₁ ys₂}
                   (xs₁≈xs₂ : 1 ∣ 1 ∣ xs₁ ≈P xs₂)
                   (ys₁≈ys₂ : 0 ∣ 1 ∣ ys₁ ≈P ys₂) →
                   1 ∣ 2 ∣ xs₁ ⋎ ys₁ ≈P xs₂ ⋎ ys₂
      evens-cong : ∀ {xs₁ xs₂}
                   (xs₁≈xs₂ : 1 ∣ 1 ∣ xs₁ ≈P xs₂) →
                   0 ∣ 1 ∣ evens xs₁ ≈P evens xs₂
      odds-cong  : ∀ {xs₁ xs₂}
                   (xs₁≈xs₂ : 1 ∣ 2 ∣ xs₁ ≈P xs₂) →
                   0 ∣ 1 ∣ odds xs₁ ≈P odds xs₂

      -- Equational reasoning.
      _≈⟨_⟩_     : ∀ xs₁ {xs₂ xs₃ m n}
                   (xs₁≈xs₂ : m ∣ n ∣ xs₁ ≈P xs₂)
                   (xs₂≈xs₃ : m ∣ n ∣ xs₂ ≈P xs₃) →
                   m ∣ n ∣ xs₁ ≈P xs₃
      _∎         : ∀ {n m} xs → m ∣ n ∣ xs ≈P xs

      -- If we have already produced 1 + n elements of the last chunk,
      -- then it is safe to pretend that we have only produced n
      -- elements.
      shift      : ∀ {n m xs₁ xs₂} (xs₁≈xs₂ : m ∣ suc n ∣ xs₁ ≈P xs₂) →
                   m ∣ n ∣ xs₁ ≈P xs₂

      -- A variation of the statement we want to prove.
      goal′      : ∀ {φ₁ φ₂ xs₁ xs₂}
                   (s₁ : SatisfiesEquation φ₁)
                   (s₂ : SatisfiesEquation φ₂)
                   (xs₁≈xs₂ : 0 ∣ 1 ∣ xs₁ ≈P xs₂) →
                   1 ∣ 1 ∣ rhs φ₁ xs₁ ≈P rhs φ₂ xs₂

  -- The equality language is complete.

  completeW : ∀ {n m xs ys} → xs ≈ ys → m ∣ n ∣ xs ≈W ys
  completeW {zero}  xs≈ys       = reset (♯ ↑ (completeW xs≈ys))
  completeW {suc n} (x ∷ xs≈ys) = x ∷ completeW (♭ xs≈ys)

  -- If we can prove that the equality language is sound, then the
  -- following lemma implies the intended result.

  goal : ∀ {φ₁ φ₂ xs₁ xs₂}
         (s₁ : SatisfiesEquation φ₁) (s₂ : SatisfiesEquation φ₂) →
         0 ∣ 1 ∣ xs₁ ≈P xs₂ → 1 ∣ 1 ∣ φ₁ xs₁ ≈P φ₂ xs₂
  goal {φ₁} {φ₂} {xs₁} {xs₂} s₁ s₂ xs₁≈xs₂ =
    φ₁ xs₁      ≈⟨ ↑ (completeW (s₁ xs₁)) ⟩
    rhs φ₁ xs₁  ≈⟨ goal′ s₁ s₂ xs₁≈xs₂ ⟩
    rhs φ₂ xs₂  ≈⟨ ↑ (completeW (S.sym (s₂ xs₂))) ⟩
    φ₂ xs₂      ∎

  -- Some lemmas about weak head normal forms.

  evens-congW : {xs₁ xs₂ : Stream A} →
                1 ∣ 1 ∣ xs₁ ≈W xs₂ → 0 ∣ 1 ∣ evens xs₁ ≈W evens xs₂
  evens-congW (x ∷ reset xs₁≈xs₂) =
    x ∷ reset (♯ odds-cong (♭ xs₁≈xs₂))

  reflW : ∀ xs {m} n → m ∣ n ∣ xs ≈W xs
  reflW xs       zero    = reset (♯ (xs ∎))
  reflW (x ∷ xs) (suc n) = x ∷ reflW (♭ xs) n

  transW : ∀ {xs ys zs m n} →
           m ∣ n ∣ xs ≈W ys → m ∣ n ∣ ys ≈W zs → m ∣ n ∣ xs ≈W zs
  transW (x ∷ xs≈ys)   (.x ∷ ys≈zs)  = x ∷ transW xs≈ys ys≈zs
  transW (reset xs≈ys) (reset ys≈zs) =
    reset (♯ (_ ≈⟨ ♭ xs≈ys ⟩ ♭ ys≈zs))

  shiftW : ∀ n {m xs₁ xs₂} →
           m ∣ suc n ∣ xs₁ ≈W xs₂ → m ∣ n ∣ xs₁ ≈W xs₂
  shiftW zero    (x ∷ reset xs₁≈xs₂) = reset (♯ (x ∷ shift (♭ xs₁≈xs₂)))
  shiftW (suc n) (x ∷       xs₁≈xs₂) = x ∷ shiftW n xs₁≈xs₂

  -- Every program can be transformed into WHNF.

  whnf : ∀ {xs ys m n} → m ∣ n ∣ xs ≈P ys → m ∣ n ∣ xs ≈W ys
  whnf (↑ xs≈ys) = xs≈ys

  whnf (x ∷ xs₁≈xs₂) = x ∷ whnf xs₁≈xs₂

  whnf (xs₁≈xs₂ ⋎-cong ys₁≈ys₂) with whnf xs₁≈xs₂ | whnf ys₁≈ys₂
  ... | x ∷ reset xs₁≈xs₂′ | y ∷ reset ys₁≈ys₂′ =
    x ∷ y ∷ reset (♯ (shift (♭ xs₁≈xs₂′) ⋎-cong ♭ ys₁≈ys₂′))

  whnf (evens-cong xs₁≈xs₂) = evens-congW (whnf xs₁≈xs₂)

  whnf (odds-cong xs₁≈xs₂) with whnf xs₁≈xs₂
  ... | x ∷ xs₁≈xs₂′ = evens-congW xs₁≈xs₂′

  whnf (xs₁ ≈⟨ xs₁≈xs₂ ⟩ xs₂≈xs₃) = transW (whnf xs₁≈xs₂) (whnf xs₂≈xs₃)
  whnf (xs ∎)                     = reflW xs _

  whnf (shift xs₁≈xs₂) = shiftW _ (whnf xs₁≈xs₂)

  whnf (goal′ s₁ s₂ xs₁≈xs₂) with whnf xs₁≈xs₂
  ... | (x ∷ reset xs₁≈xs₂′) =
    x ∷ reset (♯ (goal s₁ s₂ (evens-cong (goal s₁ s₂ xs₁≈xs₂))
                    ⋎-cong
                  ♭ xs₁≈xs₂′))

  -- Soundness follows by a corecursive repetition of the whnf
  -- procedure.

  ⟦_⟧W : ∀ {xs ys m n} → m ∣ n ∣ xs ≈W ys → xs ≈ ys
  ⟦ reset ys≈zs ⟧W with whnf (♭ ys≈zs)
  ... | x ∷ ys≈zs′ = x ∷ ♯ ⟦ ys≈zs′ ⟧W
  ⟦ x ∷ ys≈zs   ⟧W = x ∷ ♯ ⟦ ys≈zs ⟧W

  ⟦_⟧P : ∀ {xs ys m n} → m ∣ n ∣ xs ≈P ys → xs ≈ ys
  ⟦ xs≈ys ⟧P = ⟦ whnf xs≈ys ⟧W

-- Wrapping up.

solution : Statement
solution s₁ s₂ s = ⟦ goal s₁ s₂ (s ∎) ⟧P
  where open Solution
