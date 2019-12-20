------------------------------------------------------------------------
-- Possibly infinite binary trees
------------------------------------------------------------------------

module Tree where

open import Codata.Musical.Notation
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_)

data Tree (A : Set) : Set where
  leaf : Tree A
  node : (l : ∞ (Tree A)) (x : A) (r : ∞ (Tree A)) → Tree A

map : ∀ {A B} → (A → B) → Tree A → Tree B
map f leaf         = leaf
map f (node l x r) = node (♯ map f (♭ l)) (f x) (♯ map f (♭ r))

data _≈_ {A : Set} : (t₁ t₂ : Tree A) → Set where
  leaf : leaf ≈ leaf
  node : ∀ {l₁ l₂ x₁ x₂ r₁ r₂}
         (l≈ : ∞ (♭ l₁ ≈ ♭ l₂)) (x≡ : x₁ ≡ x₂) (r≈ : ∞ (♭ r₁ ≈ ♭ r₂)) →
         node l₁ x₁ r₁ ≈ node l₂ x₂ r₂

refl : ∀ {A} (t : Tree A) → t ≈ t
refl leaf         = leaf
refl (node l x r) = node (♯ refl (♭ l)) PropEq.refl (♯ refl (♭ r))

trans : ∀ {A} {t₁ t₂ t₃ : Tree A} →
        t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
trans leaf            leaf               = leaf
trans (node l≈ x≡ r≈) (node l≈′ x≡′ r≈′) =
  node (♯ trans (♭ l≈) (♭ l≈′)) (PropEq.trans x≡ x≡′)
       (♯ trans (♭ r≈) (♭ r≈′))

map-cong : ∀ {A B} (f : A → B) {t₁ t₂ : Tree A} →
           t₁ ≈ t₂ → map f t₁ ≈ map f t₂
map-cong f leaf            = leaf
map-cong f (node l≈ x≡ r≈) =
  node (♯ map-cong f (♭ l≈)) (PropEq.cong f x≡) (♯ map-cong f (♭ r≈))
