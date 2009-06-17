------------------------------------------------------------------------
-- Recursive types and potentially infinite trees
------------------------------------------------------------------------

module RecursiveTypes.Syntax where

open import Data.Nat
open import Data.Fin
open import Data.Function
open import Data.Product
open import Coinduction
open import Relation.Nullary
import Relation.Nullary.Decidable as Dec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
import Data.Fin.Props as FP
private
  open module DF {n} = DecSetoid (FP.decSetoid n)
                         using () renaming (_≟_ to _≟F_)

------------------------------------------------------------------------
-- Types

data Guarded : Set where
  guarded   : Guarded
  unguarded : Guarded

infixr 10 _⟶_

-- Recursive types, indexed on the maximum number of free variables.

-- Note that no attempt is made to ensure that the variable bound in μ
-- is actually used.

data Ty (n : ℕ) : Guarded → Set where
  ⊥    : ∀ {g} → Ty n g
  ⊤    : ∀ {g} → Ty n g
  var  : (x : Fin n) → Ty n guarded
  _⟶_  : ∀ {g₁ g₂ g} (τ₁ : Ty n g₁) (τ₂ : Ty n g₂) → Ty n g
  μ    : ∀ {g} (τ : Ty (suc n) unguarded) → Ty n g

forget : ∀ {n g} → Ty n g → Ty n guarded
forget ⊥         = ⊥
forget ⊤         = ⊤
forget (var x)   = var x
forget (τ₁ ⟶ τ₂) = τ₁ ⟶ τ₂
forget (μ τ)     = μ τ

-- Potentially infinite trees.

data Tree (n : ℕ) : Set where
  ⊥    : Tree n
  ⊤    : Tree n
  var  : (x : Fin n) → Tree n
  _⟶_  : (τ₁ τ₂ : ∞ (Tree n)) → Tree n

------------------------------------------------------------------------
-- Syntactic equality of types is decidable

-- private

--   drop-var : ∀ {n x y} → (Ty n ∶ var x) ≡ var y → x ≡ y
--   drop-var refl = refl

--   drop⟶ˡ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
--            (Ty n ∶ σ₁ ⟶ σ₂) ≡ τ₁ ⟶ τ₂ → σ₁ ≡ τ₁
--   drop⟶ˡ refl = refl

--   drop⟶ʳ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
--            (Ty n ∶ σ₁ ⟶ σ₂) ≡ τ₁ ⟶ τ₂ → σ₂ ≡ τ₂
--   drop⟶ʳ refl = refl

--   dropμ⟶ˡ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
--             (Ty n ∶ μ σ₁ ⟶ σ₂) ≡ μ τ₁ ⟶ τ₂ → σ₁ ≡ τ₁
--   dropμ⟶ˡ refl = refl

--   dropμ⟶ʳ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
--             (Ty n ∶ μ σ₁ ⟶ σ₂) ≡ μ τ₁ ⟶ τ₂ → σ₂ ≡ τ₂
--   dropμ⟶ʳ refl = refl

-- infix 4 _≡?_

-- _≡?_ : ∀ {n} (σ τ : Ty n) → Dec (σ ≡ τ)
-- ⊥         ≡? ⊥           = yes refl
-- ⊥         ≡? ⊤           = no (λ ())
-- ⊥         ≡? var y       = no (λ ())
-- ⊥         ≡? τ₁ ⟶ τ₂     = no (λ ())
-- ⊥         ≡? μ τ₁ ⟶ τ₂   = no (λ ())
-- ⊤         ≡? ⊥           = no (λ ())
-- ⊤         ≡? ⊤           = yes refl
-- ⊤         ≡? var y       = no (λ ())
-- ⊤         ≡? τ₁ ⟶ τ₂     = no (λ ())
-- ⊤         ≡? μ τ₁ ⟶ τ₂   = no (λ ())
-- var x     ≡? ⊥           = no (λ ())
-- var x     ≡? ⊤           = no (λ ())
-- var x     ≡? var  y      = Dec.map (cong var , drop-var) (x ≟F y)
-- var x     ≡? τ₁ ⟶ τ₂     = no (λ ())
-- var x     ≡? μ τ₁ ⟶ τ₂   = no (λ ())
-- σ₁ ⟶ σ₂   ≡? ⊥           = no (λ ())
-- σ₁ ⟶ σ₂   ≡? ⊤           = no (λ ())
-- σ₁ ⟶ σ₂   ≡? var y       = no (λ ())
-- σ₁ ⟶ σ₂   ≡?  τ₁ ⟶  τ₂   with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
-- σ₁ ⟶ σ₂   ≡? .σ₁ ⟶ .σ₂   | yes refl | yes refl = yes refl
-- σ₁ ⟶ σ₂   ≡?  τ₁ ⟶  τ₂   | no σ₁≢τ₁ | _        = no (σ₁≢τ₁ ∘ drop⟶ˡ)
-- σ₁ ⟶ σ₂   ≡?  τ₁ ⟶  τ₂   | _        | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ drop⟶ʳ)
-- σ₁ ⟶ σ₂   ≡? μ τ₁ ⟶ τ₂   = no (λ ())
-- μ σ₁ ⟶ σ₂ ≡? ⊥           = no (λ ())
-- μ σ₁ ⟶ σ₂ ≡? ⊤           = no (λ ())
-- μ σ₁ ⟶ σ₂ ≡? var y       = no (λ ())
-- μ σ₁ ⟶ σ₂ ≡? τ₁ ⟶ τ₂     = no (λ ())
-- μ σ₁ ⟶ σ₂ ≡? μ  τ₁ ⟶  τ₂ with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
-- μ σ₁ ⟶ σ₂ ≡? μ .σ₁ ⟶ .σ₂ | yes refl | yes refl = yes refl
-- μ σ₁ ⟶ σ₂ ≡? μ  τ₁ ⟶  τ₂ | no σ₁≢τ₁ | _        = no (σ₁≢τ₁ ∘ dropμ⟶ˡ)
-- μ σ₁ ⟶ σ₂ ≡? μ  τ₁ ⟶  τ₂ | _        | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ dropμ⟶ʳ)

------------------------------------------------------------------------
-- Hypotheses

-- A hypothesis is a pair of types where the first is assumed to be a
-- subtype of the other.

open Data.Product public using () renaming (_,_ to _≲_)

-- Hyp : ℕ → Set
-- Hyp n = Ty n × Ty n
