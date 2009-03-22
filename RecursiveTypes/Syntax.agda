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
open import Relation.Binary.PropositionalEquality as PropEq
open import Relation.Binary.HeterogeneousEquality
import Data.Fin.Props as FP
private
  open module DF {n} = DecSetoid (FP.decSetoid n)
                         using () renaming (_≟_ to _≟F_)

------------------------------------------------------------------------
-- Types

infixr 10 _⟶_
infix  10 ν_⟶_

-- Recursive types, indexed on the maximum number of free variables. I
-- use the character ν rather than μ because the (unfoldings of the)
-- types can be infinite.

-- Note that no attempt is made to ensure that the variable bound in
-- ν_⟶_ is actually used.

data Ty (n : ℕ) : Set where
  ⊥    : Ty n
  ⊤    : Ty n
  var  : (x : Fin n) → Ty n
  _⟶_  : (τ₁ τ₂ : Ty n) → Ty n
  ν_⟶_ : (τ₁ τ₂ : Ty (suc n)) → Ty n

-- Potentially infinite trees.

data Tree (n : ℕ) : Set where
  ⊥    : Tree n
  ⊤    : Tree n
  var  : (x : Fin n) → Tree n
  _⟶_  : (τ₁ τ₂ : ∞ (Tree n)) → Tree n

------------------------------------------------------------------------
-- Syntactic equality of types is decidable

private

  drop-var : ∀ {n x y} → (Ty n ∶ var x) ≡ var y → x ≡ y
  drop-var refl = refl

  drop⟶ˡ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
           (Ty n ∶ σ₁ ⟶ σ₂) ≡ τ₁ ⟶ τ₂ → σ₁ ≡ τ₁
  drop⟶ˡ refl = refl

  drop⟶ʳ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
           (Ty n ∶ σ₁ ⟶ σ₂) ≡ τ₁ ⟶ τ₂ → σ₂ ≡ τ₂
  drop⟶ʳ refl = refl

  dropν⟶ˡ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
            (Ty n ∶ ν σ₁ ⟶ σ₂) ≡ ν τ₁ ⟶ τ₂ → σ₁ ≡ τ₁
  dropν⟶ˡ refl = refl

  dropν⟶ʳ : ∀ {n σ₁ σ₂ τ₁ τ₂} →
            (Ty n ∶ ν σ₁ ⟶ σ₂) ≡ ν τ₁ ⟶ τ₂ → σ₂ ≡ τ₂
  dropν⟶ʳ refl = refl

  indices-equal : ∀ {m n} {σ : Ty m} {τ : Ty n} → σ ≅ τ → m ≡ n
  indices-equal refl = refl

infix 4 _≡?_ _≅?_

_≡?_ : ∀ {n} (σ τ : Ty n) → Dec (σ ≡ τ)
⊥         ≡? ⊥           = yes refl
⊥         ≡? ⊤           = no (λ ())
⊥         ≡? var y       = no (λ ())
⊥         ≡? τ₁ ⟶ τ₂     = no (λ ())
⊥         ≡? ν τ₁ ⟶ τ₂   = no (λ ())
⊤         ≡? ⊥           = no (λ ())
⊤         ≡? ⊤           = yes refl
⊤         ≡? var y       = no (λ ())
⊤         ≡? τ₁ ⟶ τ₂     = no (λ ())
⊤         ≡? ν τ₁ ⟶ τ₂   = no (λ ())
var x     ≡? ⊥           = no (λ ())
var x     ≡? ⊤           = no (λ ())
var x     ≡? var  y      = Dec.map (PropEq.cong var , drop-var) (x ≟F y)
var x     ≡? τ₁ ⟶ τ₂     = no (λ ())
var x     ≡? ν τ₁ ⟶ τ₂   = no (λ ())
σ₁ ⟶ σ₂   ≡? ⊥           = no (λ ())
σ₁ ⟶ σ₂   ≡? ⊤           = no (λ ())
σ₁ ⟶ σ₂   ≡? var y       = no (λ ())
σ₁ ⟶ σ₂   ≡?  τ₁ ⟶  τ₂   with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
σ₁ ⟶ σ₂   ≡? .σ₁ ⟶ .σ₂   | yes refl | yes refl = yes refl
σ₁ ⟶ σ₂   ≡?  τ₁ ⟶  τ₂   | no σ₁≢τ₁ | _        = no (σ₁≢τ₁ ∘ drop⟶ˡ)
σ₁ ⟶ σ₂   ≡?  τ₁ ⟶  τ₂   | _        | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ drop⟶ʳ)
σ₁ ⟶ σ₂   ≡? ν τ₁ ⟶ τ₂   = no (λ ())
ν σ₁ ⟶ σ₂ ≡? ⊥           = no (λ ())
ν σ₁ ⟶ σ₂ ≡? ⊤           = no (λ ())
ν σ₁ ⟶ σ₂ ≡? var y       = no (λ ())
ν σ₁ ⟶ σ₂ ≡? τ₁ ⟶ τ₂     = no (λ ())
ν σ₁ ⟶ σ₂ ≡? ν  τ₁ ⟶  τ₂ with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
ν σ₁ ⟶ σ₂ ≡? ν .σ₁ ⟶ .σ₂ | yes refl | yes refl = yes refl
ν σ₁ ⟶ σ₂ ≡? ν  τ₁ ⟶  τ₂ | no σ₁≢τ₁ | _        = no (σ₁≢τ₁ ∘ dropν⟶ˡ)
ν σ₁ ⟶ σ₂ ≡? ν  τ₁ ⟶  τ₂ | _        | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ dropν⟶ʳ)

_≅?_ : ∀ {m n} (σ : Ty m) (τ : Ty n) → Dec (σ ≅ τ)
_≅?_ {m} { n} σ τ with m ≟ n
_≅?_ {m} {.m} σ τ | yes refl = Dec.map (≡-to-≅ , ≅-to-≡) (σ ≡? τ)
_≅?_ {m} { n} σ τ | no  m≠n  = no (m≠n ∘ indices-equal)
