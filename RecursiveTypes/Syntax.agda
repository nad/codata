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

-- Some type constructors are guarding, and some are not. The
-- constructor any means that the type constructor may or may not be
-- guarding.

data Kind : Set where
  guarding : Kind
  any      : Kind

infixr 10 _⟶_

-- Recursive types, parameterised on the maximum number of free
-- variables.
--
-- Note that no attempt is made to ensure that the variable bound in μ
-- is actually used.

data Ty (n : ℕ) : Kind → Set where
  ⊥    : Ty n any
  ⊤    : Ty n any
  var  : (x : Fin n) → Ty n any
  _⟶_  : ∀ {k} (τ₁ τ₂ : Ty n any) → Ty n k
  μ    : (τ : Ty (suc n) guarding) → Ty n any

-- Types without information about the Kind.

TY : ℕ → Set
TY n = Ty n any

-- The Kind information can be "forgotten".

forget : ∀ {k n} → Ty n k → TY n
forget {any}      τ         = τ
forget {guarding} (τ₁ ⟶ τ₂) = τ₁ ⟶ τ₂

-- Potentially infinite trees.

data Tree (n : ℕ) : Set where
  ⊥    : Tree n
  ⊤    : Tree n
  var  : (x : Fin n) → Tree n
  _⟶_  : (τ₁ τ₂ : ∞ (Tree n)) → Tree n

------------------------------------------------------------------------
-- Syntactic equality of types is decidable

private

  drop-var : ∀ {n x y} → (Ty n _ ∶ var x) ≡ var y → x ≡ y
  drop-var refl = refl

  drop⟶ˡ : ∀ {n k σ₁ σ₂ τ₁ τ₂} →
           (Ty n k ∶ σ₁ ⟶ σ₂) ≡ τ₁ ⟶ τ₂ → σ₁ ≡ τ₁
  drop⟶ˡ refl = refl

  drop⟶ʳ : ∀ {n k σ₁ σ₂ τ₁ τ₂} →
           (Ty n k ∶ σ₁ ⟶ σ₂) ≡ τ₁ ⟶ τ₂ → σ₂ ≡ τ₂
  drop⟶ʳ refl = refl

  dropμ : ∀ {n} {σ τ : Ty (suc n) _} → μ σ ≡ μ τ → σ ≡ τ
  dropμ refl = refl

infix 4 _≡?_

_≡?_ : ∀ {n k} (σ τ : Ty n k) → Dec (σ ≡ τ)
⊥       ≡? ⊥         = yes refl
⊥       ≡? ⊤         = no (λ ())
⊥       ≡? var y     = no (λ ())
⊥       ≡? τ₁ ⟶ τ₂   = no (λ ())
⊥       ≡? μ τ       = no (λ ())
⊤       ≡? ⊥         = no (λ ())
⊤       ≡? ⊤         = yes refl
⊤       ≡? var y     = no (λ ())
⊤       ≡? τ₁ ⟶ τ₂   = no (λ ())
⊤       ≡? μ τ       = no (λ ())
var x   ≡? ⊥         = no (λ ())
var x   ≡? ⊤         = no (λ ())
var x   ≡? var  y    = Dec.map (cong var , drop-var) (x ≟F y)
var x   ≡? τ₁ ⟶ τ₂   = no (λ ())
var x   ≡? μ τ       = no (λ ())
σ₁ ⟶ σ₂ ≡? ⊥         = no (λ ())
σ₁ ⟶ σ₂ ≡? ⊤         = no (λ ())
σ₁ ⟶ σ₂ ≡? var y     = no (λ ())
σ₁ ⟶ σ₂ ≡?  τ₁ ⟶  τ₂ with σ₁ ≡? τ₁ | σ₂ ≡? τ₂
σ₁ ⟶ σ₂ ≡? .σ₁ ⟶ .σ₂ | yes refl | yes refl = yes refl
σ₁ ⟶ σ₂ ≡?  τ₁ ⟶  τ₂ | no σ₁≢τ₁ | _        = no (σ₁≢τ₁ ∘ drop⟶ˡ)
σ₁ ⟶ σ₂ ≡?  τ₁ ⟶  τ₂ | _        | no σ₂≢τ₂ = no (σ₂≢τ₂ ∘ drop⟶ʳ)
σ₁ ⟶ σ₂ ≡? μ τ       = no (λ ())
μ σ     ≡? ⊥         = no (λ ())
μ σ     ≡? ⊤         = no (λ ())
μ σ     ≡? var y     = no (λ ())
μ σ     ≡? τ₁ ⟶ τ₂   = no (λ ())
μ σ     ≡? μ  τ      with σ ≡? τ
μ σ     ≡? μ .σ      | yes refl = yes refl
μ σ     ≡? μ  τ      | no  σ≢τ  = no (σ≢τ ∘ dropμ)

------------------------------------------------------------------------
-- Hypotheses

-- A hypothesis is a pair of types where the first is assumed to be a
-- subtype of the other.

open Data.Product public using () renaming (_,_ to _≲_)

Hyp : ℕ → Set
Hyp n = TY n × TY n
