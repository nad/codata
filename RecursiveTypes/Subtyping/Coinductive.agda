------------------------------------------------------------------------
-- Coinductive definition of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Coinductive where

open import Data.Fin
open import Coinduction

open import RecursiveTypes.Syntax
open import RecursiveTypes.Semantics

infixr 10 _⟶_
infix  4  _≤∞_ _≤Coind_
infixr 2  _≤⟨_⟩_
infix  2  _∎

------------------------------------------------------------------------
-- Definition

-- The obvious definition of subtyping for trees.

data _≤∞_ : ∀ {m n} → Tree m → Tree n → Set where
  ⊥   : ∀ {m n} {τ : Tree n} → ⊥ {m} ≤∞ τ
  ⊤   : ∀ {m n} {σ : Tree m} → σ ≤∞ ⊤ {n}
  var : ∀ {n} {x : Fin n} → var x ≤∞ var x
  _⟶_ : ∀ {m n} {σ₁ σ₂ : ∞ (Tree m)} {τ₁ τ₂ : ∞ (Tree n)}
        (τ₁≤σ₁ : ∞ (♭ τ₁ ≤∞ ♭ σ₁)) (σ₂≤τ₂ : ∞ (♭ σ₂ ≤∞ ♭ τ₂)) →
        σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂

-- Subtyping for recursive types is defined in terms of subtyping for
-- trees.

_≤Coind_ : ∀ {m n} → Ty m → Ty n → Set
σ ≤Coind τ = ⟦ σ ⟧ ≤∞ ⟦ τ ⟧

------------------------------------------------------------------------
-- A trick used to ensure guardedness of expressions using
-- transitivity

infix 4 _≤∞Prog_ _≤∞WHNF_

data _≤∞Prog_ : ∀ {m n} → Tree m → Tree n → Set where
  ⊥      : ∀ {m n} {τ : Tree n} → ⊥ {m} ≤∞Prog τ
  ⊤      : ∀ {m n} {σ : Tree m} → σ ≤∞Prog ⊤ {n}
  var    : ∀ {n} {x : Fin n} → var x ≤∞Prog var x
  _⟶_    : ∀ {m n} {σ₁ σ₂ : ∞ (Tree m)} {τ₁ τ₂ : ∞ (Tree n)}
           (τ₁≤σ₁ : ∞ (♭ τ₁ ≤∞Prog ♭ σ₁)) (σ₂≤τ₂ : ∞ (♭ σ₂ ≤∞Prog ♭ τ₂)) →
           σ₁ ⟶ σ₂ ≤∞Prog τ₁ ⟶ τ₂
  -- Reflexivity.
  _∎     : ∀ {n} (τ : Tree n) → τ ≤∞Prog τ
  -- Transitivity.
  _≤⟨_⟩_ : ∀ {m n k} (τ₁ : Tree m) {τ₂ : Tree n} {τ₃ : Tree k}
           (τ₁≤τ₂ : τ₁ ≤∞Prog τ₂) (τ₂≤τ₃ : τ₂ ≤∞Prog τ₃) → τ₁ ≤∞Prog τ₃

data _≤∞WHNF_ : ∀ {m n} → Tree m → Tree n → Set where
  ⊥   : ∀ {m n} {τ : Tree n} → ⊥ {m} ≤∞WHNF τ
  ⊤   : ∀ {m n} {σ : Tree m} → σ ≤∞WHNF ⊤ {n}
  var : ∀ {n} {x : Fin n} → var x ≤∞WHNF var x
  _⟶_ : ∀ {m n} {σ₁ σ₂ : ∞ (Tree m)} {τ₁ τ₂ : ∞ (Tree n)}
        (τ₁≤σ₁ : ♭ τ₁ ≤∞Prog ♭ σ₁) (σ₂≤τ₂ : ♭ σ₂ ≤∞Prog ♭ τ₂) →
        σ₁ ⟶ σ₂ ≤∞WHNF τ₁ ⟶ τ₂

whnf : ∀ {m n} {σ : Tree m} {τ : Tree n} → σ ≤∞Prog τ → σ ≤∞WHNF τ
whnf ⊥                    = ⊥
whnf ⊤                    = ⊤
whnf var                  = var
whnf (τ₁≤σ₁ ⟶ σ₂≤τ₂)      = ♭ τ₁≤σ₁ ⟶ ♭ σ₂≤τ₂
whnf (⊥ ∎)                = ⊥
whnf (⊤ ∎)                = ⊤
whnf (var x ∎)            = var
whnf (σ ⟶ τ ∎)            = (♭ σ ∎) ⟶ (♭ τ ∎)
whnf (σ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) with whnf τ₁≤τ₂ | whnf τ₂≤τ₃
whnf (._ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) | ⊥             | _             = ⊥
whnf (_  ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) | _             | ⊤             = ⊤
whnf (._ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) | var           | var           = var
whnf (._ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) | τ₁≤σ₁ ⟶ σ₂≤τ₂ | τ₂≤σ₂ ⟶ σ₃≤τ₃ =
  (_ ≤⟨ τ₂≤σ₂ ⟩ τ₁≤σ₁) ⟶ (_ ≤⟨ σ₂≤τ₂ ⟩ σ₃≤τ₃)

mutual

  value : ∀ {m n} {σ : Tree m} {τ : Tree n} → σ ≤∞WHNF τ → σ ≤∞ τ
  value ⊥               = ⊥
  value ⊤               = ⊤
  value var             = var
  value (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♯ ⟦ τ₁≤σ₁ ⟧≤∞ ⟶ ♯ ⟦ σ₂≤τ₂ ⟧≤∞

  ⟦_⟧≤∞ : ∀ {m n} {σ : Tree m} {τ : Tree n} → σ ≤∞Prog τ → σ ≤∞ τ
  ⟦ σ≤τ ⟧≤∞ = value (whnf σ≤τ)
