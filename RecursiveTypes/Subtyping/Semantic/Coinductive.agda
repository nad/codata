------------------------------------------------------------------------
-- Coinductive definition of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Semantic.Coinductive where

open import Coinduction
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Data.Function
open import Data.Empty using (⊥-elim)
open import Relation.Nullary
open import Relation.Binary.HeterogeneousEquality using (_≅_; refl)

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
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
whnf (._ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) | τ₁≤σ₁ ⟶ σ₂≤τ₂ | χ₁≤τ₁ ⟶ τ₂≤χ₂ =
  (_ ≤⟨ χ₁≤τ₁ ⟩ τ₁≤σ₁) ⟶ (_ ≤⟨ σ₂≤τ₂ ⟩ τ₂≤χ₂)

mutual

  value : ∀ {m n} {σ : Tree m} {τ : Tree n} → σ ≤∞WHNF τ → σ ≤∞ τ
  value ⊥               = ⊥
  value ⊤               = ⊤
  value var             = var
  value (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♯ ⟦ τ₁≤σ₁ ⟧≤∞ ⟶ ♯ ⟦ σ₂≤τ₂ ⟧≤∞

  ⟦_⟧≤∞ : ∀ {m n} {σ : Tree m} {τ : Tree n} → σ ≤∞Prog τ → σ ≤∞ τ
  ⟦ σ≤τ ⟧≤∞ = value (whnf σ≤τ)

prog : ∀ {m n} {σ : Tree m} {τ : Tree n} → σ ≤∞ τ → σ ≤∞Prog τ
prog ⊥               = ⊥
prog ⊤               = ⊤
prog var             = var
prog (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♯ prog (♭ τ₁≤σ₁) ⟶ ♯ prog (♭ σ₂≤τ₂)

------------------------------------------------------------------------
-- Some lemmas

trans : ∀ {m n k} {τ₁ : Tree m} {τ₂ : Tree n} {τ₃ : Tree k} →
        τ₁ ≤∞ τ₂ → τ₂ ≤∞ τ₃ → τ₁ ≤∞ τ₃
trans {τ₁ = τ₁} {τ₂} {τ₃} τ₁≤τ₂ τ₂≤τ₃ =
  ⟦ τ₁ ≤⟨ prog τ₁≤τ₂ ⟩
    τ₂ ≤⟨ prog τ₂≤τ₃ ⟩
    τ₃ ∎ ⟧≤∞

unfold : ∀ {n} {τ₁ τ₂ : Ty (suc n)} →
         let τ = ν τ₁ ⟶ τ₂ in τ ≤Coind τ₁ ⟶ τ₂ [0≔ τ ]
unfold = ♯ ⟦ _ ∎ ⟧≤∞ ⟶ ♯ ⟦ _ ∎ ⟧≤∞

fold : ∀ {n} {τ₁ τ₂ : Ty (suc n)} →
       let τ = ν τ₁ ⟶ τ₂ in τ₁ ⟶ τ₂ [0≔ τ ] ≤Coind τ
fold = ♯ ⟦ _ ∎ ⟧≤∞ ⟶ ♯ ⟦ _ ∎ ⟧≤∞

var:≤∞⟶≅ : ∀ {m} {n} {x : Fin m} {y : Fin n} →
           var x ≤∞ var y → var x ≅ var y
var:≤∞⟶≅ var = refl

left-proj : ∀ {m n} {σ₁ σ₂ : ∞ (Tree m)} {τ₁ τ₂ : ∞ (Tree n)} →
            σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂ → ♭ τ₁ ≤∞ ♭ σ₁
left-proj (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♭ τ₁≤σ₁

right-proj : ∀ {m n} {σ₁ σ₂ : ∞ (Tree m)} {τ₁ τ₂ : ∞ (Tree n)} →
             σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂ → ♭ σ₂ ≤∞ ♭ τ₂
right-proj (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♭ σ₂≤τ₂

------------------------------------------------------------------------
-- Double-negation does not affect _≤∞_

drop-¬¬ : ∀ {m n} (σ : Tree m) (τ : Tree n) → ¬ ¬ σ ≤∞ τ → σ ≤∞ τ
drop-¬¬ ⊥         τ         ¬≰ = ⊥
drop-¬¬ σ         ⊤         ¬≰ = ⊤
drop-¬¬ (var x)   (var  y)  ¬≰ with var x ≅? var y
drop-¬¬ (var x)   (var .x)  ¬≰ | yes refl = var
drop-¬¬ (var x)   (var  y)  ¬≰ | no  x≠y  = ⊥-elim (¬≰ (x≠y ∘ var:≤∞⟶≅))
drop-¬¬ (σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) ¬≰ =
  ♯ drop-¬¬ (♭ τ₁) (♭ σ₁) (λ ≰ → ¬≰ (≰ ∘  left-proj)) ⟶
  ♯ drop-¬¬ (♭ σ₂) (♭ τ₂) (λ ≰ → ¬≰ (≰ ∘ right-proj))
drop-¬¬ ⊤         ⊥         ¬≰ = ⊥-elim (¬≰ (λ ()))
drop-¬¬ ⊤         (var x)   ¬≰ = ⊥-elim (¬≰ (λ ()))
drop-¬¬ ⊤         (τ₁ ⟶ τ₂) ¬≰ = ⊥-elim (¬≰ (λ ()))
drop-¬¬ (var x)   ⊥         ¬≰ = ⊥-elim (¬≰ (λ ()))
drop-¬¬ (var x)   (τ₁ ⟶ τ₂) ¬≰ = ⊥-elim (¬≰ (λ ()))
drop-¬¬ (σ₁ ⟶ σ₂) ⊥         ¬≰ = ⊥-elim (¬≰ (λ ()))
drop-¬¬ (σ₁ ⟶ σ₂) (var x)   ¬≰ = ⊥-elim (¬≰ (λ ()))
