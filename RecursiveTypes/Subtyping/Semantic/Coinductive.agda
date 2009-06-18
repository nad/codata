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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

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

data _≤∞_ {n} : Tree n → Tree n → Set where
  ⊥   : ∀ {τ} → ⊥ ≤∞ τ
  ⊤   : ∀ {σ} → σ ≤∞ ⊤
  var : ∀ {x} → var x ≤∞ var x
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
        (τ₁≤σ₁ : ∞ (♭ τ₁ ≤∞ ♭ σ₁)) (σ₂≤τ₂ : ∞ (♭ σ₂ ≤∞ ♭ τ₂)) →
        σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂

-- Subtyping for recursive types is defined in terms of subtyping for
-- trees.

_≤Coind_ : ∀ {n k} → Ty n k → Ty n k → Set
σ ≤Coind τ = ⟦ σ ⟧ ≤∞ ⟦ τ ⟧

------------------------------------------------------------------------
-- A trick used to ensure guardedness of expressions using
-- transitivity

infix 4 _≤∞Prog_ _≤∞WHNF_

data _≤∞Prog_ {n} : Tree n → Tree n → Set where
  ⊥      : ∀ {τ} → ⊥ ≤∞Prog τ
  ⊤      : ∀ {σ} → σ ≤∞Prog ⊤
  var    : ∀ {x} → var x ≤∞Prog var x
  _⟶_    : ∀ {σ₁ σ₂ τ₁ τ₂}
           (τ₁≤σ₁ : ∞ (♭ τ₁ ≤∞Prog ♭ σ₁)) (σ₂≤τ₂ : ∞ (♭ σ₂ ≤∞Prog ♭ τ₂)) →
           σ₁ ⟶ σ₂ ≤∞Prog τ₁ ⟶ τ₂
  -- Reflexivity.
  _∎     : ∀ τ → τ ≤∞Prog τ
  -- Transitivity.
  _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
           (τ₁≤τ₂ : τ₁ ≤∞Prog τ₂) (τ₂≤τ₃ : τ₂ ≤∞Prog τ₃) → τ₁ ≤∞Prog τ₃

data _≤∞WHNF_ {n} : Tree n → Tree n → Set where
  ⊥   : ∀ {τ} → ⊥ ≤∞WHNF τ
  ⊤   : ∀ {σ} → σ ≤∞WHNF ⊤
  var : ∀ {x} → var x ≤∞WHNF var x
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
        (τ₁≤σ₁ : ♭ τ₁ ≤∞Prog ♭ σ₁) (σ₂≤τ₂ : ♭ σ₂ ≤∞Prog ♭ τ₂) →
        σ₁ ⟶ σ₂ ≤∞WHNF τ₁ ⟶ τ₂

whnf : ∀ {n} {σ τ : Tree n} → σ ≤∞Prog τ → σ ≤∞WHNF τ
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

  value : ∀ {n} {σ τ : Tree n} → σ ≤∞WHNF τ → σ ≤∞ τ
  value ⊥               = ⊥
  value ⊤               = ⊤
  value var             = var
  value (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♯ ⟦ τ₁≤σ₁ ⟧≤∞ ⟶ ♯ ⟦ σ₂≤τ₂ ⟧≤∞

  ⟦_⟧≤∞ : ∀ {n} {σ τ : Tree n} → σ ≤∞Prog τ → σ ≤∞ τ
  ⟦ σ≤τ ⟧≤∞ = value (whnf σ≤τ)

prog : ∀ {n} {σ τ : Tree n} → σ ≤∞ τ → σ ≤∞Prog τ
prog ⊥               = ⊥
prog ⊤               = ⊤
prog var             = var
prog (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♯ prog (♭ τ₁≤σ₁) ⟶ ♯ prog (♭ σ₂≤τ₂)

------------------------------------------------------------------------
-- Some lemmas

trans : ∀ {n} {τ₁ τ₂ τ₃ : Tree n} →
        τ₁ ≤∞ τ₂ → τ₂ ≤∞ τ₃ → τ₁ ≤∞ τ₃
trans {τ₁ = τ₁} {τ₂} {τ₃} τ₁≤τ₂ τ₂≤τ₃ =
  ⟦ τ₁ ≤⟨ prog τ₁≤τ₂ ⟩
    τ₂ ≤⟨ prog τ₂≤τ₃ ⟩
    τ₃ ∎ ⟧≤∞

unfold : ∀ {n} (τ : Ty (suc n) guarding) →
         μ τ ≤Coind unfold[μ τ ]
unfold (_ ⟶ _) = ♯ ⟦ _ ∎ ⟧≤∞ ⟶ ♯ ⟦ _ ∎ ⟧≤∞

fold : ∀ {n} (τ : Ty (suc n) guarding) →
       unfold[μ τ ] ≤Coind μ τ
fold (_ ⟶ _) = ♯ ⟦ _ ∎ ⟧≤∞ ⟶ ♯ ⟦ _ ∎ ⟧≤∞

var:≤∞⟶≡ : ∀ {n} {x y : Fin n} →
           var x ≤∞ var y → var x ≡ var y
var:≤∞⟶≡ var = refl

left-proj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : ∞ (Tree n)} →
            σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂ → ♭ τ₁ ≤∞ ♭ σ₁
left-proj (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♭ τ₁≤σ₁

right-proj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : ∞ (Tree n)} →
             σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂ → ♭ σ₂ ≤∞ ♭ τ₂
right-proj (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♭ σ₂≤τ₂

------------------------------------------------------------------------
-- Double-negation does not affect _≤∞_

drop-¬¬ : ∀ {n} (σ τ : Tree n) → ¬ ¬ σ ≤∞ τ → σ ≤∞ τ
drop-¬¬ ⊥         τ         ¬≰ = ⊥
drop-¬¬ σ         ⊤         ¬≰ = ⊤
drop-¬¬ (var x)   (var  y)  ¬≰ with var x ≡? var y
drop-¬¬ (var x)   (var .x)  ¬≰ | yes refl = var
drop-¬¬ (var x)   (var  y)  ¬≰ | no  x≠y  = ⊥-elim (¬≰ (x≠y ∘ var:≤∞⟶≡))
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
