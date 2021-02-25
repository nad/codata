------------------------------------------------------------------------
-- Coinductive definition of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Semantic.Coinductive where

open import Codata.Musical.Notation
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin)
open import Function.Base
open import Data.Empty using (⊥-elim)
open import Relation.Nullary
open import Relation.Nullary.Negation hiding (stable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
open import RecursiveTypes.Semantics

infixr 10 _⟶_
infix  4  _≤∞_ _≤Coind_
infix  3  _∎
infixr 2  _≤⟨_⟩_

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

_≤Coind_ : ∀ {n} → Ty n → Ty n → Set
σ ≤Coind τ = ⟦ σ ⟧ ≤∞ ⟦ τ ⟧

------------------------------------------------------------------------
-- A trick used to ensure guardedness of expressions using
-- transitivity

infix 4 _≤∞P_ _≤∞W_

data _≤∞P_ {n} : Tree n → Tree n → Set where
  ⊥      : ∀ {τ} → ⊥ ≤∞P τ
  ⊤      : ∀ {σ} → σ ≤∞P ⊤
  var    : ∀ {x} → var x ≤∞P var x
  _⟶_    : ∀ {σ₁ σ₂ τ₁ τ₂}
           (τ₁≤σ₁ : ∞ (♭ τ₁ ≤∞P ♭ σ₁)) (σ₂≤τ₂ : ∞ (♭ σ₂ ≤∞P ♭ τ₂)) →
           σ₁ ⟶ σ₂ ≤∞P τ₁ ⟶ τ₂
  -- Transitivity.
  _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
           (τ₁≤τ₂ : τ₁ ≤∞P τ₂) (τ₂≤τ₃ : τ₂ ≤∞P τ₃) → τ₁ ≤∞P τ₃

data _≤∞W_ {n} : Tree n → Tree n → Set where
  ⊥   : ∀ {τ} → ⊥ ≤∞W τ
  ⊤   : ∀ {σ} → σ ≤∞W ⊤
  var : ∀ {x} → var x ≤∞W var x
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
        (τ₁≤σ₁ : ♭ τ₁ ≤∞P ♭ σ₁) (σ₂≤τ₂ : ♭ σ₂ ≤∞P ♭ τ₂) →
        σ₁ ⟶ σ₂ ≤∞W τ₁ ⟶ τ₂

transW : ∀ {n} {τ₁ τ₂ τ₃ : Tree n} →
         τ₁ ≤∞W τ₂ → τ₂ ≤∞W τ₃ → τ₁ ≤∞W τ₃
transW ⊥               _               = ⊥
transW _               ⊤               = ⊤
transW var             var             = var
transW (τ₁≤σ₁ ⟶ σ₂≤τ₂) (χ₁≤τ₁ ⟶ τ₂≤χ₂) =
  (_ ≤⟨ χ₁≤τ₁ ⟩ τ₁≤σ₁) ⟶ (_ ≤⟨ σ₂≤τ₂ ⟩ τ₂≤χ₂)

whnf : ∀ {n} {σ τ : Tree n} → σ ≤∞P τ → σ ≤∞W τ
whnf ⊥                    = ⊥
whnf ⊤                    = ⊤
whnf var                  = var
whnf (τ₁≤σ₁ ⟶ σ₂≤τ₂)      = ♭ τ₁≤σ₁ ⟶ ♭ σ₂≤τ₂
whnf (σ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = transW (whnf τ₁≤τ₂) (whnf τ₂≤τ₃)

mutual

  ⟦_⟧W : ∀ {n} {σ τ : Tree n} → σ ≤∞W τ → σ ≤∞ τ
  ⟦ ⊥             ⟧W = ⊥
  ⟦ ⊤             ⟧W = ⊤
  ⟦ var           ⟧W = var
  ⟦ τ₁≤σ₁ ⟶ σ₂≤τ₂ ⟧W = ♯ ⟦ τ₁≤σ₁ ⟧P ⟶ ♯ ⟦ σ₂≤τ₂ ⟧P

  ⟦_⟧P : ∀ {n} {σ τ : Tree n} → σ ≤∞P τ → σ ≤∞ τ
  ⟦ σ≤τ ⟧P = ⟦ whnf σ≤τ ⟧W

⌜_⌝ : ∀ {n} {σ τ : Tree n} → σ ≤∞ τ → σ ≤∞P τ
⌜ ⊥             ⌝ = ⊥
⌜ ⊤             ⌝ = ⊤
⌜ var           ⌝ = var
⌜ τ₁≤σ₁ ⟶ σ₂≤τ₂ ⌝ = ♯ ⌜ ♭ τ₁≤σ₁ ⌝ ⟶ ♯ ⌜ ♭ σ₂≤τ₂ ⌝

------------------------------------------------------------------------
-- Some lemmas

refl∞ : ∀ {n} (τ : Tree n) → τ ≤∞ τ
refl∞ ⊥       = ⊥
refl∞ ⊤       = ⊤
refl∞ (var x) = var
refl∞ (σ ⟶ τ) = ♯ refl∞ (♭ σ) ⟶ ♯ refl∞ (♭ τ)

_∎ : ∀ {n} (τ : Tree n) → τ ≤∞P τ
τ ∎ = ⌜ refl∞ τ ⌝

trans : ∀ {n} {τ₁ τ₂ τ₃ : Tree n} →
        τ₁ ≤∞ τ₂ → τ₂ ≤∞ τ₃ → τ₁ ≤∞ τ₃
trans {τ₁ = τ₁} {τ₂} {τ₃} τ₁≤τ₂ τ₂≤τ₃ =
  ⟦ τ₁ ≤⟨ ⌜ τ₁≤τ₂ ⌝ ⟩
    τ₂ ≤⟨ ⌜ τ₂≤τ₃ ⌝ ⟩
    τ₃ ∎ ⟧P

unfold : ∀ {n} {τ₁ τ₂ : Ty (suc n)} →
         μ τ₁ ⟶ τ₂ ≤Coind unfold[μ τ₁ ⟶ τ₂ ]
unfold = ♯ refl∞ _ ⟶ ♯ refl∞ _

fold : ∀ {n} {τ₁ τ₂ : Ty (suc n)} →
       unfold[μ τ₁ ⟶ τ₂ ] ≤Coind μ τ₁ ⟶ τ₂
fold = ♯ refl∞ _ ⟶ ♯ refl∞ _

var:≤∞⟶≡ : ∀ {n} {x y : Fin n} →
           var x ≤∞ var y → Ty.var x ≡ Ty.var y
var:≤∞⟶≡ var = refl

left-proj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : ∞ (Tree n)} →
            σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂ → ♭ τ₁ ≤∞ ♭ σ₁
left-proj (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♭ τ₁≤σ₁

right-proj : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : ∞ (Tree n)} →
             σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂ → ♭ σ₂ ≤∞ ♭ τ₂
right-proj (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♭ σ₂≤τ₂

------------------------------------------------------------------------
-- _≤∞_ is stable under double-negation

stable : ∀ {n} (σ τ : Tree n) → Stable (σ ≤∞ τ)
stable ⊥         τ         ¬≰ = ⊥
stable σ         ⊤         ¬≰ = ⊤
stable (var x)   (var  y)  ¬≰ with var x ≡? var y
stable (var x)   (var .x)  ¬≰ | yes refl = var
stable (var x)   (var  y)  ¬≰ | no  x≠y  = ⊥-elim (¬≰ (x≠y ∘ var:≤∞⟶≡))
stable (σ₁ ⟶ σ₂) (τ₁ ⟶ τ₂) ¬≰ =
  ♯ stable (♭ τ₁) (♭ σ₁) (λ ≰ → ¬≰ (≰ ∘  left-proj)) ⟶
  ♯ stable (♭ σ₂) (♭ τ₂) (λ ≰ → ¬≰ (≰ ∘ right-proj))
stable ⊤         ⊥         ¬≰ = ⊥-elim (¬≰ (λ ()))
stable ⊤         (var x)   ¬≰ = ⊥-elim (¬≰ (λ ()))
stable ⊤         (τ₁ ⟶ τ₂) ¬≰ = ⊥-elim (¬≰ (λ ()))
stable (var x)   ⊥         ¬≰ = ⊥-elim (¬≰ (λ ()))
stable (var x)   (τ₁ ⟶ τ₂) ¬≰ = ⊥-elim (¬≰ (λ ()))
stable (σ₁ ⟶ σ₂) ⊥         ¬≰ = ⊥-elim (¬≰ (λ ()))
stable (σ₁ ⟶ σ₂) (var x)   ¬≰ = ⊥-elim (¬≰ (λ ()))
