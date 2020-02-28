------------------------------------------------------------------------
-- Incorrect coinductive axiomatisation of subtyping
------------------------------------------------------------------------

-- This module shows that if we remove transitivity from
-- RecursiveTypes.Subtyping.Axiomatic.Coinductive._≤_, and take the
-- transitive closure of the resulting relation, then we get a weaker
-- (less defined) relation than the one we started with.

module RecursiveTypes.Subtyping.Axiomatic.Incorrect where

open import Codata.Musical.Notation
open import Data.Fin using (Fin; zero; suc)
open import Function using (id; _$_)
open import Data.Nat
  using (ℕ; zero; suc; z≤n; s≤s; ≤′-refl) renaming (_≤_ to _≤ℕ_)
open import Data.Nat.Induction
open import Data.Nat.Properties using (≤-step; ≤⇒≤′)
open import Data.Product as Prod
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary

open import RecursiveTypes.Syntax hiding (_≲_)
open import RecursiveTypes.Substitution using (_[0≔_]; unfold[μ_⟶_])
open import RecursiveTypes.Subtyping.Semantic.Coinductive as Sem
  using (_≤Coind_; ⊥; ⊤; _⟶_)

------------------------------------------------------------------------
-- The alternative "subtyping" relation

infixr 10 _⟶_
infix  4  _≤_ _≤′_
infixr 2  _≤⟨_⟩_
infix  2  _∎

-- A definition which does not include a transitivity constructor.

data _≤′_ {n} : Ty n → Ty n → Set where
  ⊥   : ∀ {τ} → ⊥ ≤′ τ
  ⊤   : ∀ {σ} → σ ≤′ ⊤
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
        (τ₁≤′σ₁ : ∞ (τ₁ ≤′ σ₁)) (σ₂≤′τ₂ : ∞ (σ₂ ≤′ τ₂)) →
        σ₁ ⟶ σ₂ ≤′ τ₁ ⟶ τ₂

  unfold : ∀ {τ₁ τ₂} → μ τ₁ ⟶ τ₂ ≤′ unfold[μ τ₁ ⟶ τ₂ ]
  fold   : ∀ {τ₁ τ₂} → unfold[μ τ₁ ⟶ τ₂ ] ≤′ μ τ₁ ⟶ τ₂

  _∎ : ∀ τ → τ ≤′ τ

-- The transitive closure of this relation.

data _≤_ {n} : Ty n → Ty n → Set where
  include : ∀ {σ τ} (σ≤τ : σ ≤′ τ) → σ ≤ τ
  _≤⟨_⟩_  : ∀ τ₁ {τ₂ τ₃} (τ₁≤τ₂ : τ₁ ≤ τ₂) (τ₂≤τ₃ : τ₂ ≤ τ₃) → τ₁ ≤ τ₃

------------------------------------------------------------------------
-- Some types used in counterexamples below

σ : Ty zero
σ = μ ⊤ ⟶ var zero

τ : Ty zero
τ = μ ⊥ ⟶ var zero

σ≤τ : σ ≤Coind τ
σ≤τ = ♯ ⊥ ⟶ ♯ σ≤τ

------------------------------------------------------------------------
-- Soundness and incompleteness of _≤′_

sound′ : ∀ {n} {σ τ : Ty n} → σ ≤′ τ → σ ≤Coind τ
sound′ ⊥               = ⊥
sound′ ⊤               = ⊤
sound′ (τ₁≤σ₁ ⟶ σ₂≤τ₂) = ♯ sound′ (♭ τ₁≤σ₁) ⟶ ♯ sound′ (♭ σ₂≤τ₂)
sound′ unfold          = Sem.unfold
sound′ fold            = Sem.fold
sound′ (τ ∎)           = Sem.refl∞ _

incomplete′ : ¬ (∀ {n} {σ τ : Ty n} → σ ≤Coind τ → σ ≤′ τ)
incomplete′ hyp with hyp {σ = σ} {τ = τ} σ≤τ
... | ()

------------------------------------------------------------------------
-- Soundness of _≤_

sound : ∀ {n} {σ τ : Ty n} → σ ≤ τ → σ ≤Coind τ
sound (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = Sem.trans (sound τ₁≤τ₂) (sound τ₂≤τ₃)
sound (include σ≤τ)         = sound′ σ≤τ

------------------------------------------------------------------------
-- An alternative definition of the transitive closure of _≤′_

infixr 5 _∷_
infix  4 _≲_

data _≲_ {n} : Ty n → Ty n → Set where
  [_] : ∀ {σ τ} (σ≤τ : σ ≤′ τ) → σ ≲ τ
  _∷_ : ∀ {τ₁ τ₂ τ₃} (τ₁≤τ₂ : τ₁ ≤′ τ₂) (τ₂≲τ₃ : τ₂ ≲ τ₃) → τ₁ ≲ τ₃

-- This definition is transitive.

_++_ : ∀ {n} {τ₁ τ₂ τ₃ : Ty n} → τ₁ ≲ τ₂ → τ₂ ≲ τ₃ → τ₁ ≲ τ₃
[ τ₁≤τ₂ ]       ++ τ₂≤τ₃ = τ₁≤τ₂ ∷ τ₂≤τ₃
(τ₁≤τ₂ ∷ τ₂≤τ₃) ++ τ₃≤τ₄ = τ₁≤τ₂ ∷ (τ₂≤τ₃ ++ τ₃≤τ₄)

-- Hence it is complete with respect to the one above.

≲-complete : ∀ {n} {σ τ : Ty n} → σ ≤ τ → σ ≲ τ
≲-complete (include σ≤τ)         = [ σ≤τ ]
≲-complete (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = ≲-complete τ₁≤τ₂ ++ ≲-complete τ₂≤τ₃

-- It is also sound.

≲-sound : ∀ {n} {σ τ : Ty n} → σ ≲ τ → σ ≤ τ
≲-sound [ σ≤τ ]         = include σ≤τ
≲-sound (τ₁≤τ₂ ∷ τ₂≲τ₃) = _ ≤⟨ include τ₁≤τ₂ ⟩ ≲-sound τ₂≲τ₃

-- The number of uses of transitivity in the proof.

length : ∀ {n} {σ τ : Ty n} → σ ≲ τ → ℕ
length [ σ≤τ ]         = 0
length (τ₁≤τ₂ ∷ τ₂≲τ₃) = suc (length τ₂≲τ₃)

------------------------------------------------------------------------
-- Given proofs of certain statements one can extract shorter or
-- equally long proofs for related statements

mutual

  codomain-⟶μ : ∀ {n} {σ₁ σ₂ : Ty n} {τ₁ τ₂} →
                (σ₁⟶σ₂≲μτ₁⟶τ₂ : σ₁ ⟶ σ₂ ≲ μ τ₁ ⟶ τ₂) →
                ∃ λ (σ₂≲τ₂′ : σ₂ ≲ τ₂ [0≔ μ τ₁ ⟶ τ₂ ]) →
                    length σ₂≲τ₂′ ≤ℕ length σ₁⟶σ₂≲μτ₁⟶τ₂
  codomain-⟶μ [ fold ]                  = ([ _ ∎ ] , z≤n)
  codomain-⟶μ (τ₁≤′σ₁ ⟶ σ₂≤′τ₂ ∷ τ₂≲τ₃) = Prod.map (_∷_ (♭ σ₂≤′τ₂)) s≤s (codomain-⟶μ τ₂≲τ₃)
  codomain-⟶μ (fold            ∷ τ₂≲τ₃) = Prod.map id ≤-step (codomain-μμ τ₂≲τ₃)
  codomain-⟶μ ((._ ∎)          ∷ τ₂≲τ₃) = Prod.map id ≤-step (codomain-⟶μ τ₂≲τ₃)
  codomain-⟶μ (⊤               ∷ τ₂≲τ₃) with sound (≲-sound τ₂≲τ₃)
  ... | ()

  codomain-μμ : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : Ty (suc n)} →
                (μσ₁⟶σ₂≲μτ₁⟶τ₂ : μ σ₁ ⟶ σ₂ ≲ μ τ₁ ⟶ τ₂) →
                ∃ λ (σ₂′≲τ₂′ : σ₂ [0≔ μ σ₁ ⟶ σ₂ ] ≲ τ₂ [0≔ μ τ₁ ⟶ τ₂ ]) →
                    length σ₂′≲τ₂′ ≤ℕ length μσ₁⟶σ₂≲μτ₁⟶τ₂
  codomain-μμ [ ._ ∎ ]         = ([ _ ∎ ] , z≤n)
  codomain-μμ (unfold ∷ τ₂≲τ₃) = Prod.map id ≤-step (codomain-⟶μ τ₂≲τ₃)
  codomain-μμ ((._ ∎) ∷ τ₂≲τ₃) = Prod.map id ≤-step (codomain-μμ τ₂≲τ₃)
  codomain-μμ (⊤      ∷ τ₂≲τ₃) with sound (≲-sound τ₂≲τ₃)
  ... | ()

------------------------------------------------------------------------
-- Incompleteness of _≤_

incomplete : ¬ (∀ {n} {σ τ : Ty n} → σ ≤Coind τ → σ ≤ τ)
incomplete hyp = σ≴τ $ ≲-complete $ hyp σ≤τ
  where
  σ≴τ : ¬ σ ≲ τ
  σ≴τ σ≲τ = <′-rec Pred ≴ _ σ≲τ refl
    where
    Pred : ℕ → Set
    Pred n = (σ≲τ : σ ≲ τ) → length σ≲τ ≢ n

    ≴ : ∀ n → <′-Rec Pred n → Pred n
    ≴ n  rec [ () ]           _
    ≴ ._ rec ((._ ∎) ∷ τ₂≲τ₃) refl = rec _ ≤′-refl τ₂≲τ₃ refl
    ≴ ._ rec (unfold ∷ τ₂≲τ₃) refl with codomain-⟶μ τ₂≲τ₃
    ... | (τ₂≲τ₃′ , not-longer) = rec _ (≤⇒≤′ $ s≤s not-longer) τ₂≲τ₃′ refl
    ≴ n  rec (⊤      ∷ τ₂≲τ₃) _    with sound (≲-sound τ₂≲τ₃)
    ... | ()
