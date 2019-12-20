------------------------------------------------------------------------
-- Functional semantics and type soundness proof for an untyped
-- λ-calculus with constants
------------------------------------------------------------------------

module Lambda.Substitution.Functional where

open import Category.Monad.Partiality as Partiality using (_⊥; never)
open import Category.Monad.Partiality.All as All
  using (All; now; later)
open import Codata.Musical.Notation
open import Data.Maybe as Maybe using (Maybe)
open import Data.Maybe.Relation.Unary.Any as Maybe using (just)
open import Data.Vec using ([])
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary

open All.Alternative
private
  open module E {A : Set} = Partiality.Equality (_≡_ {A = A})
  open module R {A : Set} =
    Partiality.Reasoning (P.isEquivalence {A = A})

open import Lambda.Syntax
open WHNF
open import Lambda.Substitution
open import Lambda.Closure.Functional
  using (module PF; module Workaround)
open Workaround hiding (_>>=_)

------------------------------------------------------------------------
-- Semantics

infix 5 _∙_

-- Note that this definition gives us determinism "for free".

mutual

  ⟦_⟧′ : Tm 0 → Maybe (Value 0) ⊥P
  ⟦ con i ⟧′   = return (con i)
  ⟦ var () ⟧′
  ⟦ ƛ t ⟧′     = return (ƛ t)
  ⟦ t₁ · t₂ ⟧′ = ⟦ t₁ ⟧′ >>= λ v₁ →
                 ⟦ t₂ ⟧′ >>= λ v₂ →
                 v₁ ∙ v₂
    where open Workaround

  _∙_ : Value 0 → Value 0 → Maybe (Value 0) ⊥P
  con i ∙ v₂ = fail
  ƛ t₁  ∙ v₂ = later (♯ ⟦ t₁ / sub ⌜ v₂ ⌝ ⟧′)

⟦_⟧ : Tm 0 → Maybe (Value 0) ⊥
⟦ t ⟧ = ⟪ ⟦ t ⟧′ ⟫P

------------------------------------------------------------------------
-- Example

Ω-loops : ⟦ Ω ⟧ ≈ never
Ω-loops = later (♯ Ω-loops)

------------------------------------------------------------------------
-- Some lemmas

open PF hiding (_>>=_)

-- An abbreviation.

infix 5 _⟦·⟧_

_⟦·⟧_ : Maybe (Value 0) ⊥ → Maybe (Value 0) ⊥ → Maybe (Value 0) ⊥
v₁ ⟦·⟧ v₂ = v₁ >>= λ v₁ → v₂ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P
  where open PF

-- _⟦·⟧_ preserves equality.

_⟦·⟧-cong_ : ∀ {k v₁₁ v₁₂ v₂₁ v₂₂} →
             Rel k v₁₁ v₂₁ → Rel k v₁₂ v₂₂ →
             Rel k (v₁₁ ⟦·⟧ v₁₂) (v₂₁ ⟦·⟧ v₂₂)
v₁₁≈v₂₁ ⟦·⟧-cong v₁₂≈v₂₂ =
  v₁₁≈v₂₁ >>=-cong λ v₁ →
  v₁₂≈v₂₂ >>=-cong λ v₂ →
  ⟪ v₁ ∙ v₂ ⟫P ∎

-- The semantics of application is compositional (with respect to the
-- syntactic equality which is used).

·-comp : (t₁ t₂ : Tm 0) →
         ⟦ t₁ · t₂ ⟧ ≅ ⟦ t₁ ⟧ ⟦·⟧ ⟦ t₂ ⟧
·-comp t₁ t₂ =
  ⟦ t₁ · t₂ ⟧                                  ≅⟨ >>=-hom ⟦ t₁ ⟧′ _ ⟩

  PF._>>=_ ⟦ t₁ ⟧ (λ v₁ →
           ⟪ Workaround._>>=_ ⟦ t₂ ⟧′ (λ v₂ →
             v₁ ∙ v₂) ⟫P)                      ≅⟨ ((⟦ t₁ ⟧ ∎) >>=-cong λ _ →
                                                   >>=-hom ⟦ t₂ ⟧′ _) ⟩
  ⟦ t₁ ⟧ ⟦·⟧ ⟦ t₂ ⟧                            ∎

------------------------------------------------------------------------
-- Type soundness

-- WF-Value and WF-MV specify when a (potential) value is well-formed
-- with respect to a given type.

WF-Value : Ty → Value 0 → Set
WF-Value σ v = [] ⊢ ⌜ v ⌝ ∈ σ

WF-MV : Ty → Maybe (Value 0) → Set
WF-MV σ = Maybe.Any (WF-Value σ)

-- If we can prove All (WF-MV σ) x, then x does not "go wrong".

does-not-go-wrong : ∀ {σ x} → All (WF-MV σ) x → ¬ x ≈ PF.fail
does-not-go-wrong (now (just _)) (now ())
does-not-go-wrong (later x-wf)   (laterˡ x↯) =
  does-not-go-wrong (♭ x-wf) x↯

-- Well-typed programs do not "go wrong".

mutual

  ⟦⟧-wf : ∀ (t : Tm 0) {σ} → [] ⊢ t ∈ σ →
          AllP (WF-MV σ) ⟦ t ⟧
  ⟦⟧-wf (con i)   con         = now (just con)
  ⟦⟧-wf (var ())  var
  ⟦⟧-wf (ƛ t)     (ƛ t∈)      = now (just (ƛ t∈))
  ⟦⟧-wf (t₁ · t₂) (t₁∈ · t₂∈) =
    ⟦ t₁ · t₂ ⟧        ≅⟨ ·-comp t₁ t₂ ⟩P
    ⟦ t₁ ⟧ ⟦·⟧ ⟦ t₂ ⟧   ⟨ (⟦⟧-wf t₁ t₁∈ >>=-congP λ { .{_} (just f-wf) →
                           ⟦⟧-wf t₂ t₂∈ >>=-congP λ { .{_} (just v-wf) →
                           ∙-wf f-wf v-wf }}) ⟩P

  ∙-wf : ∀ {σ τ f v} →
         WF-Value (σ ⇾ τ) f → WF-Value (♭ σ) v →
         AllP (WF-MV (♭ τ)) ⟪ f ∙ v ⟫P
  ∙-wf {f = con _} ()      _
  ∙-wf {f = ƛ t₁}  (ƛ t₁∈) v₂∈ =
    later (♯ ⟦⟧-wf _ (/-preserves t₁∈ (sub-preserves v₂∈)))

type-soundness : ∀ {t σ} → [] ⊢ t ∈ σ → ¬ ⟦ t ⟧ ≈ PF.fail
type-soundness t∈ =
  does-not-go-wrong (All.Alternative.sound (⟦⟧-wf _ t∈))
