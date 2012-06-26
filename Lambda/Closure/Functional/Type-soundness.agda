------------------------------------------------------------------------
-- A type system and a type soundness result
------------------------------------------------------------------------

module Lambda.Closure.Functional.Type-soundness where

import Category.Monad.Partiality as Partiality
open import Category.Monad.Partiality.All as All
  using (All; now; later)
open import Coinduction
open import Data.Fin using (Fin; zero; suc)
open import Data.Maybe as Maybe using (Maybe; just; nothing)
open import Data.Nat
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary

open All.Alternative
private
  open module E {A : Set} = Partiality.Equality (_≡_ {A = A})
    using (_≈_; now; laterˡ)

open import Lambda.Closure.Functional
open Lambda.Closure.Functional.PF using (fail)
open Lambda.Closure.Functional.Workaround using (⟪_⟫P)
open import Lambda.Syntax
open Lambda.Syntax.Closure Tm

------------------------------------------------------------------------
-- Type system (following Leroy and Grall)

-- Recursive, simple types, defined coinductively.

infixr 8 _⇾_

data Ty : Set where
  nat : Ty
  _⇾_ : (σ τ : ∞ Ty) → Ty

-- Contexts.

Ctxt : ℕ → Set
Ctxt n = Vec Ty n

-- Type system.

infixl 9 _·_
infix  4 _⊢_∈_

data _⊢_∈_ {n} (Γ : Ctxt n) : Tm n → Ty → Set where
  con : ∀ {i} → Γ ⊢ con i ∈ nat
  var : ∀ {x} → Γ ⊢ var x ∈ lookup x Γ
  ƛ   : ∀ {t σ τ} (t∈ : ♭ σ ∷ Γ ⊢ t ∈ ♭ τ) → Γ ⊢ ƛ t ∈ σ ⇾ τ
  _·_ : ∀ {t₁ t₂ σ τ} (t₁∈ : Γ ⊢ t₁ ∈ σ ⇾ τ) (t₂∈ : Γ ⊢ t₂ ∈ ♭ σ) →
        Γ ⊢ t₁ · t₂ ∈ ♭ τ

-- Ω is well-typed.

Ω-well-typed : (τ : Ty) → [] ⊢ Ω ∈ τ
Ω-well-typed τ =
  _·_ {σ = ♯ σ} {τ = ♯ τ} (ƛ (var · var)) (ƛ (var · var))
  where σ = ♯ σ ⇾ ♯ τ

-- A call-by-value fix-point combinator.

Z : Tm 0
Z = ƛ (t · t)
  where t = ƛ (vr 1 · ƛ (vr 1 · vr 1 · vr 0))

-- This combinator is also well-typed.

fix-well-typed :
  ∀ {σ τ} → [] ⊢ Z ∈ ♯ (♯ (σ ⇾ τ) ⇾ ♯ (σ ⇾ τ)) ⇾ ♯ (σ ⇾ τ)
fix-well-typed =
  ƛ (_·_ {σ = υ} {τ = ♯ _}
         (ƛ (var · ƛ (var · var · var)))
         (ƛ (var · ƛ (var · var · var))))
  where
  υ : ∞ Ty
  υ = ♯ (υ ⇾ ♯ _)

------------------------------------------------------------------------
-- Type soundness

-- WF-Value, WF-Env and WF-MV specify when a
-- value/environment/potential value is well-formed with respect to a
-- given context (and type).

mutual

  data WF-Value : Ty → Value → Set where
    con : ∀ {i} → WF-Value nat (con i)
    ƛ   : ∀ {n Γ σ τ} {t : Tm (1 + n)} {ρ}
          (t∈ : ♭ σ ∷ Γ ⊢ t ∈ ♭ τ) (ρ-wf : WF-Env Γ ρ) →
          WF-Value (σ ⇾ τ) (ƛ t ρ)

  infixr 5 _∷_

  data WF-Env : ∀ {n} → Ctxt n → Env n → Set where
    []  : WF-Env [] []
    _∷_ : ∀ {n} {Γ : Ctxt n} {ρ σ v}
          (v-wf : WF-Value σ v) (ρ-wf : WF-Env Γ ρ) →
          WF-Env (σ ∷ Γ) (v ∷ ρ)

WF-MV : Ty → Maybe Value → Set
WF-MV σ = Maybe.Any (WF-Value σ)

-- Variables pointing into a well-formed environment refer to
-- well-formed values.

lookup-wf : ∀ {n Γ ρ} (x : Fin n) → WF-Env Γ ρ →
            WF-Value (lookup x Γ) (lookup x ρ)
lookup-wf zero    (v-wf ∷ ρ-wf) = v-wf
lookup-wf (suc x) (v-wf ∷ ρ-wf) = lookup-wf x ρ-wf

-- If we can prove All (WF-MV σ) x, then x does not "go wrong".

does-not-go-wrong : ∀ {σ x} → All (WF-MV σ) x → ¬ x ≈ fail
does-not-go-wrong (now (just _)) (now ())
does-not-go-wrong (later x-wf)   (laterˡ x↯) =
  does-not-go-wrong (♭ x-wf) x↯

-- Well-typed programs do not "go wrong".

mutual

  ⟦⟧-wf : ∀ {n Γ} (t : Tm n) {σ} → Γ ⊢ t ∈ σ →
          ∀ {ρ} → WF-Env Γ ρ → AllP (WF-MV σ) (⟦ t ⟧ ρ)
  ⟦⟧-wf (con i)   con             ρ-wf = now (just con)
  ⟦⟧-wf (var x)   var             ρ-wf = now (just (lookup-wf x ρ-wf))
  ⟦⟧-wf (ƛ t)     (ƛ t∈)          ρ-wf = now (just (ƛ t∈ ρ-wf))
  ⟦⟧-wf (t₁ · t₂) (t₁∈ · t₂∈) {ρ} ρ-wf =
    ⟦ t₁ · t₂ ⟧ ρ          ≅⟨ ·-comp t₁ t₂ ⟩P
    ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ   ⟨ (⟦⟧-wf t₁ t₁∈ ρ-wf >>=-congP λ { .{_} (just f-wf) →
                               ⟦⟧-wf t₂ t₂∈ ρ-wf >>=-congP λ { .{_} (just v-wf) →
                               ∙-wf f-wf v-wf }}) ⟩P

  ∙-wf : ∀ {σ τ f v} →
         WF-Value (σ ⇾ τ) f → WF-Value (♭ σ) v →
         AllP (WF-MV (♭ τ)) ⟪ f ∙ v ⟫P
  ∙-wf (ƛ t₁∈ ρ₁-wf) v₂-wf = later (♯ ⟦⟧-wf _ t₁∈ (v₂-wf ∷ ρ₁-wf))

type-soundness : ∀ {t : Tm 0} {σ} → [] ⊢ t ∈ σ → ¬ ⟦ t ⟧ [] ≈ fail
type-soundness t∈ =
  does-not-go-wrong (All.Alternative.sound (⟦⟧-wf _ t∈ []))
