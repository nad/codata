------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

{-# OPTIONS --no-termination-check #-}

module Lambda.Closure.Functional.No-workarounds where

open import Category.Monad
open import Category.Monad.Partiality as Partiality
  using (_⊥; never; OtherKind; other; steps)
open import Codata.Musical.Notation
open import Data.Empty using (⊥-elim)
open import Data.List hiding (lookup)
open import Data.Maybe hiding (_>>=_)
import Data.Maybe.Categorical as Maybe
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function
import Level
open import Relation.Binary using (module Preorder)
open import Relation.Binary.PropositionalEquality as P using (_≡_)
open import Relation.Nullary
open import Relation.Nullary.Negation

open Partiality._⊥
private
  open module E {A : Set} = Partiality.Equality (_≡_ {A = A})
  open module R {A : Set} =
    Partiality.Reasoning (P.isEquivalence {A = A})

open import Lambda.Syntax
open Closure Tm
open import Lambda.VirtualMachine
open Functional
private
  module VM = Closure Code

------------------------------------------------------------------------
-- A monad with partiality and failure

PF : RawMonad {f = Level.zero} (_⊥ ∘ Maybe)
PF = Maybe.monadT Partiality.monad

module PF where
  open RawMonad PF public

  fail : {A : Set} → Maybe A ⊥
  fail = now nothing

  _>>=-cong_ :
    ∀ {k} {A B : Set} {x₁ x₂ : Maybe A ⊥} {f₁ f₂ : A → Maybe B ⊥} →
    Rel k x₁ x₂ → (∀ x → Rel k (f₁ x) (f₂ x)) →
    Rel k (x₁ >>= f₁) (x₂ >>= f₂)
  _>>=-cong_ {k} {f₁ = f₁} {f₂} x₁≈x₂ f₁≈f₂ =
    Partiality._>>=-cong_ x₁≈x₂ helper
    where
    helper : ∀ {x y} → x ≡ y →
             Rel k (maybe f₁ fail x) (maybe f₂ fail y)
    helper {x = nothing} P.refl = fail ∎
    helper {x = just x}  P.refl = f₁≈f₂ x

  associative :
    {A B C : Set}
    (x : Maybe A ⊥) (f : A → Maybe B ⊥) (g : B → Maybe C ⊥) →
    (x >>= f >>= g) ≅ (x >>= λ y → f y >>= g)
  associative x f g =
    (x >>= f >>= g)                      ≅⟨ Partiality.associative P.refl x _ _ ⟩
    (x >>=′ λ y → maybe f fail y >>= g)  ≅⟨ Partiality._>>=-cong_ (x ∎) helper ⟩
    (x >>= λ y → f y >>= g)              ∎
    where
    open RawMonad Partiality.monad renaming (_>>=_ to _>>=′_)

    helper : ∀ {y₁ y₂} → y₁ ≡ y₂ →
             (maybe f fail y₁ >>= g) ≅ maybe (λ z → f z >>= g) fail y₂
    helper {y₁ = nothing} P.refl = fail ∎
    helper {y₁ = just y}  P.refl = (f y >>= g) ∎

  >>=-inversion-⇓ :
    ∀ {k} {A B : Set} x {f : A → Maybe B ⊥} {y} →
    (x>>=f⇓ : (x >>= f) ⇓[ k ] just y) →
    ∃ λ z → ∃₂ λ (x⇓ : x ⇓[ k ] just z)
                 (fz⇓ : f z ⇓[ k ] just y) →
                 steps x⇓ + steps fz⇓ ≡ steps x>>=f⇓
  >>=-inversion-⇓ x {f} x>>=f⇓
    with Partiality.>>=-inversion-⇓ {_∼A_ = _≡_} P.refl x x>>=f⇓
  ... | (nothing , x↯ , now ()  , _)
  ... | (just z  , x⇓ , fz⇓     , eq) = (z , x⇓ , fz⇓ , eq)

  >>=-inversion-⇑ :
    ∀ {k} {A B : Set} x {f : A → Maybe B ⊥} →
    (x >>= f) ⇑[ other k ] →
    ¬ ¬ (x ⇑[ other k ] ⊎
         ∃ λ y → x ⇓[ other k ] just y × f y ⇑[ other k ])
  >>=-inversion-⇑ {k} x {f} x>>=f⇑ =
    helper ⟨$⟩ Partiality.>>=-inversion-⇑ P.isEquivalence x x>>=f⇑
    where
    open RawMonad ¬¬-Monad renaming (_<$>_ to _⟨$⟩_)

    helper : (_ ⊎ ∃ λ (y : Maybe _) → _) → _
    helper (inj₁ x⇑                      ) = inj₁ x⇑
    helper (inj₂ (just y  , x⇓,fy⇑)      ) = inj₂ (y , x⇓,fy⇑)
    helper (inj₂ (nothing , x↯,now∼never)) =
      ⊥-elim (Partiality.now≉never (proj₂ x↯,now∼never))

open PF

------------------------------------------------------------------------
-- Semantics

infix 5 _∙_

-- Note that this definition gives us determinism "for free".

mutual

  ⟦_⟧ : ∀ {n} → Tm n → Env n → Maybe Value ⊥
  ⟦ con i ⟧   ρ = return (con i)
  ⟦ var x ⟧   ρ = return (lookup ρ x)
  ⟦ ƛ t ⟧     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧ ρ = ⟦ t₁ ⟧ ρ >>= λ v₁ →
                  ⟦ t₂ ⟧ ρ >>= λ v₂ →
                  v₁ ∙ v₂

  _∙_ : Value → Value → Maybe Value ⊥
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = later (♯ (⟦ t₁ ⟧ (v₂ ∷ ρ)))

------------------------------------------------------------------------
-- Example

Ω-loops : ⟦ Ω ⟧ [] ≈ never
Ω-loops = later (♯ Ω-loops)

------------------------------------------------------------------------
-- Some lemmas

-- An abbreviation.

infix 5 _⟦·⟧_

_⟦·⟧_ : Maybe Value ⊥ → Maybe Value ⊥ → Maybe Value ⊥
v₁ ⟦·⟧ v₂ = v₁ >>= λ v₁ → v₂ >>= λ v₂ → v₁ ∙ v₂

-- _⟦·⟧_ preserves equality.

_⟦·⟧-cong_ : ∀ {k v₁₁ v₁₂ v₂₁ v₂₂} →
             Rel k v₁₁ v₂₁ → Rel k v₁₂ v₂₂ →
             Rel k (v₁₁ ⟦·⟧ v₁₂) (v₂₁ ⟦·⟧ v₂₂)
v₁₁≈v₂₁ ⟦·⟧-cong v₁₂≈v₂₂ =
  v₁₁≈v₂₁ >>=-cong λ v₁ →
  v₁₂≈v₂₂ >>=-cong λ v₂ →
  v₁ ∙ v₂ ∎

-- The semantics of application is compositional (with respect to the
-- syntactic equality which is used).

·-comp : ∀ {n} (t₁ t₂ : Tm n) {ρ} →
         ⟦ t₁ · t₂ ⟧ ρ ≅ ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ
·-comp t₁ t₂ = _ ∎

------------------------------------------------------------------------
-- Compiler correctness

module Correctness where

  -- The relation _≈_ does not admit unrestricted use of transitivity
  -- in corecursive proofs, so I have formulated the correctness proof
  -- using a continuation. Note that the proof would perhaps be easier
  -- if the semantics was also formulated in continuation-passing
  -- style.

  mutual

    correct :
      ∀ {n} t {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
      (∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈ k v) →
      exec ⟨ comp t c , s , comp-env ρ ⟩ ≈ (⟦ t ⟧ ρ >>= k)
    correct (con i) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (Lambda.Syntax.Closure.con i) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (con i) ⟩
      k (con i)                                                    ∎)
    correct (var x) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (lookup (comp-env ρ) x) ∷ s , comp-env ρ ⟩  ≡⟨ P.cong (λ v → exec ⟨ c , val v ∷ s , comp-env ρ ⟩) (lookup-hom x ρ) ⟩
      exec ⟨ c , val (comp-val (lookup ρ x)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (lookup ρ x) ⟩
      k (lookup ρ x)                                             ∎)
    correct (ƛ t) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (comp-val (ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (ƛ t ρ) ⟩
      k (ƛ t ρ)                                             ∎)
    correct (t₁ · t₂) {ρ} {c} {s} {k} hyp =
      exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩      ≈⟨ correct t₁ (λ v₁ → correct t₂ (λ v₂ → ∙-correct v₁ v₂ hyp)) ⟩
      (⟦ t₁ ⟧ ρ >>= λ v₁ →  ⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂  >>= k)  ≅⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ → sym $ associative (⟦ t₂ ⟧ ρ) _ _) ⟩
      (⟦ t₁ ⟧ ρ >>= λ v₁ → (⟦ t₂ ⟧ ρ >>= λ v₂ → v₁ ∙ v₂) >>= k)  ≅⟨ sym $ associative (⟦ t₁ ⟧ ρ) _ _ ⟩
      (⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ >>= k)                              ≅⟨ _ ∎ ⟩
      (⟦ t₁ · t₂ ⟧ ρ >>= k)                                      ∎

    ∙-correct :
      ∀ {n} v₁ v₂ {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
      (∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈ k v) →
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s , comp-env ρ ⟩ ≈
      (v₁ ∙ v₂ >>= k)
    ∙-correct (con i)   v₂                 _   = fail ∎
    ∙-correct (ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val (ƛ t₁ ρ₁)) ∷ s , comp-env ρ ⟩  ≈⟨ later (♯ (

        exec ⟨ comp t₁ [ ret ] , ret c (comp-env ρ) ∷ s , comp-env (v₂ ∷ ρ₁) ⟩               ≈⟨ correct t₁ (λ v → laterˡ (hyp v)) ⟩
        (⟦ t₁ ⟧ (v₂ ∷ ρ₁) >>= k)                                                             ∎)) ⟩

      (ƛ t₁ ρ₁ ∙ v₂ >>= k)                                                              ∎

-- Note that the equality that is used here is syntactic.

correct : ∀ t →
          exec ⟨ comp t [] , [] , [] ⟩ ≈
          (⟦ t ⟧ [] >>= λ v → PF.return (comp-val v))
correct t = Correctness.correct t (λ v → return (comp-val v) ∎)
