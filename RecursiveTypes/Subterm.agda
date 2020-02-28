------------------------------------------------------------------------
-- Brandt and Henglein's subterm relation
------------------------------------------------------------------------

module RecursiveTypes.Subterm where

open import Algebra
open import Data.Fin using (Fin; zero; suc; lift)
open import Data.Nat
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Relation.Binary.BagAndSetEquality as BSEq
open import Data.List.Relation.Binary.Subset.Propositional
open import Data.List.Relation.Binary.Subset.Propositional.Properties
open import Data.Product
open import Data.Sum
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (module Inverse)
open import Relation.Binary
import Relation.Binary.Reasoning.Preorder as PreR
import Relation.Binary.Reasoning.Setoid as EqR
import Relation.Binary.PropositionalEquality as P
open import Data.Fin.Substitution

private
  open module SetM {A : Set} =
    CommutativeMonoid (BSEq.commutativeMonoid set A)
      using (_≈_)

open import RecursiveTypes.Syntax
open import RecursiveTypes.Substitution
  hiding (subst) renaming (id to idˢ)
open // using (_//_)

------------------------------------------------------------------------
-- Subterms

-- The subterm relation.

infix 4 _⊑_

data _⊑_ {n} : Ty n → Ty n → Set where
  refl   : ∀ {τ} → τ ⊑ τ
  unfold : ∀ {σ τ₁ τ₂} (σ⊑ : σ ⊑ unfold[μ τ₁ ⟶ τ₂ ]) → σ ⊑ μ τ₁ ⟶ τ₂
  ⟶ˡ     : ∀ {σ τ₁ τ₂} (σ⊑τ₁ : σ ⊑ τ₁) → σ ⊑ τ₁ ⟶ τ₂
  ⟶ʳ     : ∀ {σ τ₁ τ₂} (σ⊑τ₂ : σ ⊑ τ₂) → σ ⊑ τ₁ ⟶ τ₂

-- Some simple consequences.

unfold′ : ∀ {n} {τ₁ τ₂ : Ty (suc n)} →
          unfold[μ τ₁ ⟶ τ₂ ] ⊑ μ τ₁ ⟶ τ₂
unfold′ = unfold refl

⟶ˡ′ : ∀ {n} {τ₁ τ₂ : Ty n} → τ₁ ⊑ τ₁ ⟶ τ₂
⟶ˡ′ = ⟶ˡ refl

⟶ʳ′ : ∀ {n} {τ₁ τ₂ : Ty n} → τ₂ ⊑ τ₁ ⟶ τ₂
⟶ʳ′ = ⟶ʳ refl

-- The subterm relation is transitive.

trans : ∀ {n} {σ τ χ : Ty n} →
        σ ⊑ τ → τ ⊑ χ → σ ⊑ χ
trans σ⊑τ refl        = σ⊑τ
trans σ⊑τ (unfold τ⊑) = unfold (trans σ⊑τ τ⊑)
trans σ⊑τ (⟶ˡ τ⊑δ₁)   = ⟶ˡ (trans σ⊑τ τ⊑δ₁)
trans σ⊑τ (⟶ʳ τ⊑δ₂)   = ⟶ʳ (trans σ⊑τ τ⊑δ₂)

------------------------------------------------------------------------
-- Subterm closure

-- The list τ_∗ contains exactly the subterms of τ (possibly with
-- duplicates).
--
-- The important property is completeness, which ensures that the
-- number of distinct subterms of a given type is always finite.

mutual

  infix 7 _∗ _∗′

  _∗ : ∀ {n} → Ty n → List (Ty n)
  τ ∗ = τ ∷ τ ∗′

  _∗′ : ∀ {n} → Ty n → List (Ty n)
  (τ₁ ⟶ τ₂)   ∗′ = τ₁ ∗ ++ τ₂ ∗
  (μ τ₁ ⟶ τ₂) ∗′ = (τ₁ ⟶ τ₂ ∷ τ₁ ∗ ++ τ₂ ∗) // sub (μ τ₁ ⟶ τ₂)
  τ           ∗′ = []

------------------------------------------------------------------------
-- Soundness

-- _/_ is monotonous in its left argument.

/-monoˡ : ∀ {m n σ τ} {ρ : Sub Ty m n} →
          σ ⊑ τ → σ / ρ ⊑ τ / ρ
/-monoˡ refl                              = refl
/-monoˡ (⟶ˡ σ⊑τ₁)                         = ⟶ˡ (/-monoˡ σ⊑τ₁)
/-monoˡ (⟶ʳ σ⊑τ₂)                         = ⟶ʳ (/-monoˡ σ⊑τ₂)
/-monoˡ {ρ = ρ} (unfold {σ} {τ₁} {τ₂} σ⊑) =
  unfold $ P.subst (λ χ → σ / ρ ⊑ χ)
                   (sub-commutes (τ₁ ⟶ τ₂))
                   (/-monoˡ σ⊑)

sub-⊑-μ : ∀ {n} {σ : Ty (suc n)} {τ₁ τ₂} →
          σ ⊑ τ₁ ⟶ τ₂ → σ / sub (μ τ₁ ⟶ τ₂) ⊑ μ τ₁ ⟶ τ₂
sub-⊑-μ σ⊑τ₁⟶τ₂ = unfold (/-monoˡ σ⊑τ₁⟶τ₂)

-- All list elements are subterms.

sound : ∀ {n σ} (τ : Ty n) → σ ∈ τ ∗ → σ ⊑ τ
sound τ         (here P.refl) = refl
sound (τ₁ ⟶ τ₂) (there σ∈)    =
  [ ⟶ˡ ∘ sound τ₁ , ⟶ʳ ∘ sound τ₂ ]′
    (Inverse.from (++↔ {xs = τ₁ ∗}) ⟨$⟩ σ∈)
sound (μ τ₁ ⟶ τ₂) (there (here P.refl)) = unfold refl
sound (μ τ₁ ⟶ τ₂) (there (there σ∈))
  with Inverse.from (map-∈↔ (λ σ → σ / sub (μ τ₁ ⟶ τ₂))
                            {xs = τ₁ ∗ ++ τ₂ ∗}) ⟨$⟩ σ∈
... | (χ , χ∈ , P.refl) =
  sub-⊑-μ $ [ ⟶ˡ ∘ sound τ₁ , ⟶ʳ ∘ sound τ₂ ]′
              (Inverse.from (++↔ {xs = τ₁ ∗}) ⟨$⟩ χ∈)
sound ⊥       (there ())
sound ⊤       (there ())
sound (var x) (there ())

------------------------------------------------------------------------
-- Completeness

++-lemma : ∀ {A} xs ys {zs : List A} →
           (xs ++ zs) ++ (ys ++ zs) ≈ (xs ++ ys) ++ zs
++-lemma xs ys {zs} = begin
  (xs ++ zs) ++ (ys ++ zs)  ≈⟨ SetM.assoc xs zs (ys ++ zs) ⟩
  xs ++ (zs ++ (ys ++ zs))  ≈⟨ SetM.∙-cong (SetM.refl {x = xs}) (begin
    zs ++ (ys ++ zs)             ≈⟨ SetM.∙-cong (SetM.refl {x = zs}) (SetM.comm ys zs) ⟩
    zs ++ (zs ++ ys)             ≈⟨ SetM.sym $ SetM.assoc zs zs ys ⟩
    (zs ++ zs) ++ ys             ≈⟨ SetM.∙-cong (++-idempotent zs) SetM.refl ⟩
    zs ++ ys                     ≈⟨ SetM.comm zs ys ⟩
    ys ++ zs                     ∎) ⟩
  xs ++ (ys ++ zs)          ≈⟨ SetM.sym $ SetM.assoc xs ys zs ⟩
  (xs ++ ys) ++ zs          ∎
  where open EqR ([ set ]-Equality _)

open BSEq.⊆-Reasoning

mutual

  -- Weakening "commutes" with _∗.

  wk-∗-commute : ∀ k {n} (σ : Ty (k + n)) →
                 σ / wk ↑⋆ k ∗ ⊆ σ ∗ // wk ↑⋆ k
  wk-∗-commute k σ (here P.refl) = here P.refl
  wk-∗-commute k σ (there •∈•)   = there $ wk-∗′-commute k σ •∈•

  wk-∗′-commute : ∀ k {n} (σ : Ty (k + n)) →
                  σ / wk ↑⋆ k ∗′ ⊆ σ ∗′ // wk ↑⋆ k
  wk-∗′-commute k (σ₁ ⟶ σ₂) = begin
    σ₁ ⟶ σ₂ / wk ↑⋆ k ∗′                ≡⟨ P.refl ⟩
    σ₁ / wk ↑⋆ k ∗ ++ σ₂ / wk ↑⋆ k ∗    ⊆⟨ wk-∗-commute k σ₁ ++-mono
                                           wk-∗-commute k σ₂ ⟩
    σ₁ ∗ // wk ↑⋆ k ++ σ₂ ∗ // wk ↑⋆ k  ≡⟨ P.sym $ map-++-commute
                                             (λ σ → σ / wk ↑⋆ k) (σ₁ ∗) (σ₂ ∗) ⟩
    (σ₁ ∗ ++ σ₂ ∗) // wk ↑⋆ k           ≡⟨ P.refl ⟩
    σ₁ ⟶ σ₂ ∗′ // wk ↑⋆ k               ∎
  wk-∗′-commute k (μ σ₁ ⟶ σ₂) = begin
    (μ σ₁ ⟶ σ₂) / wk ↑⋆ k ∗′                          ≡⟨ P.refl ⟩
    σ₁ ⟶ σ₂ / wk ↑⋆ (suc k) / sub (σ / wk ↑⋆ k) ∷
      (σ₁ / wk ↑⋆ (suc k) ∗ ++ σ₂ / wk ↑⋆ (suc k) ∗)
        // sub (σ / wk ↑⋆ k)                          ⊆⟨ lem₁ ++-mono lem₂ ⟩
    σ₁ ⟶ σ₂ / sub σ / wk ↑⋆ k ∷
      (σ₁ ∗ ++ σ₂ ∗) // sub σ // wk ↑⋆ k              ≡⟨ P.refl ⟩
    μ σ₁ ⟶ σ₂ ∗′ // wk ↑⋆ k                           ∎
    where
    σ = μ σ₁ ⟶ σ₂

    lem₁ : _ ⊆ _
    lem₁ = begin
      [ σ₁ ⟶ σ₂ / wk ↑⋆ (suc k) / sub (σ / wk ↑⋆ k) ]  ≡⟨ P.cong [_] $ P.sym $
                                                            sub-commutes (σ₁ ⟶ σ₂) ⟩
      [ σ₁ ⟶ σ₂ / sub σ / wk ↑⋆ k                   ]  ∎

    lem₂ : _ ⊆ _
    lem₂ = begin
      (σ₁ / wk ↑⋆ (suc k) ∗ ++
       σ₂ / wk ↑⋆ (suc k) ∗) // sub (σ / wk ↑⋆ k)           ⊆⟨ map-mono _ (wk-∗-commute (suc k) σ₁ ++-mono
                                                                           wk-∗-commute (suc k) σ₂) ⟩
      (σ₁ ∗ // wk ↑⋆ (suc k) ++
       σ₂ ∗ // wk ↑⋆ (suc k)) // sub (σ / wk ↑⋆ k)          ≡⟨ P.cong (λ σs → σs // sub (σ / wk ↑⋆ k)) $
                                                                 P.sym $ map-++-commute
                                                                   (λ σ → σ / wk ↑⋆ suc k) (σ₁ ∗) (σ₂ ∗) ⟩
      (σ₁ ∗ ++ σ₂ ∗) // wk ↑⋆ (suc k) // sub (σ / wk ↑⋆ k)  ≡⟨ P.sym $ //.sub-commutes (σ₁ ∗ ++ σ₂ ∗) ⟩
      (σ₁ ∗ ++ σ₂ ∗) // sub σ // wk ↑⋆ k                    ∎
  wk-∗′-commute k (var x) = begin
    var x / wk ↑⋆ k ∗′     ≡⟨ P.cong _∗′ (var-/-wk-↑⋆ k x) ⟩
    var (lift k suc x) ∗′  ≡⟨ P.refl ⟩
    []                     ⊆⟨ (λ ()) ⟩
    var x ∗′ // wk ↑⋆ k    ∎
  wk-∗′-commute k ⊥ = λ ()
  wk-∗′-commute k ⊤ = λ ()

-- Substitution "commutes" with _∗.

sub-∗′-commute-var : ∀ k {n} x (τ : Ty n) →
                     var x / sub τ ↑⋆ k ∗′ ⊆ τ ∗ // wk⋆ k
sub-∗′-commute-var zero zero τ = begin
  τ ∗′             ⊆⟨ there ⟩
  τ ∗              ≡⟨ P.sym $ //.id-vanishes (τ ∗) ⟩
  τ ∗ // wk⋆ zero  ∎
sub-∗′-commute-var zero (suc x) τ = begin
  var x / idˢ ∗′   ≡⟨ P.cong _∗′ (id-vanishes (var x)) ⟩
  var x ∗′         ≡⟨ P.refl ⟩
  []               ⊆⟨ (λ ()) ⟩
  τ ∗ // wk⋆ zero  ∎
sub-∗′-commute-var (suc k) zero τ = begin
  []                  ⊆⟨ (λ ()) ⟩
  τ ∗ // wk⋆ (suc k)  ∎
sub-∗′-commute-var (suc k) (suc x) τ = begin
  var (suc x) / sub τ ↑⋆ suc k ∗′         ≡⟨ P.cong _∗′ (suc-/-↑ {ρ = sub τ ↑⋆ k} x) ⟩
  var x / sub τ ↑⋆ k / wk ∗′              ⊆⟨ wk-∗′-commute zero (var x / sub τ ↑⋆ k) ⟩
  var x / sub τ ↑⋆ k ∗′ // wk             ⊆⟨ map-mono _ (sub-∗′-commute-var k x τ) ⟩
  τ ∗ // wk⋆ k // wk                      ≡⟨ P.sym $ //./-weaken (τ ∗) ⟩
  τ ∗ // wk⋆ (suc k)                      ∎

sub-∗-commute : ∀ k {n} σ (τ : Ty n) →
                σ / sub τ ↑⋆ k ∗ ⊆ σ ∗ // sub τ ↑⋆ k ++ τ ∗ // wk⋆ k
sub-∗-commute k σ         τ     (here P.refl) = here P.refl
sub-∗-commute k ⊥         τ     •∈•           = Inverse.to ++↔ ⟨$⟩ inj₁ •∈•
sub-∗-commute k ⊤         τ     •∈•           = Inverse.to ++↔ ⟨$⟩ inj₁ •∈•
sub-∗-commute k (var x)   τ     (there •∈•)   = there $ sub-∗′-commute-var k x τ •∈•
sub-∗-commute k (σ₁ ⟶ σ₂) τ {χ} (there •∈•)   = there $
  χ                                    ∈⟨ •∈• ⟩
  (σ₁ / ρ) ∗ ++ (σ₂ / ρ) ∗             ⊆⟨ sub-∗-commute k σ₁ τ ++-mono
                                          sub-∗-commute k σ₂ τ ⟩
  (σ₁ ∗ // ρ ++ τ ∗ // wk⋆ k) ++
  (σ₂ ∗ // ρ ++ τ ∗ // wk⋆ k)          ∼⟨ ++-lemma (σ₁ ∗ // ρ) (σ₂ ∗ // ρ) ⟩
  (σ₁ ∗ // ρ ++ σ₂ ∗ // ρ) ++
  τ ∗ // wk⋆ k                         ≡⟨ P.cong₂ _++_
                                            (P.sym $ map-++-commute (λ σ → σ / ρ) (σ₁ ∗) (σ₂ ∗))
                                            P.refl ⟩
  (σ₁ ∗ ++ σ₂ ∗) // ρ ++ τ ∗ // wk⋆ k  ∎
  where ρ = sub τ ↑⋆ k
sub-∗-commute k (μ σ₁ ⟶ σ₂) τ (there (here P.refl)) =
  there $ here $ P.sym $ sub-commutes (σ₁ ⟶ σ₂)
sub-∗-commute k (μ σ₁ ⟶ σ₂) τ {χ} (there (there •∈•)) = there $ there $
  χ                                              ∈⟨ •∈• ⟩
  ((σ₁ / ρ ↑) ∗ ++ (σ₂ / ρ ↑) ∗) // sub (σ / ρ)  ⊆⟨ map-mono _ (begin
      (σ₁ / ρ ↑) ∗ ++ (σ₂ / ρ ↑) ∗                    ⊆⟨ sub-∗-commute (suc k) σ₁ τ ++-mono
                                                         sub-∗-commute (suc k) σ₂ τ ⟩
      (σ₁ ∗ // ρ ↑ ++ τ ∗ // wk⋆ (suc k)) ++
      (σ₂ ∗ // ρ ↑ ++ τ ∗ // wk⋆ (suc k))             ∼⟨ ++-lemma (σ₁ ∗ // ρ ↑) (σ₂ ∗ // ρ ↑) ⟩
      (σ₁ ∗ // ρ ↑ ++ σ₂ ∗ // ρ ↑) ++
      τ ∗ // wk⋆ (suc k)                              ≡⟨ P.cong₂ _++_
                                                           (P.sym $ map-++-commute
                                                                      (λ σ → σ / ρ ↑) (σ₁ ∗) (σ₂ ∗))
                                                           P.refl ⟩
      (σ₁ ∗ ++ σ₂ ∗) // ρ ↑ ++
      τ ∗ // wk⋆ (suc k)                              ∎) ⟩
  ((σ₁ ∗ ++ σ₂ ∗) // ρ ↑ ++
   τ ∗ // wk⋆ (suc k)) // sub (σ / ρ)            ≡⟨ map-++-commute (λ χ → χ / sub (σ / ρ))
                                                                   ((σ₁ ∗ ++ σ₂ ∗) // ρ ↑) _ ⟩
  (σ₁ ∗ ++ σ₂ ∗) // ρ ↑ // sub (σ / ρ) ++
  τ ∗ // wk⋆ (suc k) // sub (σ / ρ)              ≡⟨ P.cong₂ _++_
                                                      (P.sym $ //.sub-commutes (σ₁ ∗ ++ σ₂ ∗))
                                                      lem ⟩
  (σ₁ ∗ ++ σ₂ ∗) // sub σ // ρ ++
  τ ∗ // wk⋆ k                                   ∎
  where
  ρ = sub τ ↑⋆ k
  σ = μ σ₁ ⟶ σ₂

  lem = ≡R.begin
    τ ∗ // wk⋆ (suc k) // sub (σ / ρ)  ≡R.≡⟨ P.cong₂ _//_ (//./-weaken (τ ∗)) P.refl ⟩
    τ ∗ // wk⋆ k // wk // sub (σ / ρ)  ≡R.≡⟨ //.wk-sub-vanishes (τ ∗ // wk⋆ k) ⟩
    τ ∗ // wk⋆ k                       ≡R.∎
    where
    module ≡R = P.≡-Reasoning

-- The list contains all subterms.

complete : ∀ {n} {σ τ : Ty n} → σ ⊑ τ → σ ∈ τ ∗
complete refl                      = here P.refl
complete (⟶ˡ σ⊑τ₁)                 = there (Inverse.to ++↔                            ⟨$⟩ inj₁ (complete σ⊑τ₁))
complete (⟶ʳ σ⊑τ₂)                 = there (Inverse.to (++↔ {P = P._≡_ _} {xs = _ ∗}) ⟨$⟩ inj₂ (complete σ⊑τ₂))
complete (unfold {σ} {τ₁} {τ₂} σ⊑) =
  σ                                 ∈⟨ complete σ⊑ ⟩
  unfold[μ τ₁ ⟶ τ₂ ] ∗              ⊆⟨ sub-∗-commute zero (τ₁ ⟶ τ₂) τ ⟩
  τ₁ ⟶ τ₂ ∗ // sub τ ++ τ ∗ // idˢ  ≡⟨ P.cong (_++_ (τ₁ ⟶ τ₂ ∗ // sub τ))
                                              (//.id-vanishes (τ ∗)) ⟩
  τ ∗′ ++ τ ∗                       ⊆⟨ there {x = τ} {xs = τ ∗′} ++-mono id ⟩
  τ ∗  ++ τ ∗                       ∼⟨ ++-idempotent (τ ∗) ⟩
  τ ∗                               ∎
  where τ = μ τ₁ ⟶ τ₂

------------------------------------------------------------------------
-- A wrapper function

-- Pairs up subterms with proofs.

subtermsOf : ∀ {n} (τ : Ty n) → List (∃ λ σ → σ ⊑ τ)
subtermsOf τ = map-with-∈ (τ ∗) (-,_ ∘′ sound τ)

-- subtermsOf is complete.

subtermsOf-complete : ∀ {n} {σ τ : Ty n} →
                      σ ⊑ τ → ∃ λ σ⊑τ → (σ , σ⊑τ) ∈ subtermsOf τ
subtermsOf-complete {σ = σ} {τ} σ⊑τ =
  (-, Inverse.to (map-with-∈↔ {f = -,_ ∘′ sound τ}) ⟨$⟩
        (σ , complete σ⊑τ , P.refl))
