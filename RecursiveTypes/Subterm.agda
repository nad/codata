------------------------------------------------------------------------
-- Brandt and Henglein's subterm relation
------------------------------------------------------------------------

module RecursiveTypes.Subterm where

open import Data.Fin using (Fin; zero; suc; lift)
open import Data.Nat
open import Data.List using (List; []; _∷_; [_]; _++_)
open import Data.List.Properties
open import Data.List.Any
open Membership-≡
open import Data.List.Any.Properties as AnyProp
open AnyProp.Membership-≡
open import Data.Product
open import Data.Sum
open import Data.Function
open import Relation.Binary.PropositionalEquality hiding (trans)
open import Data.Fin.Substitution

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
  unfold : ∀ {σ τ₁ τ₂} (σ⊑ : σ ⊑ unfold[ν τ₁ ⟶ τ₂ ]) → σ ⊑ ν τ₁ ⟶ τ₂
  ⟶ˡ     : ∀ {σ τ₁ τ₂} (σ⊑τ₁ : σ ⊑ τ₁) → σ ⊑ τ₁ ⟶ τ₂
  ⟶ʳ     : ∀ {σ τ₁ τ₂} (σ⊑τ₂ : σ ⊑ τ₂) → σ ⊑ τ₁ ⟶ τ₂

-- Some simple consequences.

unfold′ : ∀ {n} {τ₁ τ₂ : Ty (suc n)} →
          unfold[ν τ₁ ⟶ τ₂ ] ⊑ ν τ₁ ⟶ τ₂
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
  (ν τ₁ ⟶ τ₂) ∗′ = (τ₁ ⟶ τ₂ ∷ τ₁ ∗ ++ τ₂ ∗) // sub (ν τ₁ ⟶ τ₂)
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
  unfold $ subst (λ χ → σ / ρ ⊑ χ)
                 (sub-commutes (τ₁ ⟶ τ₂))
                 (/-monoˡ σ⊑)

sub-⊑-ν : ∀ {n} {σ : Ty (suc n)} {τ₁ τ₂} →
          σ ⊑ τ₁ ⟶ τ₂ → σ / sub (ν τ₁ ⟶ τ₂) ⊑ ν τ₁ ⟶ τ₂
sub-⊑-ν σ⊑τ₁⟶τ₂ = unfold (/-monoˡ σ⊑τ₁⟶τ₂)

-- All list elements are subterms.

sound : ∀ {n σ} (τ : Ty n) → σ ∈ τ ∗ → σ ⊑ τ
sound τ         (here refl) = refl
sound (τ₁ ⟶ τ₂) (there σ∈)  =
  [ ⟶ˡ ∘ sound τ₁ , ⟶ʳ ∘ sound τ₂ ]′ (++⁻ (τ₁ ∗) σ∈)
sound (ν τ₁ ⟶ τ₂) (there (here refl)) = unfold refl
sound (ν τ₁ ⟶ τ₂) (there (there σ∈))  with map-∈⁻ (τ₁ ∗ ++ τ₂ ∗) σ∈
... | (χ , χ∈ , refl) =
  sub-⊑-ν $ [ ⟶ˡ ∘ sound τ₁ , ⟶ʳ ∘ sound τ₂ ]′ (++⁻ (τ₁ ∗) χ∈)
sound ⊥       (there ())
sound ⊤       (there ())
sound (var x) (there ())

------------------------------------------------------------------------
-- Completeness

open ⊆-Reasoning

++-lemma : ∀ {A} xs ys {zs : List A} →
           (xs ++ zs) ++ (ys ++ zs) ⊆ (xs ++ ys) ++ zs
++-lemma xs ys {zs} x∈ with ++⁻ (xs ++ zs) x∈
++-lemma xs ys {zs} x∈ | inj₁ x∈ˡ with ++⁻ xs x∈ˡ
... | inj₁ x∈xs = ++⁺ˡ (++⁺ˡ x∈xs)
... | inj₂ x∈zs = ++⁺ʳ (xs ++ ys) x∈zs
++-lemma xs ys {zs} x∈ | inj₂ x∈ʳ with ++⁻ ys x∈ʳ
... | inj₁ x∈ys = ++⁺ˡ (++⁺ʳ xs x∈ys)
... | inj₂ x∈zs = ++⁺ʳ (xs ++ ys) x∈zs

mutual

  -- Weakening "commutes" with _∗.

  wk-∗-commute : ∀ k {n} (σ : Ty (k + n)) →
                 σ / wk ↑⋆ k ∗ ⊆ σ ∗ // wk ↑⋆ k
  wk-∗-commute k σ (here refl) = here refl
  wk-∗-commute k σ (there •∈•) = there $ wk-∗′-commute k σ •∈•

  wk-∗′-commute : ∀ k {n} (σ : Ty (k + n)) →
                  σ / wk ↑⋆ k ∗′ ⊆ σ ∗′ // wk ↑⋆ k
  wk-∗′-commute k (σ₁ ⟶ σ₂) = begin
    σ₁ ⟶ σ₂ / wk ↑⋆ k ∗′                ≡⟨ refl ⟩
    σ₁ / wk ↑⋆ k ∗ ++ σ₂ / wk ↑⋆ k ∗    ⊆⟨ wk-∗-commute k σ₁ ++-mono
                                           wk-∗-commute k σ₂ ⟩
    σ₁ ∗ // wk ↑⋆ k ++ σ₂ ∗ // wk ↑⋆ k  ≡⟨ sym $ map-++-commute
                                             (λ σ → σ / wk ↑⋆ k) (σ₁ ∗) (σ₂ ∗) ⟩
    (σ₁ ∗ ++ σ₂ ∗) // wk ↑⋆ k           ≡⟨ refl ⟩
    σ₁ ⟶ σ₂ ∗′ // wk ↑⋆ k               ∎
  wk-∗′-commute k (ν σ₁ ⟶ σ₂) = begin
    (ν σ₁ ⟶ σ₂) / wk ↑⋆ k ∗′                          ≡⟨ refl ⟩
    σ₁ ⟶ σ₂ / wk ↑⋆ (suc k) / sub (σ / wk ↑⋆ k) ∷
      (σ₁ / wk ↑⋆ (suc k) ∗ ++ σ₂ / wk ↑⋆ (suc k) ∗)
        // sub (σ / wk ↑⋆ k)                          ⊆⟨ lem₁ ++-mono lem₂ ⟩
    σ₁ ⟶ σ₂ / sub σ / wk ↑⋆ k ∷
      (σ₁ ∗ ++ σ₂ ∗) // sub σ // wk ↑⋆ k              ≡⟨ refl ⟩
    ν σ₁ ⟶ σ₂ ∗′ // wk ↑⋆ k                           ∎
    where
    σ = ν σ₁ ⟶ σ₂

    lem₁ : _ ⊆ _
    lem₁ = begin
      [ σ₁ ⟶ σ₂ / wk ↑⋆ (suc k) / sub (σ / wk ↑⋆ k) ]  ≡⟨ cong [_] $ sym $
                                                            sub-commutes (σ₁ ⟶ σ₂) ⟩
      [ σ₁ ⟶ σ₂ / sub σ / wk ↑⋆ k                   ]  ∎

    lem₂ : _ ⊆ _
    lem₂ = begin
      (σ₁ / wk ↑⋆ (suc k) ∗ ++
       σ₂ / wk ↑⋆ (suc k) ∗) // sub (σ / wk ↑⋆ k)           ⊆⟨ map-mono $ wk-∗-commute (suc k) σ₁ ++-mono
                                                                          wk-∗-commute (suc k) σ₂ ⟩
      (σ₁ ∗ // wk ↑⋆ (suc k) ++
       σ₂ ∗ // wk ↑⋆ (suc k)) // sub (σ / wk ↑⋆ k)          ≡⟨ cong (λ σs → σs // sub (σ / wk ↑⋆ k)) $
                                                                 sym $ map-++-commute
                                                                   (λ σ → σ / wk ↑⋆ suc k) (σ₁ ∗) (σ₂ ∗) ⟩
      (σ₁ ∗ ++ σ₂ ∗) // wk ↑⋆ (suc k) // sub (σ / wk ↑⋆ k)  ≡⟨ sym $ //.sub-commutes (σ₁ ∗ ++ σ₂ ∗) ⟩
      (σ₁ ∗ ++ σ₂ ∗) // sub σ // wk ↑⋆ k                    ∎
  wk-∗′-commute k (var x) = begin
    var x / wk ↑⋆ k ∗′     ≡⟨ cong _∗′ (var-/-wk-↑⋆ k x) ⟩
    var (lift k suc x) ∗′  ≡⟨ refl ⟩
    []                     ⊆⟨ (λ ()) ⟩
    var x ∗′ // wk ↑⋆ k    ∎
  wk-∗′-commute k ⊥ = λ ()
  wk-∗′-commute k ⊤ = λ ()

-- Substitution "commutes" with _∗.

sub-∗′-commute-var : ∀ k {n} x (τ : Ty n) →
                     var x / sub τ ↑⋆ k ∗′ ⊆ τ ∗ // wk⋆ k
sub-∗′-commute-var zero zero τ = begin
  τ ∗′             ⊆⟨ there ⟩
  τ ∗              ≡⟨ sym $ //.id-vanishes (τ ∗) ⟩
  τ ∗ // wk⋆ zero  ∎
sub-∗′-commute-var zero (suc x) τ = begin
  var x / idˢ ∗′   ≡⟨ cong _∗′ (id-vanishes (var x)) ⟩
  var x ∗′         ≡⟨ refl ⟩
  []               ⊆⟨ (λ ()) ⟩
  τ ∗ // wk⋆ zero  ∎
sub-∗′-commute-var (suc k) zero τ = begin
  []                  ⊆⟨ (λ ()) ⟩
  τ ∗ // wk⋆ (suc k)  ∎
sub-∗′-commute-var (suc k) (suc x) τ = begin
  var (suc x) / sub τ ↑⋆ suc k ∗′         ≡⟨ cong _∗′ (suc-/-↑ x) ⟩
  var x / sub τ ↑⋆ k / wk ∗′              ⊆⟨ wk-∗′-commute zero (var x / sub τ ↑⋆ k) ⟩
  var x / sub τ ↑⋆ k ∗′ // wk             ⊆⟨ map-mono (sub-∗′-commute-var k x τ) ⟩
  τ ∗ // wk⋆ k // wk                      ≡⟨ sym $ //./-weaken (τ ∗) ⟩
  τ ∗ // wk⋆ (suc k)                      ∎

sub-∗-commute : ∀ k {n} σ (τ : Ty n) →
                σ / sub τ ↑⋆ k ∗ ⊆ σ ∗ // sub τ ↑⋆ k ++ τ ∗ // wk⋆ k
sub-∗-commute k σ         τ     (here refl) = here refl
sub-∗-commute k ⊥         τ     •∈•         = ++⁺ˡ •∈•
sub-∗-commute k ⊤         τ     •∈•         = ++⁺ˡ •∈•
sub-∗-commute k (var x)   τ     (there •∈•) = there $ sub-∗′-commute-var k x τ •∈•
sub-∗-commute k (σ₁ ⟶ σ₂) τ {χ} (there •∈•) = there $
  χ                                    ∈⟨ •∈• ⟩
  (σ₁ / ρ) ∗ ++ (σ₂ / ρ) ∗             ⊆⟨ sub-∗-commute k σ₁ τ ++-mono
                                          sub-∗-commute k σ₂ τ ⟩
  (σ₁ ∗ // ρ ++ τ ∗ // wk⋆ k) ++
  (σ₂ ∗ // ρ ++ τ ∗ // wk⋆ k)          ⊆⟨ ++-lemma (σ₁ ∗ // ρ) (σ₂ ∗ // ρ) ⟩
  (σ₁ ∗ // ρ ++ σ₂ ∗ // ρ) ++
  τ ∗ // wk⋆ k                         ≡⟨ cong₂ _++_
                                            (sym $ map-++-commute (λ σ → σ / ρ) (σ₁ ∗) (σ₂ ∗))
                                            refl ⟩
  (σ₁ ∗ ++ σ₂ ∗) // ρ ++ τ ∗ // wk⋆ k  ∎
  where ρ = sub τ ↑⋆ k
sub-∗-commute k (ν σ₁ ⟶ σ₂) τ (there (here refl)) =
  there $ here $ sym $ sub-commutes (σ₁ ⟶ σ₂)
sub-∗-commute k (ν σ₁ ⟶ σ₂) τ {χ} (there (there •∈•)) = there $ there $
  χ                                              ∈⟨ •∈• ⟩
  ((σ₁ / ρ ↑) ∗ ++ (σ₂ / ρ ↑) ∗) // sub (σ / ρ)  ⊆⟨ map-mono (begin
      (σ₁ / ρ ↑) ∗ ++ (σ₂ / ρ ↑) ∗                    ⊆⟨ sub-∗-commute (suc k) σ₁ τ ++-mono
                                                         sub-∗-commute (suc k) σ₂ τ ⟩
      (σ₁ ∗ // ρ ↑ ++ τ ∗ // wk⋆ (suc k)) ++
      (σ₂ ∗ // ρ ↑ ++ τ ∗ // wk⋆ (suc k))             ⊆⟨ ++-lemma (σ₁ ∗ // ρ ↑) (σ₂ ∗ // ρ ↑) ⟩
      (σ₁ ∗ // ρ ↑ ++ σ₂ ∗ // ρ ↑) ++
      τ ∗ // wk⋆ (suc k)                              ≡⟨ cong₂ _++_
                                                           (sym $ map-++-commute
                                                                    (λ σ → σ / ρ ↑) (σ₁ ∗) (σ₂ ∗))
                                                           refl ⟩
      (σ₁ ∗ ++ σ₂ ∗) // ρ ↑ ++
      τ ∗ // wk⋆ (suc k)                              ∎) ⟩
  ((σ₁ ∗ ++ σ₂ ∗) // ρ ↑ ++
   τ ∗ // wk⋆ (suc k)) // sub (σ / ρ)            ≡⟨ map-++-commute (λ χ → χ / sub (σ / ρ))
                                                                   ((σ₁ ∗ ++ σ₂ ∗) // ρ ↑) _ ⟩
  (σ₁ ∗ ++ σ₂ ∗) // ρ ↑ // sub (σ / ρ) ++
  τ ∗ // wk⋆ (suc k) // sub (σ / ρ)              ≡⟨ cong₂ _++_
                                                      (sym $ //.sub-commutes (σ₁ ∗ ++ σ₂ ∗))
                                                      lem ⟩
  (σ₁ ∗ ++ σ₂ ∗) // sub σ // ρ ++
  τ ∗ // wk⋆ k                                   ∎
  where
  ρ = sub τ ↑⋆ k
  σ = ν σ₁ ⟶ σ₂

  lem = begin′
    τ ∗ // wk⋆ (suc k) // sub (σ / ρ)  ≡⟨ cong₂ _//_ (//./-weaken (τ ∗)) refl ⟩′
    τ ∗ // wk⋆ k // wk // sub (σ / ρ)  ≡⟨ //.wk-sub-vanishes (τ ∗ // wk⋆ k) ⟩′
    τ ∗ // wk⋆ k                       ∎′
    where open ≡-Reasoning
            renaming (begin_ to begin′_; _≡⟨_⟩_ to _≡⟨_⟩′_; _∎ to _∎′)

-- The list contains all subterms.

complete : ∀ {n} {σ τ : Ty n} → σ ⊑ τ → σ ∈ τ ∗
complete refl                      = here refl
complete (⟶ˡ σ⊑τ₁)                 = there (++⁺ˡ       (complete σ⊑τ₁))
complete (⟶ʳ σ⊑τ₂)                 = there (++⁺ʳ (_ ∗) (complete σ⊑τ₂))
complete (unfold {σ} {τ₁} {τ₂} σ⊑) =
  σ                                 ∈⟨ complete σ⊑ ⟩
  unfold[ν τ₁ ⟶ τ₂ ] ∗              ⊆⟨ sub-∗-commute zero (τ₁ ⟶ τ₂) τ ⟩
  τ₁ ⟶ τ₂ ∗ // sub τ ++ τ ∗ // idˢ  ≡⟨ cong (_++_ (τ₁ ⟶ τ₂ ∗ // sub τ))
                                            (//.id-vanishes (τ ∗)) ⟩
  τ ∗′ ++ τ ∗                       ⊆⟨ there {x = τ} {xs = τ ∗′} ++-mono id ⟩
  τ ∗  ++ τ ∗                       ⊆⟨ ++-idempotent ⟩
  τ ∗                               ∎
  where τ = ν τ₁ ⟶ τ₂
