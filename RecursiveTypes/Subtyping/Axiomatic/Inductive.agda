------------------------------------------------------------------------
-- Inductive axiomatisation of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Axiomatic.Inductive where

open import Coinduction hiding (unfold)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Any as Any using (Any)
open Any.Membership-≡ using (_∈_)
open import Data.List.Any.Properties
open import Data.List.All as All using (All; []; _∷_)
open import Data.Product
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Inverse using (module Inverse)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

open import RecursiveTypes.Syntax
open import RecursiveTypes.Syntax.UnfoldedOrFixpoint
open import RecursiveTypes.Substitution using (unfold[μ_⟶_])
import RecursiveTypes.Subterm as ST
import RecursiveTypes.Subterm.RestrictedHypothesis as Restricted
open import RecursiveTypes.Subtyping.Semantic.Coinductive as Sem
  using (_≤Coind_)
open import RecursiveTypes.Subtyping.Axiomatic.Coinductive as Ax
  using (_≤_; ⊥; ⊤; _⟶_; unfold; fold; _∎; _≤⟨_⟩_)

------------------------------------------------------------------------
-- Definition

infixr 10 _⟶_
infix  4  _⊢_≤_
infixr 2  _≤⟨_⟩_
infix  2  _∎

-- This inductive subtyping relation is parameterised on a list of
-- hypotheses. Note Brandt and Henglein's unusual definition of _⟶_.

data _⊢_≤_ {n} (A : List (Hyp n)) : Ty n → Ty n → Set where
  -- Structural rules.
  ⊥   : ∀ {τ} → A ⊢ ⊥ ≤ τ
  ⊤   : ∀ {σ} → A ⊢ σ ≤ ⊤
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂} →
        let H = σ₁ ⟶ σ₂ ≲ τ₁ ⟶ τ₂ in
        (τ₁≤σ₁ : H ∷ A ⊢ τ₁ ≤ σ₁) (σ₂≤τ₂ : H ∷ A ⊢ σ₂ ≤ τ₂) →
        A ⊢ σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂

  -- Rules for folding and unfolding μ.
  unfold : ∀ {τ₁ τ₂} → A ⊢ μ τ₁ ⟶ τ₂ ≤ unfold[μ τ₁ ⟶ τ₂ ]
  fold   : ∀ {τ₁ τ₂} → A ⊢ unfold[μ τ₁ ⟶ τ₂ ] ≤ μ τ₁ ⟶ τ₂

  -- Reflexivity.
  _∎ : ∀ τ → A ⊢ τ ≤ τ

  -- Transitivity.
  _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
           (τ₁≤τ₂ : A ⊢ τ₁ ≤ τ₂) (τ₂≤τ₃ : A ⊢ τ₂ ≤ τ₃) → A ⊢ τ₁ ≤ τ₃

  -- Hypothesis.
  hyp : ∀ {σ τ} (σ≤τ : (σ ≲ τ) ∈ A) → A ⊢ σ ≤ τ

------------------------------------------------------------------------
-- Soundness

-- A hypothesis is valid if there is a corresponding proof.

Valid : ∀ {n} → (Ty n → Ty n → Set) → Hyp n → Set
Valid _≤_ (σ₁ ≲ σ₂) = σ₁ ≤ σ₂

module Soundness where

  -- The soundness proof uses my trick to show that the code is
  -- productive.

  infix 4 _≤P_ _≤W_

  mutual

    -- Soundness proof programs.

    data _≤P_ {n} : Ty n → Ty n → Set where
      sound : ∀ {A σ τ} →
              (valid : All (Valid _≤W_) A) (σ≤τ : A ⊢ σ ≤ τ) → σ ≤P τ

    -- Weak head normal forms of soundness proof programs. Note that
    -- _⟶_ takes (suspended) /programs/ as arguments, while _≤⟨_⟩_
    -- takes /WHNFs/.

    data _≤W_ {n} : Ty n → Ty n → Set where
      done   : ∀ {σ τ} (σ≤τ : σ ≤ τ) → σ ≤W τ
      _⟶_    : ∀ {σ₁ σ₂ τ₁ τ₂}
               (τ₁≤σ₁ : ∞ (τ₁ ≤P σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤P τ₂)) →
               σ₁ ⟶ σ₂ ≤W τ₁ ⟶ τ₂
      _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
               (τ₁≤τ₂ : τ₁ ≤W τ₂) (τ₂≤τ₃ : τ₂ ≤W τ₃) → τ₁ ≤W τ₃

  -- The following two functions compute the WHNF of a soundness
  -- program. Note the circular, but productive, definition of proof
  -- below.

  soundW : ∀ {n} {σ τ : Ty n} {A} →
           All (Valid _≤W_) A → A ⊢ σ ≤ τ → σ ≤W τ
  soundW valid ⊥                     = done ⊥
  soundW valid ⊤                     = done ⊤
  soundW valid unfold                = done unfold
  soundW valid fold                  = done fold
  soundW valid (τ ∎)                 = done (τ ∎)
  soundW valid (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ soundW valid τ₁≤τ₂ ⟩
                                             soundW valid τ₂≤τ₃
  soundW valid (hyp σ≤τ)             = All.lookup valid σ≤τ
  soundW valid (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = proof
    where
    proof : _ ≤W _
    proof = ♯ sound (proof ∷ valid) τ₁≤σ₁ ⟶
            ♯ sound (proof ∷ valid) σ₂≤τ₂

  whnf : ∀ {n} {σ τ : Ty n} →
         σ ≤P τ → σ ≤W τ
  whnf (sound valid σ≤τ) = soundW valid σ≤τ

  -- Computes actual proofs.

  mutual

    ⟦_⟧W : ∀ {n} {σ τ : Ty n} → σ ≤W τ → σ ≤ τ
    ⟦ done σ≤τ            ⟧W = σ≤τ
    ⟦ τ₁≤σ₁ ⟶ σ₂≤τ₂       ⟧W = ♯ ⟦ ♭ τ₁≤σ₁ ⟧P ⟶ ♯ ⟦ ♭ σ₂≤τ₂ ⟧P
    ⟦ τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃ ⟧W = τ₁ ≤⟨ ⟦ τ₁≤τ₂ ⟧W ⟩ ⟦ τ₂≤τ₃ ⟧W

    ⟦_⟧P : ∀ {n} {σ τ : Ty n} → σ ≤P τ → σ ≤ τ
    ⟦ σ≤τ ⟧P = ⟦ whnf σ≤τ ⟧W

-- The subtyping relation defined above is sound with respect to the
-- others.

sound : ∀ {n A} {σ τ : Ty n} →
        All (Valid _≤_) A → A ⊢ σ ≤ τ → σ ≤ τ
sound {n} valid σ≤τ =
  ⟦ S.sound (All.map (λ {h} → done′ h) valid) σ≤τ ⟧P
  where
  open module S = Soundness

  done′ : (σ₁≲σ₂ : Hyp n) → Valid _≤_ σ₁≲σ₂ → Valid _≤W_ σ₁≲σ₂
  done′ (_ ≲ _) = done

------------------------------------------------------------------------
-- The subtyping relation is decidable

module Decidable {n} (χ₁ χ₂ : Ty n) where

  open Restricted χ₁ χ₂

  -- The proof below is not optimised for speed. (See Gapeyev, Levin
  -- and Pierce's "Recursive Subtyping Revealed" from ICFP '00 for
  -- more information about the complexity of subtyping algorithms.)

  mutual

    -- A wrapper which applies the U∨Μ view.

    _⊢_,_≤?_,_ : ∀ {A ℓ} → A ⊕ ℓ →
                 ∀ σ → Subterm σ → ∀ τ → Subterm τ →
                 ⟨ A ⟩⋆ ⊢ σ ≤ τ ⊎ (¬ σ ≤Coind τ)
    T ⊢ σ , σ⊑ ≤? τ , τ⊑ = T ⊩ u∨μ σ , σ⊑ ≤? u∨μ τ , τ⊑

    -- _⊩_,_≤?_,_ unfolds fixpoints. Note that at least one U∨Μ
    -- argument becomes smaller in each recursive call, while ℓ, an
    -- upper bound on the number of pairs of types yet to be
    -- inspected, is preserved.

    _⊩_,_≤?_,_ : ∀ {A ℓ} → A ⊕ ℓ →
                 ∀ {σ τ} → U∨Μ σ → Subterm σ → U∨Μ τ → Subterm τ →
                 ⟨ A ⟩⋆ ⊢ σ ≤ τ ⊎ (¬ σ ≤Coind τ)

    T ⊩ fixpoint {σ₁} {σ₂} u , σ⊑ ≤? τ , τ⊑ =
      Sum.map (λ ≤τ → μ σ₁ ⟶ σ₂           ≤⟨ unfold ⟩
                      unfold[μ σ₁ ⟶ σ₂ ]  ≤⟨ ≤τ ⟩
                      u∨μ⁻¹ τ             ∎)
              (λ ≰τ ≤τ → ≰τ (Sem.trans Sem.fold ≤τ))
              (T ⊩ u , anti-mono ST.unfold′ σ⊑ ≤? τ , τ⊑)
    T ⊩ σ , σ⊑ ≤? fixpoint {τ₁} {τ₂} u , τ⊑ =
      Sum.map (λ σ≤ → u∨μ⁻¹ σ             ≤⟨ σ≤ ⟩
                      unfold[μ τ₁ ⟶ τ₂ ]  ≤⟨ fold ⟩
                      μ τ₁ ⟶ τ₂           ∎)
              (λ σ≰ σ≤ → σ≰ (Sem.trans σ≤ Sem.unfold))
              (T ⊩ σ , σ⊑ ≤? u , anti-mono ST.unfold′ τ⊑)

    T ⊩ unfolded σ , σ⊑ ≤? unfolded τ , τ⊑ = T ⊪ σ , σ⊑ ≤? τ , τ⊑

    -- _⊪_,_≤?_,_ handles the structural cases. Note that ℓ becomes
    -- smaller in each recursive call.

    _⊪_,_≤?_,_ : ∀ {A ℓ} → A ⊕ ℓ →
                 ∀ {σ} → Unfolded σ → Subterm σ →
                 ∀ {τ} → Unfolded τ → Subterm τ →
                 ⟨ A ⟩⋆ ⊢ σ ≤ τ ⊎ (¬ σ ≤Coind τ)
    T ⊪ ⊥ , _ ≤? τ , _ = inj₁ ⊥
    T ⊪ σ , _ ≤? ⊤ , _ = inj₁ ⊤

    T ⊪ var x , _ ≤? var y , _ = helper (var x ≡? var y)
      where
      helper : ∀ {A x y} → Dec ((var x ∶ Ty n) ≡ var y) →
               ⟨ A ⟩⋆ ⊢ var x ≤ var y ⊎ ¬ var x ≤Coind var y
      helper (yes refl) = inj₁ (var _ ∎)
      helper (no  x≠y)  = inj₂ (x≠y ∘ Sem.var:≤∞⟶≡)

    _⊪_,_≤?_,_ {A} T (σ₁ ⟶ σ₂) σ⊑ (τ₁ ⟶ τ₂) τ⊑ =
      helper (lookupOrInsert T H)
      where
      H = (, σ⊑) ≲ (, τ⊑)

      helper₂ :
        ⟨ H ∷ A ⟩⋆ ⊢ τ₁      ≤ σ₁      ⊎ ¬ τ₁      ≤Coind σ₁      →
        ⟨ H ∷ A ⟩⋆ ⊢      σ₂ ≤      τ₂ ⊎ ¬      σ₂ ≤Coind      τ₂ →
        ⟨     A ⟩⋆ ⊢ σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂ ⊎ ¬ σ₁ ⟶ σ₂ ≤Coind τ₁ ⟶ τ₂
      helper₂ (inj₁ ≤₁) (inj₁ ≤₂) = inj₁ (≤₁ ⟶ ≤₂)
      helper₂ (inj₂ ≰ ) (_      ) = inj₂ (≰ ∘  Sem.left-proj)
      helper₂ (_      ) (inj₂ ≰ ) = inj₂ (≰ ∘ Sem.right-proj)

      helper : ∀ {ℓ} → Any (_≈_ H) A ⊎ (∃ λ n → ℓ ≡ suc n × H ∷ A ⊕ n) →
               ⟨ A ⟩⋆ ⊢ σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂ ⊎ ¬ σ₁ ⟶ σ₂ ≤Coind τ₁ ⟶ τ₂
      helper (inj₁ σ≲τ)             = inj₁ $ hyp $ Inverse.to map↔ ⟨$⟩ σ≲τ
      helper (inj₂ (_ , refl , T′)) = helper₂
        (T′ ⊢ τ₁ , anti-mono ST.⟶ˡ′ τ⊑ ≤? σ₁ , anti-mono ST.⟶ˡ′ σ⊑)
        (T′ ⊢ σ₂ , anti-mono ST.⟶ʳ′ σ⊑ ≤? τ₂ , anti-mono ST.⟶ʳ′ τ⊑)

    T ⊪ ⊤       , _ ≤? ⊥       , _ = inj₂ (λ ())
    T ⊪ ⊤       , _ ≤? var x   , _ = inj₂ (λ ())
    T ⊪ ⊤       , _ ≤? τ₁ ⟶ τ₂ , _ = inj₂ (λ ())
    T ⊪ var x   , _ ≤? ⊥       , _ = inj₂ (λ ())
    T ⊪ var x   , _ ≤? τ₁ ⟶ τ₂ , _ = inj₂ (λ ())
    T ⊪ σ₁ ⟶ σ₂ , _ ≤? ⊥       , _ = inj₂ (λ ())
    T ⊪ σ₁ ⟶ σ₂ , _ ≤? var x   , _ = inj₂ (λ ())

  -- Finally we have to prove that an upper bound ℓ actually exists.

  dec : [] ⊢ χ₁ ≤ χ₂ ⊎ (¬ χ₁ ≤ χ₂)
  dec = Sum.map id (λ σ≰τ → σ≰τ ∘ Ax.sound) $
        empty ⊢ χ₁ , inj₁ ST.refl ≤? χ₂ , inj₂ ST.refl

infix 4 []⊢_≤?_ _≤?_

-- The subtyping relation defined above is decidable (when the set of
-- assumptions is empty).

[]⊢_≤?_ : ∀ {n} (σ τ : Ty n) → Dec ([] ⊢ σ ≤ τ)
[]⊢ σ ≤? τ with Decidable.dec σ τ
... | inj₁ σ≤τ = yes σ≤τ
... | inj₂ σ≰τ = no (σ≰τ ∘ sound [])

-- The other subtyping relations can also be decided.

_≤?_ : ∀ {n} (σ τ : Ty n) → Dec (σ ≤ τ)
σ ≤? τ with Decidable.dec σ τ
... | inj₁ σ≤τ = yes (sound [] σ≤τ)
... | inj₂ σ≰τ = no σ≰τ

------------------------------------------------------------------------
-- Completeness

-- Weakening (at the end of the list of assumptions).

weaken : ∀ {n A A′} {σ τ : Ty n} →
         A ⊢ σ ≤ τ → A ++ A′ ⊢ σ ≤ τ
weaken ⊥                     = ⊥
weaken ⊤                     = ⊤
weaken unfold                = unfold
weaken fold                  = fold
weaken (τ ∎)                 = τ ∎
weaken (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ weaken τ₁≤τ₂ ⟩ weaken τ₂≤τ₃
weaken (hyp h)               = hyp (Inverse.to ++↔ ⟨$⟩ inj₁ h)
weaken (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = weaken τ₁≤σ₁ ⟶ weaken σ₂≤τ₂

-- The subtyping relation defined above is complete with respect to
-- the others.

complete : ∀ {n A} {σ τ : Ty n} →
           σ ≤ τ → A ⊢ σ ≤ τ
complete {σ = σ} {τ} σ≤τ with Decidable.dec σ τ
... | inj₁ []⊢σ≤τ = weaken []⊢σ≤τ
... | inj₂ σ≰τ    with σ≰τ σ≤τ
...   | ()
