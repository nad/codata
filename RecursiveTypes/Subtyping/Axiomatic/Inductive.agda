------------------------------------------------------------------------
-- Inductive axiomatisation of subtyping
------------------------------------------------------------------------

module RecursiveTypes.Subtyping.Axiomatic.Inductive where

open import Coinduction
open import Data.Empty using (⊥-elim)
open import Data.Function
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _++_)
import Data.List.Any as Any
open Any.Membership-≡ using (_∈_)
import Data.List.Any.Properties as AnyP
open import Data.List.All as All using (All; []; _∷_)
open import Data.Product
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary
open import Relation.Unary using (Pred)
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
--
-- This definition is lazy in order to simplify the definition of
-- sound below.

Valid : ∀ {n} → (Ty n → Ty n → Set) → Pred (Hyp n)
Valid _≤_ σ₁≲σ₂ = proj₁ σ₁≲σ₂ ≤ proj₂ σ₁≲σ₂

module Soundness where

  -- The soundness proof uses my trick to show that the code is
  -- productive.

  infix 4 _≤Prog_ _≤WHNF_

  mutual

    -- Soundness proof programs.

    data _≤Prog_ {n} : Ty n → Ty n → Set where
      sound : ∀ {A σ τ} →
              (valid : All (Valid _≤WHNF_) A) (σ≤τ : A ⊢ σ ≤ τ) →
              σ ≤Prog τ

    -- Weak head normal forms of soundness proof programs. Note that
    -- _⟶_ takes (suspended) /programs/ as arguments, while _≤⟨_⟩_
    -- takes /WHNFs/.

    data _≤WHNF_ {n} : Ty n → Ty n → Set where
      done   : ∀ {σ τ} (σ≤τ : σ ≤ τ) → σ ≤WHNF τ
      _⟶_    : ∀ {σ₁ σ₂ τ₁ τ₂}
               (τ₁≤σ₁ : ∞ (τ₁ ≤Prog σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤Prog τ₂)) →
               σ₁ ⟶ σ₂ ≤WHNF τ₁ ⟶ τ₂
      _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃}
               (τ₁≤τ₂ : τ₁ ≤WHNF τ₂) (τ₂≤τ₃ : τ₂ ≤WHNF τ₃) → τ₁ ≤WHNF τ₃

  -- Computes the WHNF of a soundness program. Note the circular, but
  -- productive, definition of proof below.

  whnf : ∀ {n} {σ τ : Ty n} →
         σ ≤Prog τ → σ ≤WHNF τ
  whnf (sound {A} valid σ≤τ) = w-s σ≤τ
    where
    w-s : ∀ {σ τ} → A ⊢ σ ≤ τ → σ ≤WHNF τ
    w-s ⊥                     = done ⊥
    w-s ⊤                     = done ⊤
    w-s unfold                = done unfold
    w-s fold                  = done fold
    w-s (τ ∎)                 = done (τ ∎)
    w-s (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ w-s τ₁≤τ₂ ⟩ w-s τ₂≤τ₃
    w-s (hyp σ≤τ)             = All.lookup valid σ≤τ
    w-s (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = proof
      where proof = ♯ sound (proof ∷ valid) τ₁≤σ₁ ⟶
                    ♯ sound (proof ∷ valid) σ₂≤τ₂

  -- Computes actual proofs.

  mutual

    value : ∀ {n} {σ τ : Ty n} →
            σ ≤WHNF τ → σ ≤ τ
    value (done σ≤τ)            = σ≤τ
    value (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = ♯ ⟦ ♭ τ₁≤σ₁ ⟧≤ ⟶ ♯ ⟦ ♭ σ₂≤τ₂ ⟧≤
    value (τ₁ ≤⟨ τ₁≤τ₂ ⟩ τ₂≤τ₃) = τ₁ ≤⟨ value τ₁≤τ₂ ⟩ value τ₂≤τ₃

    ⟦_⟧≤ : ∀ {n} {σ τ : Ty n} →
           σ ≤Prog τ → σ ≤ τ
    ⟦ σ≤τ ⟧≤ = value (whnf σ≤τ)

-- The subtyping relation defined above is sound with respect to the
-- others.

sound : ∀ {n A} {σ τ : Ty n} →
        A ⊢ σ ≤ τ → All (Valid _≤_) A → σ ≤ τ
sound σ≤τ valid = ⟦ S.sound (All.map done valid) σ≤τ ⟧≤
  where open module S = Soundness

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

    -- _,_⊪_,_≤?_,_ handles the structural cases. Note that ℓ becomes
    -- smaller in each recursive call.

    _⊪_,_≤?_,_ : ∀ {A ℓ} → A ⊕ ℓ →
                 ∀ {σ} → Unfolded σ → Subterm σ →
                 ∀ {τ} → Unfolded τ → Subterm τ →
                 ⟨ A ⟩⋆ ⊢ σ ≤ τ ⊎ (¬ σ ≤Coind τ)
    T ⊪ ⊥ , _ ≤? τ , _ = inj₁ ⊥
    T ⊪ σ , _ ≤? ⊤ , _ = inj₁ ⊤

    T ⊪ var x , _ ≤? var  y , _ with var x ≡? var y
    T ⊪ var x , _ ≤? var .x , _ | yes refl = inj₁ (var x ∎)
    T ⊪ var x , _ ≤? var  y , _ | no  x≠y  = inj₂ (x≠y ∘ Sem.var:≤∞⟶≡)

    T ⊪ σ₁ ⟶ σ₂ , σ⊑ ≤? τ₁ ⟶ τ₂ , τ⊑
      with lookupOrInsert T ((, σ⊑) ≲ (, τ⊑))
    ... | inj₁ σ≲τ = inj₁ $ hyp $ AnyP.map⁺ σ≲τ
    ... | inj₂ (_ , refl , T′)
          with T′ ⊢ τ₁ , anti-mono ST.⟶ˡ′ τ⊑ ≤? σ₁ , anti-mono ST.⟶ˡ′ σ⊑
             | T′ ⊢ σ₂ , anti-mono ST.⟶ʳ′ σ⊑ ≤? τ₂ , anti-mono ST.⟶ʳ′ τ⊑
    ...   | inj₁ ≤₁ | inj₁ ≤₂ = inj₁ (≤₁ ⟶ ≤₂)
    ...   | inj₂ ≰  | _       = inj₂ (≰ ∘  Sem.left-proj)
    ...   | _       | inj₂ ≰  = inj₂ (≰ ∘ Sem.right-proj)

    T ⊪ ⊤       , _ ≤? ⊥       , _ = inj₂ (λ ())
    T ⊪ ⊤       , _ ≤? var x   , _ = inj₂ (λ ())
    T ⊪ ⊤       , _ ≤? τ₁ ⟶ τ₂ , _ = inj₂ (λ ())
    T ⊪ var x   , _ ≤? ⊥       , _ = inj₂ (λ ())
    T ⊪ var x   , _ ≤? τ₁ ⟶ τ₂ , _ = inj₂ (λ ())
    T ⊪ σ₁ ⟶ σ₂ , _ ≤? ⊥       , _ = inj₂ (λ ())
    T ⊪ σ₁ ⟶ σ₂ , _ ≤? var x   , _ = inj₂ (λ ())

  -- Finally we have to prove that an upper bound ℓ actually exists.

  dec : [] ⊢ χ₁ ≤ χ₂ ⊎ (¬ χ₁ ≤Coind χ₂)
  dec = empty ⊢ χ₁ , inj₁ ST.refl ≤? χ₂ , inj₂ ST.refl

infix 4 []⊢_≤?_ _≤?_

-- The subtyping relation defined above is decidable (when the set of
-- assumptions is empty).

[]⊢_≤?_ : ∀ {n} (σ τ : Ty n) → Dec ([] ⊢ σ ≤ τ)
[]⊢ σ ≤? τ with Decidable.dec σ τ
... | inj₁ σ≤τ = yes σ≤τ
... | inj₂ σ≰τ = no (σ≰τ ∘ Ax.sound ∘ flip sound [])

-- The other subtyping relations can also be decided.

_≤?_ : ∀ {n} (σ τ : Ty n) → Dec (σ ≤ τ)
σ ≤? τ with Decidable.dec σ τ
... | inj₁ σ≤τ = yes (sound σ≤τ [])
... | inj₂ σ≰τ = no (σ≰τ ∘ Ax.sound)

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
weaken (hyp h)               = hyp (AnyP.++⁺ˡ h)
weaken (τ₁≤σ₁ ⟶ σ₂≤τ₂)       = weaken τ₁≤σ₁ ⟶ weaken σ₂≤τ₂

-- The subtyping relation defined above is complete with respect to
-- the others.

complete : ∀ {n A} {σ τ : Ty n} →
           σ ≤ τ → A ⊢ σ ≤ τ
complete {σ = σ} {τ} σ≤τ with Decidable.dec σ τ
... | inj₁ ⊢σ≤τ = weaken ⊢σ≤τ
... | inj₂ σ≰τ  = ⊥-elim (σ≰τ (Ax.sound σ≤τ))
