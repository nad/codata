------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.Closure.Functional where

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

------------------------------------------------------------------------
-- A workaround for the limitations of guardedness

module Workaround where

  data Maybe_⊥P : Set → Set₁ where
    fail   : ∀ {A} → Maybe A ⊥P
    return : ∀ {A} (x : A) → Maybe A ⊥P
    later  : ∀ {A} (x : ∞ (Maybe A ⊥P)) → Maybe A ⊥P
    _>>=_  : ∀ {A B} (x : Maybe A ⊥P) (f : A → Maybe B ⊥P) → Maybe B ⊥P

  private

    data Maybe_⊥W : Set → Set₁ where
      fail   : ∀ {A} → Maybe A ⊥W
      return : ∀ {A} (x : A) → Maybe A ⊥W
      later  : ∀ {A} (x : Maybe A ⊥P) → Maybe A ⊥W

    mutual

      _>>=W_ : ∀ {A B} → Maybe A ⊥W → (A → Maybe B ⊥P) → Maybe B ⊥W
      fail     >>=W f = fail
      return x >>=W f = whnf (f x)
      later x  >>=W f = later (x >>= f)

      whnf : ∀ {A} → Maybe A ⊥P → Maybe A ⊥W
      whnf fail       = fail
      whnf (return x) = return x
      whnf (later x)  = later (♭ x)
      whnf (x >>= f)  = whnf x >>=W f

  mutual

    private

      ⟪_⟫W : ∀ {A} → Maybe A ⊥W → Maybe A ⊥
      ⟪ fail     ⟫W = PF.fail
      ⟪ return x ⟫W = PF.return x
      ⟪ later x  ⟫W = later (♯ ⟪ x ⟫P)

    ⟪_⟫P : ∀ {A} → Maybe A ⊥P → Maybe A ⊥
    ⟪ p ⟫P = ⟪ whnf p ⟫W

  -- The definitions above make sense. ⟪_⟫P is homomorphic with respect
  -- to fail, return, later and _>>=_.

  fail-hom : ∀ {A} → ⟪ fail {A = A} ⟫P ≅ PF.fail
  fail-hom = PF.fail ∎

  return-hom : ∀ {A} (x : A) → ⟪ return x ⟫P ≅ PF.return x
  return-hom x = PF.return x ∎

  later-hom : ∀ {A} (x : ∞ Maybe A ⊥P) →
              ⟪ later x ⟫P ≅ later (♯ ⟪ ♭ x ⟫P)
  later-hom x = later (♯ (⟪ ♭ x ⟫P ∎))

  mutual

    private

      >>=-homW : ∀ {A B} (x : Maybe A ⊥W) (f : A → Maybe B ⊥P) →
                 ⟪ x >>=W f ⟫W ≅ PF._>>=_ ⟪ x ⟫W (λ y → ⟪ f y ⟫P)
      >>=-homW fail       f = PF.fail ∎
      >>=-homW (return x) f = ⟪ f x ⟫P ∎
      >>=-homW (later x)  f = later (♯ >>=-hom x f)

    >>=-hom : ∀ {A B} (x : Maybe A ⊥P) (f : A → Maybe B ⊥P) →
              ⟪ x >>= f ⟫P ≅ PF._>>=_ ⟪ x ⟫P (λ y → ⟪ f y ⟫P)
    >>=-hom x f = >>=-homW (whnf x) f

open Workaround hiding (_>>=_)

------------------------------------------------------------------------
-- Semantics

infix 5 _∙_

-- Note that this definition gives us determinism "for free".

mutual

  ⟦_⟧′ : ∀ {n} → Tm n → Env n → Maybe Value ⊥P
  ⟦ con i ⟧′   ρ = return (con i)
  ⟦ var x ⟧′   ρ = return (lookup ρ x)
  ⟦ ƛ t ⟧′     ρ = return (ƛ t ρ)
  ⟦ t₁ · t₂ ⟧′ ρ = ⟦ t₁ ⟧′ ρ >>= λ v₁ →
                   ⟦ t₂ ⟧′ ρ >>= λ v₂ →
                   v₁ ∙ v₂
    where open Workaround

  _∙_ : Value → Value → Maybe Value ⊥P
  con i  ∙ v₂ = fail
  ƛ t₁ ρ ∙ v₂ = later (♯ (⟦ t₁ ⟧′ (v₂ ∷ ρ)))

⟦_⟧ : ∀ {n} → Tm n → Env n → Maybe Value ⊥
⟦ t ⟧ ρ = ⟪ ⟦ t ⟧′ ρ ⟫P

------------------------------------------------------------------------
-- Example

Ω-loops : ⟦ Ω ⟧ [] ≈ never
Ω-loops = later (♯ Ω-loops)

------------------------------------------------------------------------
-- Some lemmas

open PF hiding (_>>=_)

-- An abbreviation.

infix 5 _⟦·⟧_

_⟦·⟧_ : Maybe Value ⊥ → Maybe Value ⊥ → Maybe Value ⊥
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

·-comp : ∀ {n} (t₁ t₂ : Tm n) {ρ} →
         ⟦ t₁ · t₂ ⟧ ρ ≅ ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ
·-comp t₁ t₂ {ρ} =
  ⟦ t₁ · t₂ ⟧ ρ                                    ≅⟨ >>=-hom (⟦ t₁ ⟧′ ρ) _ ⟩

  PF._>>=_ (⟦ t₁ ⟧ ρ) (λ v₁ →
           ⟪ Workaround._>>=_ (⟦ t₂ ⟧′ ρ) (λ v₂ →
             v₁ ∙ v₂) ⟫P)                          ≅⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ →
                                                       >>=-hom (⟦ t₂ ⟧′ ρ) _) ⟩
  ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ                            ∎

open PF

------------------------------------------------------------------------
-- Compiler correctness

module Correctness {k : OtherKind} where

  infix  4 _≈P_ _≈W_
  infixr 2 _≡⟨_⟩W_ _≈⟨_⟩P_ _≈⟨_⟩W_

  mutual

    data _≈P_ : Maybe VM.Value ⊥ → Maybe VM.Value ⊥ → Set where
      _≈⟨_⟩P_ : ∀ x {y z} (x≈y : x ≈P y) (y≅z : y ≅ z) → x ≈P z
      correct :
        ∀ {n} t {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
        (hyp : ∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩
                       ≈W k v) →
        exec ⟨ comp t c , s , comp-env ρ ⟩ ≈P (⟦ t ⟧ ρ >>= k)

    data _≈W_ : Maybe VM.Value ⊥ → Maybe VM.Value ⊥ → Set where
      ⌈_⌉    : ∀ {x y} (x≈y : Rel (other k) x y) → x ≈W y
      later  : ∀ {x y} (x≈y : ♭ x ≈P ♭ y) → later x ≈W later y
      laterˡ : ∀ {x y} (x≈y : ♭ x ≈W   y) → later x ≈W       y

  _≡⟨_⟩W_ : ∀ x {y z} → x ≡ y → y ≈W z → x ≈W z
  _ ≡⟨ P.refl ⟩W y≈z = y≈z

  _≈⟨_⟩W_ : ∀ x {y z} → x ≈W y → y ≅ z → x ≈W z
  ._ ≈⟨ later  x≈y ⟩W later y≅z = later  (_ ≈⟨ x≈y ⟩P ♭ y≅z)
  ._ ≈⟨ laterˡ x≈y ⟩W       y≅z = laterˡ (_ ≈⟨ x≈y ⟩W   y≅z)
  _  ≈⟨ ⌈ x≈y ⌉    ⟩W       y≅z = ⌈ trans x≈y (Partiality.≅⇒ y≅z) ⌉
    where trans = Preorder.trans (Partiality.preorder P.isPreorder _)

  -- The relation _≈_ does not admit unrestricted use of transitivity
  -- in corecursive proofs, so I have formulated the correctness proof
  -- using a continuation. Note that the proof would perhaps be easier
  -- if the semantics was also formulated in continuation-passing
  -- style.

  mutual

    correctW :
      ∀ {n} t {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
      (∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈W k v) →
      exec ⟨ comp t c , s , comp-env ρ ⟩ ≈W (⟦ t ⟧ ρ >>= k)
    correctW (con i) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (Lambda.Syntax.Closure.con i) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (con i) ⟩W
      k (con i)                                                        ∎)
    correctW (var x) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (lookup (comp-env ρ) x) ∷ s , comp-env ρ ⟩  ≡⟨ P.cong (λ v → exec ⟨ c , val v ∷ s , comp-env ρ ⟩) $ lookup-hom x ρ ⟩W
      exec ⟨ c , val (comp-val (lookup ρ x)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (lookup ρ x) ⟩W
      k (lookup ρ x)                                             ∎)
    correctW (ƛ t) {ρ} {c} {s} {k} hyp = laterˡ (
      exec ⟨ c , val (comp-val (ƛ t ρ)) ∷ s , comp-env ρ ⟩  ≈⟨ hyp (ƛ t ρ) ⟩W
      k (ƛ t ρ)                                             ∎)
    correctW (t₁ · t₂) {ρ} {c} {s} {k} hyp =
      exec ⟨ comp t₁ (comp t₂ (app ∷ c)) , s , comp-env ρ ⟩           ≈⟨ correctW t₁ (λ v₁ → correctW t₂ (λ v₂ → ∙-correctW v₁ v₂ hyp)) ⟩W
      (⟦ t₁ ⟧ ρ >>= λ v₁ →  ⟦ t₂ ⟧ ρ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P  >>= k)  ≅⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ → sym $ associative (⟦ t₂ ⟧ ρ) _ _) ⟩
      (⟦ t₁ ⟧ ρ >>= λ v₁ → (⟦ t₂ ⟧ ρ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P) >>= k)  ≅⟨ sym $ associative (⟦ t₁ ⟧ ρ) _ _ ⟩
      (⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ >>= k)                                   ≅⟨ sym (·-comp t₁ t₂ >>=-cong λ v → k v ∎) ⟩
      (⟦ t₁ · t₂ ⟧ ρ >>= k)                                           ∎

    ∙-correctW :
      ∀ {n} v₁ v₂ {ρ : Env n} {c s} {k : Value → Maybe VM.Value ⊥} →
      (∀ v → exec ⟨ c , val (comp-val v) ∷ s , comp-env ρ ⟩ ≈W k v) →
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val v₁) ∷ s , comp-env ρ ⟩ ≈W
      (⟪ v₁ ∙ v₂ ⟫P >>= k)
    ∙-correctW (con i)   v₂                 _   = ⌈ PF.fail ∎ ⌉
    ∙-correctW (ƛ t₁ ρ₁) v₂ {ρ} {c} {s} {k} hyp =
      exec ⟨ app ∷ c , val (comp-val v₂) ∷ val (comp-val (ƛ t₁ ρ₁)) ∷ s , comp-env ρ ⟩  ≈⟨ later (

        exec ⟨ comp t₁ [ ret ] , ret c (comp-env ρ) ∷ s , comp-env (v₂ ∷ ρ₁) ⟩               ≈⟨ correct t₁ (λ v → laterˡ (hyp v)) ⟩P
        (⟦ t₁ ⟧ (v₂ ∷ ρ₁) >>= k)                                                             ∎) ⟩W

      (⟪ ƛ t₁ ρ₁ ∙ v₂ ⟫P >>= k)                                                         ∎

  whnf : ∀ {x y} → x ≈P y → x ≈W y
  whnf (x ≈⟨ x≈y ⟩P y≅z) = x ≈⟨ whnf x≈y ⟩W y≅z
  whnf (correct t hyp)   = correctW t hyp

  mutual

    soundW : ∀ {x y} → x ≈W y → Rel (other k) x y
    soundW ⌈ x≈y ⌉      = x≈y
    soundW (later  x≈y) = later (♯ soundP x≈y)
    soundW (laterˡ x≈y) = laterˡ (soundW x≈y)

    soundP : ∀ {x y} → x ≈P y → Rel (other k) x y
    soundP x≈y = soundW (whnf x≈y)

-- Note that the equality that is used here is syntactic.

correct : ∀ t →
          exec ⟨ comp t [] , [] , [] ⟩ ≈
          (⟦ t ⟧ [] >>= λ v → PF.return (comp-val v))
correct t =
  soundP $ Correctness.correct t (λ v → ⌈ PF.return (comp-val v) ∎ ⌉)
  where open Correctness
