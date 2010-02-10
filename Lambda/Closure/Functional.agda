------------------------------------------------------------------------
-- Functional semantics for an untyped λ-calculus with constants
------------------------------------------------------------------------

module Lambda.Closure.Functional where

open import Category.Monad
open import Category.Monad.Partiality as Partiality
  hiding (_>>=-cong_; associative; >>=-inversion-⇓; >>=-inversion-⇑;
          module Workaround)
open import Coinduction
open import Data.Empty using (⊥-elim)
open import Data.List
open import Data.Maybe as Maybe
open import Data.Product
open import Data.Sum
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Function
open import Relation.Nullary.Negation

open RelReasoning

open import Lambda.Syntax
open Closure Tm
open import Lambda.VirtualMachine as VM renaming (⟦_⟧ to ⟦_⟧t)
open VM.Functional

------------------------------------------------------------------------
-- A monad with partiality and failure

PF : RawMonad (_⊥ ∘ Maybe)
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
    helper : ∀ x → Rel k (maybe f₁ fail x) (maybe f₂ fail x)
    helper nothing  = fail ∎
    helper (just x) = f₁≈f₂ x

  associative :
    {A B C : Set}
    (x : Maybe A ⊥) (f : A → Maybe B ⊥) (g : B → Maybe C ⊥) →
    (x >>= f >>= g) ≅ (x >>= λ y → f y >>= g)
  associative x f g =
    (x >>= f >>= g)                      ≅⟨ Partiality.associative x _ _ ⟩
    (x >>=′ λ y → maybe f fail y >>= g)  ≅⟨ Partiality._>>=-cong_ (x ∎) helper ⟩
    (x >>= λ y → f y >>= g)              ∎
    where
    open RawMonad Partiality.monad renaming (_>>=_ to _>>=′_)

    helper : ∀ y → (maybe f fail y >>= g) ≅
                   maybe (λ z → f z >>= g) fail y
    helper nothing  = fail ∎
    helper (just y) = (f y >>= g) ∎

  >>=-inversion-⇓ :
    ∀ {k} {A B : Set} x {f : A → Maybe B ⊥} {y} →
    Rel k (x >>= f) (return y) →
    ∃ λ z → Rel k x (return z) × Rel k (f z) (return y)
  >>=-inversion-⇓ x {f} x>>=f⇓
    with Partiality.>>=-inversion-⇓ x x>>=f⇓
  ... | (nothing , x↯ , ())
  ... | (just z  , x⇓ , fz⇓) = (z , x⇓ , fz⇓)

  >>=-inversion-⇑ :
    Excluded-Middle _ →
    ∀ {A B : Set} x {f : A → Maybe B ⊥} →
    (x >>= f) ≳ never →
    x ≳ never ⊎ ∃ λ y → x ≳ return y × f y ≳ never
  >>=-inversion-⇑ em x {f} x>>=f⇑
    with decidable-stable em $ Partiality.>>=-inversion-⇑ x x>>=f⇑
  ... | inj₁ x⇑                         = inj₁ x⇑
  ... | inj₂ (just y  , x⇓ , fy⇑)       = inj₂ (y , x⇓ , fy⇑)
  ... | inj₂ (nothing , x↯ , now≳never) =
    ⊥-elim (now≉never (≳⇒ now≳never))

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
      ⟪ return x ⟫W = now (just x)
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
  ⟦ var x ⟧′   ρ = return (lookup x ρ)
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

ω : Tm 0
ω = ƛ (vr 0 · vr 0)

Ω : Tm 0
Ω = ω · ω

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

-- The semantics of application is compositional.

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

-- Note that the proof below is not accepted by the termination
-- checker. _≈_ does not admit unrestricted use of transitivity in
-- corecursive proofs, so my usual trick for working around the
-- limitations of the productivity checker does not help here.

correct′ : ∀ {n} t {ρ : Env n} {c s} →
           exec ⟨ ⟦ t ⟧t c , s , ⟦ ρ ⟧ρ ⟩ ≈
           (⟦ t ⟧ ρ >>= λ v → exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)
correct′ (con i)                               = laterˡ (_ ∎)
correct′ (var x) {ρ} rewrite VM.lookup-hom x ρ = laterˡ (_ ∎)
correct′ (ƛ t)                                 = laterˡ (_ ∎)
correct′ (t₁ · t₂) {ρ} {c} {s} =
  exec ⟨ ⟦ t₁ ⟧t (⟦ t₂ ⟧t (App ∷ c)) , s , ⟦ ρ ⟧ρ ⟩            ≈⟨ correct′ t₁ ⟩

  (⟦ t₁ ⟧ ρ >>= λ v₁ →
   exec ⟨ (⟦ t₂ ⟧t (App ∷ c)) , val ⟦ v₁ ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)    ≈⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ → correct′ t₂) ⟩

  (⟦ t₁ ⟧ ρ >>= λ v₁ →
   ⟦ t₂ ⟧ ρ >>= λ v₂ →
   exec ⟨ App ∷ c , val ⟦ v₂ ⟧v ∷ val ⟦ v₁ ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)  ≈⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ v₁ →
                                                                   (⟦ t₂ ⟧ ρ ∎) >>=-cong λ v₂ →
                                                                   helper v₁ v₂) ⟩
  (⟦ t₁ ⟧ ρ     >>= λ v₁ →
   ⟦ t₂ ⟧ ρ     >>= λ v₂ →
   ⟪ v₁ ∙ v₂ ⟫P >>= λ v  →
   exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)                       ≅⟨ ((⟦ t₁ ⟧ ρ ∎) >>=-cong λ _ →
                                                                   sym $ associative (⟦ t₂ ⟧ ρ) _ _) ⟩
  (⟦ t₁ ⟧ ρ >>= λ v₁ →
   (⟦ t₂ ⟧ ρ >>= λ v₂ → ⟪ v₁ ∙ v₂ ⟫P) >>= λ v →
   exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)                       ≅⟨ sym $ associative (⟦ t₁ ⟧ ρ) _ _ ⟩

  (⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ >>= λ v →
   exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)                       ≅⟨ sym (·-comp t₁ t₂ >>=-cong λ _ → _ ∎) ⟩

  (⟦ t₁ · t₂ ⟧ ρ >>= λ v →
   exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)                       ∎
  where
  helper :
    ∀ v₁ v₂ →
    exec ⟨ App ∷ c , val ⟦ v₂ ⟧v ∷ val ⟦ v₁ ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩ ≈
    PF._>>=_ ⟪ v₁ ∙ v₂ ⟫P (λ v → exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)
  helper (con i)   v₂ = _ ∎
  helper (ƛ t₁ ρ′) v₂ = later (♯ (
    exec ⟨ ⟦ t₁ ⟧t [ Ret ] , ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v₂ ∷ ρ′ ⟧ρ ⟩         ≈⟨ correct′ t₁ ⟩

    (⟦ t₁ ⟧ (v₂ ∷ ρ′) >>= λ v →
     exec ⟨ [ Ret ] , val ⟦ v ⟧v ∷ ret c ⟦ ρ ⟧ρ ∷ s , ⟦ v₂ ∷ ρ′ ⟧ρ ⟩)  ≳⟨ ((⟦ t₁ ⟧ (v₂ ∷ ρ′) ∎) >>=-cong λ _ →
                                                                           laterˡ (_ ∎)) ⟩

    (⟦ t₁ ⟧ (v₂ ∷ ρ′) >>= λ v →
     exec ⟨ c , val ⟦ v ⟧v ∷ s , ⟦ ρ ⟧ρ ⟩)                             ∎))

-- Note that the statement of compiler correctness used here is more
-- useful, and less involved, than the one in
-- Lambda.Closure.Relational. The latter statement does not apply to
-- terms which crash. Furthermore it is not a self-contained
-- correctness statement, but relies on a separate proof which shows
-- that the VM is deterministic.

correct : ∀ t →
          exec ⟨ ⟦ t ⟧t [] , [] , [] ⟩ ≈
          (⟦ t ⟧ [] >>= λ v → PF.return ⟦ v ⟧v)
correct t = correct′ t
