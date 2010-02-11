------------------------------------------------------------------------
-- The semantics in Lambda.Closure.Relational and
-- Lambda.Closure.Functional are equivalent
------------------------------------------------------------------------

module Lambda.Closure.Equivalence where

open import Category.Monad.Partiality
  hiding (>>=-inversion-⇓; >>=-inversion-⇑; module Workaround)
open import Coinduction
open import Data.Empty using (⊥-elim)
open import Data.Maybe
open import Data.Product
open import Data.Sum
open import Data.Vec using (Vec; []; _∷_)
open import Function
open import Relation.Nullary
open import Relation.Nullary.Negation

open RelReasoning

open import Lambda.Syntax
open Closure Tm
open import Lambda.Closure.Relational as R hiding (⊥)
open import Lambda.Closure.Functional as F hiding (module Workaround)
open PF

-- The functional semantics is complete for terminating computations.

complete⇓ : ∀ {n} {t : Tm n} {ρ v} →
            ρ ⊢ t ⇒ val v → ⟦ t ⟧ ρ ≈ return v
complete⇓ var = _ ∎
complete⇓ con = _ ∎
complete⇓ ƛ   = _ ∎
complete⇓ {ρ = ρ} {v′} (app {t₁} {t₂} {t = t} {ρ′} {v} t₁⇓ t₂⇓ t₁t₂⇓) =
  ⟦ t₁ · t₂ ⟧ ρ                 ≅⟨ ·-comp t₁ t₂ ⟩
  ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ         ≈⟨ complete⇓ t₁⇓ ⟦·⟧-cong complete⇓ t₂⇓ ⟩
  return (ƛ t ρ′) ⟦·⟧ return v  ≳⟨ laterˡ (_ ∎) ⟩
  ⟦ t ⟧ (v ∷ ρ′)                ≈⟨ complete⇓ t₁t₂⇓ ⟩
  return v′                     ∎

-- The functional semantics is complete for non-terminating computations.

module Complete⇑ where

  infix  4 _≈P_ _≈W_
  infixr 2 _≅⟪_⟫_ _≳⟪_⟫_ _≈⟪_⟫_

  data _≈P_ : Maybe Value ⊥ → Maybe Value ⊥ → Set₁ where
    ⌈_⌉ : ∀ {x y} (x≳y : x ≳ y) → x ≈P y

    later : ∀ {x y} (x≈y : ∞ (♭ x ≈P ♭ y)) → later x ≈P later y

    _>>=P_ : ∀ {x₁ x₂ f₁ f₂} →
             (x₁≈x₂ : x₁ ≈P x₂) (f₁≈f₂ : ∀ x → f₁ x ≈P f₂ x) →
             (x₁ >>= f₁) ≈P (x₂ >>= f₂)
    _⟦·⟧P_ : ∀ {v₁₁ v₁₂ v₂₁ v₂₂} →
             (v₁₁≈v₂₁ : v₁₁ ≈P v₂₁) (v₁₂≈v₂₂ : v₁₂ ≈P v₂₂) →
             v₁₁ ⟦·⟧ v₁₂ ≈P v₂₁ ⟦·⟧ v₂₂

    _≅⟪_⟫_ : ∀ x {y z} (x≅y : x ≅  y) (y≈z : y ≈P z) → x ≈P z
    _≳⟪_⟫_ : ∀ x {y z} (x≳y : x ≳  y) (y≈z : y ≈P z) → x ≈P z
    _≈⟪_⟫_ : ∀ x {y z} (x≈y : x ≈P y) (y≅z : y ≅  z) → x ≈P z

  private

    data _≈W_ : Maybe Value ⊥ → Maybe Value ⊥ → Set₁ where
      now    : ∀ {v}                      → now   v ≈W now   v
      later  : ∀ {x y} (x≈y : ♭ x ≈P ♭ y) → later x ≈W later y
      laterˡ : ∀ {x y} (x≈y : ♭ x ≈W   y) → later x ≈W       y

    ⌈_⌉W : ∀ {x y} → x ≳ y → x ≈W y
    ⌈ now        ⌉W = now
    ⌈ later  x≳y ⌉W = later ⌈ ♭ x≳y ⌉
    ⌈ laterˡ x≳y ⌉W = laterˡ ⌈ x≳y ⌉W

    program : ∀ {x y} → x ≈W y → x ≈P y
    program now          = ⌈ now ⌉
    program (later  x≈y) = later (♯ x≈y)
    program (laterˡ x≈y) = _ ≳⟪ laterˡ (_ ∎) ⟫ program x≈y

    _>>=W_ : ∀ {x₁ x₂ f₁ f₂} →
             x₁ ≈W x₂ → (∀ x → f₁ x ≈W f₂ x) →
             (x₁ >>= f₁) ≈W (x₂ >>= f₂)
    now {v = nothing} >>=W f₁≈f₂ = now
    now {v = just v } >>=W f₁≈f₂ = f₁≈f₂ v
    later  x≈y        >>=W f₁≈f₂ = later (x≈y >>=P (program ∘ f₁≈f₂))
    laterˡ x≈y        >>=W f₁≈f₂ = laterˡ (x≈y >>=W f₁≈f₂)

    _⟦·⟧W_ : ∀ {v₁₁ v₁₂ v₂₁ v₂₂} →
             v₁₁ ≈W v₂₁ → v₁₂ ≈W v₂₂ → v₁₁ ⟦·⟧ v₁₂ ≈W v₂₁ ⟦·⟧ v₂₂
    v₁₁≈v₂₁ ⟦·⟧W v₁₂≈v₂₂ =
      v₁₁≈v₂₁ >>=W λ v₁ →
      v₁₂≈v₂₂ >>=W λ v₂ →
      ⌈ ⟪ v₁ ∙ v₂ ⟫P ∎ ⌉W
      where open F.Workaround

    trans≅≈W : ∀ {x y z} → x ≅ y → y ≈W z → x ≈W z
    trans≅≈W now          now           = now
    trans≅≈W (later  x≅y) (later  y≈z)  = later (_ ≅⟪ ♭ x≅y ⟫ y≈z)
    trans≅≈W (later  x≅y) (laterˡ y≈z)  = laterˡ (trans≅≈W (♭ x≅y) y≈z)

    trans≳≈W : ∀ {x y z} → x ≳ y → y ≈W z → x ≈W z
    trans≳≈W now          now           = now
    trans≳≈W (later  x≳y) (later  y≈z)  = later (_ ≳⟪ ♭ x≳y ⟫ y≈z)
    trans≳≈W (later  x≳y) (laterˡ y≈z)  = laterˡ (trans≳≈W (♭ x≳y) y≈z)
    trans≳≈W (laterˡ x≳y)         y≈z   = laterˡ (trans≳≈W x≳y y≈z)

    trans≈W≅ : ∀ {x y z} → x ≈W y → y ≅ z → x ≈W z
    trans≈W≅ now          now         = now
    trans≈W≅ (later  x≈y) (later y≅z) = later (_ ≈⟪ x≈y ⟫ ♭ y≅z)
    trans≈W≅ (laterˡ x≈y)        y≅z  = laterˡ (trans≈W≅ x≈y y≅z)

    whnf : ∀ {x y} → x ≈P y → x ≈W y
    whnf ⌈ x≳y ⌉                = ⌈ x≳y ⌉W
    whnf (later x≈y)            = later (♭ x≈y)
    whnf (x₁≈x₂ >>=P f₁≈f₂)     = whnf x₁≈x₂ >>=W λ v → whnf (f₁≈f₂ v)
    whnf (v₁₁≈v₂₁ ⟦·⟧P v₁₂≈v₂₂) = whnf v₁₁≈v₂₁ ⟦·⟧W whnf v₁₂≈v₂₂
    whnf (x ≅⟪ x≅y ⟫ y≈z)       = trans≅≈W x≅y (whnf y≈z)
    whnf (x ≳⟪ x≳y ⟫ y≈z)       = trans≳≈W x≳y (whnf y≈z)
    whnf (x ≈⟪ x≈y ⟫ y≅z)       = trans≈W≅ (whnf x≈y) y≅z

  mutual

    private

      soundW : ∀ {x y} → x ≈W y → x ≈ y
      soundW now          = now
      soundW (later  x≈y) = later (♯ soundP x≈y)
      soundW (laterˡ x≈y) = laterˡ (soundW x≈y)

    soundP : ∀ {x y} → x ≈P y → x ≈ y
    soundP x≈y = soundW (whnf x≈y)

  -- The language _≈P_ does not include transitivity for weak
  -- equality, as this would be unsound. Instead some limited notions
  -- of transitivity are used:
  --
  -- • Weak equality can be combined with strong equality on both
  --   sides.
  --
  -- • The _≳_ order can be "prepended" to a weak equality. Note that
  --   results of the form "x ≈ return v" can be turned into
  --   "x ≳ return v", as in the first case below.

  complete⇑ : ∀ {n} {t : Tm n} {ρ : Env n} →
              ρ ⊢ t ⇒ R.⊥ → ⟦ t ⟧ ρ ≈P never
  complete⇑ {ρ = ρ} (app {t₁} {t₂} {t = t} {ρ′} {v} t₁⇓ t₂⇓ t₁t₂⇑) =
    ⟦ t₁ · t₂ ⟧ ρ                 ≅⟪ ·-comp t₁ t₂ ⟫
    ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ         ≳⟪ now⇒now (complete⇓ t₁⇓) ⟦·⟧-cong
                                     now⇒now (complete⇓ t₂⇓) ⟫
    return (ƛ t ρ′) ⟦·⟧ return v  ≅⟪ later (♯ (_ ∎)) ⟫
    later (♯ ⟦ t ⟧ (v ∷ ρ′))      ≈⟪ later (♯ complete⇑ (♭ t₁t₂⇑)) ⟫
    never                         ∎
  complete⇑ {ρ = ρ} (·ˡ {t₁} {t₂} t₁⇑) =
    ⟦ t₁ · t₂ ⟧ ρ          ≅⟪ ·-comp t₁ t₂ ⟫
    ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ  ≈⟪ complete⇑ (♭ t₁⇑) ⟦·⟧P ⌈ ⟦ t₂ ⟧ ρ ∎ ⌉ ⟫
    never ⟦·⟧ ⟦ t₂ ⟧ ρ     ≅⟨ left-zero _ ⟩
    never                  ∎
  complete⇑ {ρ = ρ} (·ʳ {t₁} {t₂} {v} t₁⇓ t₂⇑) =
    ⟦ t₁ · t₂ ⟧ ρ          ≅⟪ ·-comp t₁ t₂ ⟫
    ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ  ≈⟪ ⌈ now⇒now (complete⇓ t₁⇓) ⌉ ⟦·⟧P complete⇑ (♭ t₂⇑) ⟫
    return v ⟦·⟧ never     ≅⟨ left-zero _ ⟩
    never                  ∎

complete⇑ : ∀ {n} {t : Tm n} {ρ : Env n} →
            ρ ⊢ t ⇒ R.⊥ → ⟦ t ⟧ ρ ≈ never
complete⇑ = Complete⇑.soundP ∘ Complete⇑.complete⇑

-- The functional semantics is sound for terminating computations.
-- Note that this proof is not accepted by the termination checker. It
-- is terminating, though (at least in the empty context): the proof
-- follows the structure of the computation ⟦ t ⟧ ρ, which is assumed
-- to terminate.

sound⇓ : ∀ {n} (t : Tm n) {ρ : Env n} {v} →
         ⟦ t ⟧ ρ ≈ return v → ρ ⊢ t ⇒ val v
sound⇓ (con i)           now   = con
sound⇓ (var x)           now   = var
sound⇓ (ƛ t)             now   = ƛ
sound⇓ (t₁ · t₂) {ρ} {v} t₁t₂⇓
  with >>=-inversion-⇓ (⟦ t₁ ⟧ ρ) (
         ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ  ≅⟨ sym $ ·-comp t₁ t₂ ⟩
         ⟦ t₁ · t₂ ⟧ ρ          ≈⟨ t₁t₂⇓ ⟩
         return v            ∎)
sound⇓ (t₁ · t₂) {ρ} t₁t₂⇓ | (v₁    , t₁⇓ , t₂∙⇓) with >>=-inversion-⇓ (⟦ t₂ ⟧ ρ) t₂∙⇓
sound⇓ (t₁ · t₂)     t₁t₂⇓ | (con i , t₁⇓ , t₂∙⇓) | (v₂ , t₂⇓ , ())
sound⇓ (t₁ · t₂)     t₁t₂⇓ | (ƛ t _ , t₁⇓ , t₂∙⇓) | (v₂ , t₂⇓ , laterˡ ∙⇓) =
  app (sound⇓ t₁ t₁⇓) (sound⇓ t₂ t₂⇓) (sound⇓ t ∙⇓)

-- The functional semantics is sound for non-terminating computations.
-- I assume excluded middle here because double-negation elimination
-- is used "infinitely often".

sound⇑ : Excluded-Middle _ → ∀ {n} (t : Tm n) {ρ : Env n} →
         ⟦ t ⟧ ρ ≈ never → ρ ⊢ t ⇒ R.⊥
sound⇑ em (con i)       ⇑ = ⊥-elim (now≉never ⇑)
sound⇑ em (var x)       ⇑ = ⊥-elim (now≉never ⇑)
sound⇑ em (ƛ t)         ⇑ = ⊥-elim (now≉never ⇑)
sound⇑ em (t₁ · t₂) {ρ} ⇑
  with >>=-inversion-⇑ em (⟦ t₁ ⟧ ρ) (
         ⟦ t₁ ⟧ ρ ⟦·⟧ ⟦ t₂ ⟧ ρ  ≅⟨ sym $ ·-comp t₁ t₂ ⟩
         ⟦ t₁ · t₂ ⟧ ρ          ≈⟨ ⇑ ⟩
         never                  ∎)
sound⇑ em (t₁ · t₂)     ⇑ | inj₁ t₁⇑               = ·ˡ (♯ sound⇑ em t₁ t₁⇑)
sound⇑ em (t₁ · t₂) {ρ} ⇑ | inj₂ (v₁ , t₁⇓ , t₂∙⇑)
  with >>=-inversion-⇑ em (⟦ t₂ ⟧ ρ) t₂∙⇑
sound⇑ em (t₁ · t₂) ⇑ | inj₂ (v₁    , t₁⇓ , t₂∙⇑) | inj₁ t₂⇑             = ·ʳ (sound⇓ t₁ t₁⇓) (♯ sound⇑ em t₂ t₂⇑)
sound⇑ em (t₁ · t₂) ⇑ | inj₂ (con i , t₁⇓ , t₂∙⇑) | inj₂ (v₂ , t₂⇓ , ∙⇑) = ⊥-elim (now≉never ∙⇑)
sound⇑ em (t₁ · t₂) ⇑ | inj₂ (ƛ t _ , t₁⇓ , t₂∙⇑) | inj₂ (v₂ , t₂⇓ , ∙⇑) =
  app (sound⇓ t₁ t₁⇓) (sound⇓ t₂ t₂⇓) (♯ sound⇑ em t (later⁻¹ ∙⇑))

-- The functional semantics is complete for crashing computations.

complete↯ : Excluded-Middle _ → ∀ {n} (t : Tm n) (ρ : Env n) →
            ∄ (λ s → ρ ⊢ t ⇒ s) → ⟦ t ⟧ ρ ≈ now nothing
complete↯ em t ρ ¬⇒
  with decidable-stable em $ now-or-never {k = weak} (⟦ t ⟧ ρ)
... | inj₂ t⇑             = ⊥-elim (¬⇒ (, sound⇑ em t t⇑))
... | inj₁ (nothing , t↯) = t↯
... | inj₁ (just v  , t⇓) = ⊥-elim (¬⇒ (, sound⇓ t t⇓))

-- The functional semantics is sound for crashing computations.

sound↯ : ∀ {n} {t : Tm n} {ρ : Env n} →
         ⟦ t ⟧ ρ ≈ now nothing → ∄ λ s → ρ ⊢ t ⇒ s
sound↯ {t = t} {ρ} t↯ (val v , t⇓)
  with now nothing  ≈⟨ sym t↯ ⟩
       ⟦ t ⟧ ρ      ≈⟨ complete⇓ t⇓ ⟩
       return v     ∎
... | ()
sound↯ {t = t} {ρ} t↯ (R.⊥ , t⇑) = now≉never (
  now nothing  ≈⟨ sym t↯ ⟩
  ⟦ t ⟧ ρ      ≈⟨ complete⇑ t⇑ ⟩
  never        ∎)
