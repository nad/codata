-- ...
-- Coinductive Axiomatization of Recursive Type Equality and Subtyping

module RecursiveTypes where

import Data.Nat as Nat; open Nat using (ℕ; zero; suc; _+_)
import Data.Fin as Fin; open Fin using (Fin; zero; suc)
import Data.Vec as Vec; open Vec using (Vec; []; _∷_)
import Data.Vec.Properties as VecProp
open import Coinduction
open import Data.Function
open import Relation.Binary.PropositionalEquality

infixr 10 _⟶_
infix  10 ν_⟶_

data Ty (n : ℕ) : Set where
  ⊥    : Ty n
  ⊤    : Ty n
  var  : (x : Fin n) → Ty n
  _⟶_  : (σ τ : Ty n) → Ty n
  -- TODO: Make sure that var zero is free in σ or τ?
  ν_⟶_ : (σ τ : Ty (suc n)) → Ty n

data Tree (n : ℕ) : Set where
  ⊥    : Tree n
  ⊤    : Tree n
  var  : (x : Fin n) → Tree n
  _⟶_  : (σ τ : ∞ (Tree n)) → Tree n

infixl 5 _▻_

data Env (m : ℕ) : ℕ → Set where
  ∅   : Env m 0
  _▻_ : ∀ {n} (γ : Env m n) (σ : Ty (n + m)) → Env m (suc n)

tree : ∀ {m n} → Env m n → Ty (n + m) → Tree m
tree γ       ⊥             = ⊥
tree γ       ⊤             = ⊤
tree γ       (σ ⟶ τ)       = σ′ ⟶ τ′
                             where σ′ ~ ♯ tree γ σ; τ′ ~ ♯ tree γ τ
tree γ       (ν σ ⟶ τ)     = σ′ ⟶ τ′
                             where γ′ = γ ▻ ν σ ⟶ τ
                                   σ′ ~ ♯ tree γ′ σ; τ′ ~ ♯ tree γ′ τ
tree ∅       (var x)       = var x
tree (γ ▻ σ) (var zero)    = tree γ σ
tree (γ ▻ σ) (var (suc x)) = tree γ (var x)

⟦_⟧ : ∀ {n} → Ty n → Tree n
⟦ τ ⟧ = tree ∅ τ

------------------------------------------------------------------------
-- Example

inf : Ty 0
inf = ν var zero ⟶ var zero

infTree : Tree 0
infTree = ⟦ inf ⟧

------------------------------------------------------------------------
-- Subtyping defined in terms of finite approximations, following
-- Amadio and Cardelli (according to the paper)

data FinTree (n : ℕ) : Set where
  ⊥   : FinTree n
  ⊤   : FinTree n
  var : (x : Fin n) → FinTree n
  _⟶_ : (σ τ : FinTree n) → FinTree n

infix 8 _↑_ _↓_

mutual

  _↑_ : ∀ {n} → Tree n → ℕ → FinTree n
  τ     ↑ zero  = ⊤
  ⊥     ↑ suc k = ⊥
  ⊤     ↑ suc k = ⊤
  var x ↑ suc k = var x
  σ ⟶ τ ↑ suc k = (♭ σ ↓ k) ⟶ (♭ τ ↑ k)

  _↓_ : ∀ {n} → Tree n → ℕ → FinTree n
  τ     ↓ zero  = ⊥
  ⊥     ↓ suc k = ⊥
  ⊤     ↓ suc k = ⊤
  var x ↓ suc k = var x
  σ ⟶ τ ↓ suc k = (♭ σ ↑ k) ⟶ (♭ τ ↓ k)

-- I assume that there is no problem in forcing both sides to draw
-- variables from the same set.

infix 4 _≤Fin_ _≤↓_ _≤↑_ _≤AC_

data _≤Fin_ {n} : (σ τ : FinTree n) → Set where
  ⊥    : ∀ {τ} → ⊥ ≤Fin τ
  ⊤    : ∀ {σ} → σ ≤Fin ⊤
  refl : ∀ {τ} → τ ≤Fin τ
  _⟶_  : ∀ {σ₁ σ₂ τ₁ τ₂}
         (τ₁≤σ₁ : τ₁ ≤Fin σ₁) (σ₂≤τ₂ : σ₂ ≤Fin τ₂) →
         σ₁ ⟶ σ₂ ≤Fin τ₁ ⟶ τ₂

_≤↓_ : ∀ {n} (σ τ : Tree n) → Set
σ ≤↓ τ = ∀ k → σ ↓ k ≤Fin τ ↓ k

_≤↑_ : ∀ {n} (σ τ : Tree n) → Set
σ ≤↑ τ = ∀ k → σ ↑ k ≤Fin τ ↑ k

_≤AC_ : ∀ {n} (σ τ : Ty n) → Set
σ ≤AC τ = ⟦ σ ⟧ ≤↓ ⟦ τ ⟧

------------------------------------------------------------------------
-- Coinductive definition of equality and subtyping (mine)

-- The obvious definitions.

infix 4 _≈∞_ _≤∞_

data _≈∞_ {n} : (σ τ : Tree n) → Set where
  ⊥   : ⊥ ≈∞ ⊥
  ⊤   : ⊤ ≈∞ ⊤
  var : ∀ {x} → var x ≈∞ var x
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
        (σ₁≈τ₁ : ∞ (♭ σ₁ ≈∞ ♭ τ₁)) (σ₂≈τ₂ : ∞ (♭ σ₂ ≈∞ ♭ τ₂)) →
        σ₁ ⟶ σ₂ ≈∞ τ₁ ⟶ τ₂

data _≤∞_ {n} : (σ τ : Tree n) → Set where
  ⊥   : ∀ {τ} → ⊥ ≤∞ τ
  ⊤   : ∀ {σ} → σ ≤∞ ⊤
  var : ∀ {x} → var x ≤∞ var x
  _⟶_ : ∀ {σ₁ σ₂ τ₁ τ₂}
        (τ₁≤σ₁ : ∞ (♭ τ₁ ≤∞ ♭ σ₁)) (σ₂≤τ₂ : ∞ (♭ σ₂ ≤∞ ♭ τ₂)) →
        σ₁ ⟶ σ₂ ≤∞ τ₁ ⟶ τ₂

_≤Coind_ : ∀ {n} (σ τ : Ty n) → Set
σ ≤Coind τ = ⟦ σ ⟧ ≤∞ ⟦ τ ⟧

sym≈∞ : ∀ {n} {σ τ : Tree n} → σ ≈∞ τ → τ ≈∞ σ
sym≈∞ ⊥               = ⊥
sym≈∞ ⊤               = ⊤
sym≈∞ var             = var
sym≈∞ (σ₁≈τ₁ ⟶ σ₂≈τ₂) = sym≈∞₁ ⟶ sym≈∞₂
                        where sym≈∞₁ ~ ♯ sym≈∞ (♭ σ₁≈τ₁)
                              sym≈∞₂ ~ ♯ sym≈∞ (♭ σ₂≈τ₂)

refl≤∞ : ∀ {n} {σ τ : Tree n} → σ ≈∞ τ → σ ≤∞ τ
refl≤∞ ⊥               = ⊥
refl≤∞ ⊤               = ⊤
refl≤∞ var             = var
refl≤∞ (σ₁≈τ₁ ⟶ σ₂≈τ₂) = refl≤∞₁ ⟶ refl≤∞₂
                         where refl≤∞₁ ~ ♯ refl≤∞ (sym≈∞ (♭ σ₁≈τ₁))
                               refl≤∞₂ ~ ♯ refl≤∞ (♭ σ₂≈τ₂)

------------------------------------------------------------------------
-- Substitutions

-- Using Conor's trick.

module Subst (T : ℕ → Set)
             (vr : ∀ {n} → Fin n → T n)
             (wk : ∀ {n} → T n → T (suc n))
             (ty : ∀ {n} → T n → Ty n)
             (ty-vr : ∀ {n} (x : Fin n) → ty (vr x) ≡ var x)
             (wk-vr : ∀ {n} (x : Fin n) → wk (vr x) ≡ vr (suc x))
             where

  infixl 8 _/_
  infixl 9 _↑⋆_
  infix  9 _↑

  Sub : ℕ → ℕ → Set
  Sub m n = Vec (T n) m

  wkˢ : ∀ {m n} → Sub m n → Sub m (suc n)
  wkˢ = Vec.map wk

  wkⁿ : ∀ {m n} k → Sub m n → Sub m (k + n)
  wkⁿ zero    = id
  wkⁿ (suc k) = wkˢ ∘ wkⁿ k

  _↑ : ∀ {m n} → Sub m n → Sub (suc m) (suc n)
  ρ ↑ = vr zero ∷ wkˢ ρ

  _↑⋆_ : ∀ {i j n} → Sub (i + j) n → ∀ k → Sub (k + i + j) (k + n)
  ρ ↑⋆ zero  = ρ
  ρ ↑⋆ suc k = (ρ ↑⋆ k) ↑

  idˢ : ∀ {n} → Sub n n
  idˢ {zero}  = []
  idˢ {suc n} = idˢ ↑

  sub : ∀ {n} → T n → Sub (suc n) n
  sub t = t ∷ idˢ

  _/_ : ∀ {m n} → Ty m → Sub m n → Ty n
  ⊥       / ρ = ⊥
  ⊤       / ρ = ⊤
  var x   / ρ = ty (Vec.lookup x ρ)
  σ ⟶ τ   / ρ = (σ / ρ) ⟶ (τ / ρ)
  ν σ ⟶ τ / ρ = ν (σ / ρ ↑) ⟶ (τ / ρ ↑)

  weaken : ∀ {n} → Ty n → Ty (suc n)
  weaken τ = τ / wkˢ idˢ

  id-lemma′ : ∀ {n} (x : Fin n) → Vec.lookup x idˢ ≡ vr x
  id-lemma′ zero    = refl
  id-lemma′ (suc x) = begin
    Vec.lookup x (wkˢ idˢ)  ≡⟨ VecProp.lookup-natural wk x idˢ ⟩
    wk (Vec.lookup x idˢ)   ≡⟨ cong wk (id-lemma′ x) ⟩
    wk (vr x)               ≡⟨ wk-vr x ⟩
    vr (suc x)              ∎
    where open ≡-Reasoning

  id-lemma : ∀ {n} (τ : Ty n) → τ / idˢ ≡ τ
  id-lemma ⊥         = refl
  id-lemma ⊤         = refl
  id-lemma (σ ⟶ τ)   = cong₂ _⟶_  (id-lemma σ) (id-lemma τ)
  id-lemma (ν σ ⟶ τ) = cong₂ ν_⟶_ (id-lemma σ) (id-lemma τ)
  id-lemma (var x)   = begin
    ty (Vec.lookup x idˢ)  ≡⟨ cong ty (id-lemma′ x) ⟩
    ty (vr x)              ≡⟨ ty-vr x ⟩
    var x                  ∎
    where open ≡-Reasoning

  weaken-var : ∀ {n} (x : Fin n) → weaken (var x) ≡ var (suc x)
  weaken-var x = id-lemma (var (suc x))

module VarSubst     = Subst Fin id suc var (λ _ → refl) (λ _ → refl)
open module TySubst = Subst Ty var VarSubst.weaken id
                            (λ _ → refl) VarSubst.weaken-var

infix 8 _[0≔_]

_[0≔_] : ∀ {n} → Ty (suc n) → Ty n → Ty n
σ [0≔ τ ] = σ / sub τ

------------------------------------------------------------------------
-- Coinductive axiomatisation of subtyping

infix  4 _≤_
infixr 2 _≤⟨_⟩_
infix  2 _∎

data _≤_ {n} : (σ τ : Ty n) → Set where
  ⊥      : ∀ {τ} → ⊥ ≤ τ
  ⊤      : ∀ {σ} → σ ≤ ⊤
  var    : ∀ {x} → var x ≤ var x
  _⟶_    : ∀ {σ₁ σ₂ τ₁ τ₂}
           (τ₁≤σ₁ : ∞ (τ₁ ≤ σ₁)) (σ₂≤τ₂ : ∞ (σ₂ ≤ τ₂)) →
           σ₁ ⟶ σ₂ ≤ τ₁ ⟶ τ₂
  unfold : ∀ τ₁ τ₂ → let τ = ν τ₁ ⟶ τ₂ in
           τ ≤ (τ₁ [0≔ τ ]) ⟶ (τ₂ [0≔ τ ])
  fold   : ∀ τ₁ τ₂ → let τ = ν τ₁ ⟶ τ₂ in
           (τ₁ [0≔ τ ]) ⟶ (τ₂ [0≔ τ ]) ≤ τ
  _≤⟨_⟩_ : ∀ τ₁ {τ₂ τ₃ : Ty n}
           (τ₁≤τ₂ : τ₁ ≤ τ₂) (τ₂≤τ₃ : τ₂ ≤ τ₃) → τ₁ ≤ τ₃
  _∎     : (τ : Ty n) → τ ≤ τ

-- ν-cong : ∀ {n} {σ₁ σ₂ τ₁ τ₂ : Ty (suc n)} →
--          ∞ (τ₁ ≤ σ₁) → ∞ (σ₂ ≤ τ₂) → ν σ₁ ⟶ σ₂ ≤ ν τ₁ ⟶ τ₂
-- ν-cong {σ₁ = σ₁} {σ₂} {τ₁} {τ₂} τ₁≤σ₁ σ₂≤τ₂ =
--   σ                            ≤⟨ unfold σ₁ σ₂ ⟩
--   (σ₁ [0≔ σ ]) ⟶ (σ₂ [0≔ σ ])  ≤⟨ {!!} ⟶ {!!} ⟩
--   (τ₁ [0≔ τ ]) ⟶ (τ₂ [0≔ τ ])  ≤
--   τ                             ⟨ fold τ₁ τ₂ ⟩∎
--   where
--   σ = ν σ₁ ⟶ σ₂
--   τ = ν τ₁ ⟶ τ₂

--   infix 2 _≤_⟨_⟩∎

--   _≤_⟨_⟩∎ : ∀ {n} (τ₁ τ₂ : Ty n) → τ₁ ≤ τ₂ → τ₁ ≤ τ₂
--   _ ≤ _ ⟨ τ₁≤τ₂ ⟩∎ = τ₁≤τ₂

-- _∎ : ∀ {n} (τ : Ty n) → τ ≤ τ
-- ⊥       ∎ = ⊥
-- ⊤       ∎ = ⊤
-- var x   ∎ = var
-- σ ⟶ τ   ∎ = ♯ (σ ∎) ⟶ ♯ (τ ∎)
-- ν σ ⟶ τ ∎ = ν-cong (♯ (σ ∎)) (♯ (τ ∎))
