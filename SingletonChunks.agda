------------------------------------------------------------------------
-- An implementation of the Fibonacci sequence using tail
------------------------------------------------------------------------

module SingletonChunks where

open import Codata.Musical.Notation
open import Codata.Musical.Stream as S using (Stream; _≈_; _∷_)
open import Data.Bool
open import Data.Nat
open import Data.Vec as V using (Vec; []; _∷_)
import Relation.Binary.PropositionalEquality as P

------------------------------------------------------------------------
-- Stream programs

-- StreamP b A encodes programs generating streams in chunks of size
-- (at least) 1. The first chunk may be empty if b is false.

infixr 5 _∷_

data StreamP : Bool → Set → Set₁ where
  [_]     : ∀ {A} (xs : ∞ (StreamP true A)) → StreamP false A
  _∷_     : ∀ {A} (x : A) (xs : StreamP false A) → StreamP true A
  forget  : ∀ {A} (xs : StreamP true A) → StreamP false A
  tail    : ∀ {A} (xs : StreamP true A) → StreamP false A
  zipWith : ∀ {b A B C} (f : A → B → C)
            (xs : StreamP b A) (ys : StreamP b B) → StreamP b C

data StreamW : Bool → Set → Set₁ where
  [_] : ∀ {A} (xs : StreamP true A) → StreamW false A
  _∷_ : ∀ {A} (x : A) (xs : StreamW false A) → StreamW true A

forgetW : ∀ {A} → StreamW true A → StreamW false A
forgetW (x ∷ [ xs ]) = [ x ∷ forget xs ]

tailW : ∀ {A} → StreamW true A → StreamW false A
tailW (x ∷ xs) = xs

zipWithW : ∀ {b A B C} → (A → B → C) →
           StreamW b A → StreamW b B → StreamW b C
zipWithW f [ xs ]   [ ys ]   = [ zipWith f xs ys ]
zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithW f xs ys

whnf : ∀ {b A} → StreamP b A → StreamW b A
whnf [ xs ]            = [ ♭ xs ]
whnf (x ∷ xs)          = x ∷ whnf xs
whnf (forget xs)       = forgetW (whnf xs)
whnf (tail xs)         = tailW (whnf xs)
whnf (zipWith f xs ys) = zipWithW f (whnf xs) (whnf ys)

mutual

  ⟦_⟧W : ∀ {A} → StreamW true A → Stream A
  ⟦ x ∷ [ xs ] ⟧W = x ∷ ♯ ⟦ xs ⟧P

  ⟦_⟧P : ∀ {A} → StreamP true A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- The Fibonacci sequence

fib : StreamP true ℕ
fib = 0 ∷ [ ♯ (1 ∷ zipWith _+_ (forget fib) (tail fib)) ]

------------------------------------------------------------------------
-- The definition of fib is correct

-- ⟦_⟧ is homomorphic with respect to zipWith/S.zipWith.

zipWith-hom : ∀ {A B C} (_∙_ : A → B → C) xs ys →
              ⟦ zipWith _∙_ xs ys ⟧P ≈ S.zipWith _∙_ ⟦ xs ⟧P ⟦ ys ⟧P
zipWith-hom _∙_ xs ys with whnf xs | whnf ys
zipWith-hom _∙_ xs ys | x ∷ [ xs′ ] | y ∷ [ ys′ ] =
  P.refl ∷ ♯ zipWith-hom _∙_ xs′ ys′

-- forget is the identity on streams.

open import MapIterate as M using (_≈P_; _∷_; _≈⟨_⟩_; _∎)
open import Relation.Binary.PropositionalEquality as P using (_≡_; [_])

forget-lemma : ∀ {A} x (xs : StreamP true A) →
               ⟦ x ∷ forget xs ⟧P ≈P x ∷ ♯ ⟦ xs ⟧P
forget-lemma x xs with whnf xs in eq
... | y ∷ [ ys ] = x ∷ ♯ helper eq
  where
  helper : whnf xs ≡ y ∷ [ ys ] →
           ⟦ y ∷ forget ys ⟧P ≈P ⟦ xs ⟧P
  helper eq rewrite eq = _ ≈⟨ forget-lemma y ys ⟩ (y ∷ ♯ (_ ∎))

-- The stream ⟦ fib ⟧P satisfies its intended defining equation.

open import Relation.Binary
module SS {A : Set} = Setoid (S.setoid A)

fib-correct :
  ⟦ fib ⟧P ≈ 0 ∷ ♯ (1 ∷ ♯ S.zipWith _+_ ⟦ fib ⟧P (S.tail ⟦ fib ⟧P))
fib-correct =
  P.refl ∷ ♯ (P.refl ∷ ♯ SS.trans
   (zipWith-hom _+_ (0 ∷ forget fib′) fib′)
   (S.zipWith-cong _+_ (SS.trans (M.soundP (forget-lemma 0 fib′))
                                 (P.refl ∷ ♯ SS.refl)) SS.refl))
  where fib′ = 1 ∷ zipWith _+_ (forget fib) (tail fib)

------------------------------------------------------------------------
-- An equality proof language

infix  4 _≈[_]P_ _≈[_]W_
infix  3 _∎
infixr 2 _≈⟨_⟩_

data _≈[_]P_ : {A : Set} → Stream A → Bool → Stream A → Set₁ where
  [_]     : ∀ {A} {xs ys : Stream A}
            (xs≈ys : ∞ (xs ≈[ true ]P ys)) → xs ≈[ false ]P ys
  _∷_     : ∀ {b A} (x : A) {xs ys : ∞ (Stream A)}
            (xs≈ys : ♭ xs ≈[ b ]P ♭ ys) → x ∷ xs ≈[ true ]P x ∷ ys
  forget  : ∀ {A} {xs ys : Stream A}
            (xs≈ys : xs ≈[ true ]P ys) → xs ≈[ false ]P ys
  _≈⟨_⟩_  : ∀ {b A} (xs : Stream A) {ys zs}
            (xs≈ys : xs ≈[ b ]P ys) (ys≈zs : ys ≈[ b ]P zs) →
            xs ≈[ b ]P zs
  _∎      : ∀ {A} (xs : Stream A) → xs ≈[ true ]P xs
  tail    : ∀ {A} {xs ys : Stream A} (xs≈ys : xs ≈[ true ]P ys) →
            S.tail xs ≈[ false ]P S.tail ys
  zipWith : ∀ {b A B C} (f : A → B → C) {xs xs′ ys ys′}
            (xs≈xs′ : xs ≈[ b ]P xs′) (ys≈ys′ : ys ≈[ b ]P ys′) →
            S.zipWith f xs ys ≈[ b ]P S.zipWith f xs′ ys′

-- Completeness.

completeP : ∀ {A : Set} {xs ys : Stream A} →
            xs ≈ ys → xs ≈[ true ]P ys
completeP (P.refl ∷ xs≈ys) = _ ∷ [ ♯ completeP (♭ xs≈ys) ]

-- Weak head normal forms.

data _≈[_]W_ {A : Set} : Stream A → Bool → Stream A → Set₁ where
  [_]     : {xs ys : Stream A}
            (xs≈ys : xs ≈[ true ]P ys) → xs ≈[ false ]W ys
  _∷_     : ∀ (x : A) {xs ys}
            (xs≈ys : ♭ xs ≈[ true ]P ♭ ys) → x ∷ xs ≈[ true ]W x ∷ ys

consW≈ : ∀ {A b} (x : A) {xs ys} →
         ♭ xs ≈[ b ]W ♭ ys → x ∷ xs ≈[ true ]W x ∷ ys
consW≈ x xs≈ys = x ∷ helper xs≈ys
  where
  helper : ∀ {A b} {xs ys : Stream A} →
           xs ≈[ b ]W ys → xs ≈[ true ]P ys
  helper [ xs≈ys ]   = xs≈ys
  helper (x ∷ xs≈ys) = x ∷ xs≈ys

forgetW≈ : ∀ {A} {xs ys : Stream A} →
           xs ≈[ true ]W ys → xs ≈[ false ]W ys
forgetW≈ (x ∷ xs≈ys) = [ x ∷ forget xs≈ys ]

transW≈ : ∀ {A b} {xs ys zs : Stream A} →
          xs ≈[ b ]W ys → ys ≈[ b ]W zs → xs ≈[ b ]W zs
transW≈ [ xs≈ys ]   [ ys≈zs ]    = [ _ ≈⟨ xs≈ys ⟩ ys≈zs ]
transW≈ (x ∷ xs≈ys) (.x ∷ ys≈zs) = x ∷ (_ ≈⟨ xs≈ys ⟩ ys≈zs)

reflW≈ : ∀ {A} (xs : Stream A) → xs ≈[ true ]W xs
reflW≈ (x ∷ xs) = x ∷ (♭ xs ∎)

tailW≈ : ∀ {A} {xs ys : Stream A} →
         xs ≈[ true ]W ys → S.tail xs ≈[ false ]W S.tail ys
tailW≈ (x ∷ xs≈ys) = [ xs≈ys ]

zipWithW≈ : ∀ {A B C b} (_∙_ : A → B → C) {xs₁ ys₁ xs₂ ys₂} →
            xs₁ ≈[ b ]W ys₁ → xs₂ ≈[ b ]W ys₂ →
            S.zipWith _∙_ xs₁ xs₂ ≈[ b ]W S.zipWith _∙_ ys₁ ys₂
zipWithW≈ _∙_ [ xs₁≈ys₁ ]    [ xs₂≈ys₂ ]    = [ zipWith _∙_ xs₁≈ys₁ xs₂≈ys₂ ]
zipWithW≈ _∙_ (x₁ ∷ xs₁≈ys₁) (x₂ ∷ xs₂≈ys₂) =
  (x₁ ∙ x₂) ∷ zipWith _∙_ xs₁≈ys₁ xs₂≈ys₂

whnf≈ : ∀ {A : Set} {xs ys : Stream A} {b} →
        xs ≈[ b ]P ys → xs ≈[ b ]W ys
whnf≈ [ xs≈ys ]                 = [ ♭ xs≈ys ]
whnf≈ (x ∷ xs≈ys)               = consW≈ x (whnf≈ xs≈ys)
whnf≈ (forget xs≈ys)            = forgetW≈ (whnf≈ xs≈ys)
whnf≈ (xs ≈⟨ xs≈ys ⟩ ys≈zs)     = transW≈ (whnf≈ xs≈ys) (whnf≈ ys≈zs)
whnf≈ (xs ∎)                    = reflW≈ xs
whnf≈ (tail xs≈ys)              = tailW≈ (whnf≈ xs≈ys)
whnf≈ (zipWith f xs≈xs′ ys≈ys′) = zipWithW≈ f (whnf≈ xs≈xs′) (whnf≈ ys≈ys′)

-- Soundness.

mutual

  soundW : {A : Set} {xs ys : Stream A} → xs ≈[ true ]W ys → xs ≈ ys
  soundW (x ∷ xs≈ys) = P.refl ∷ ♯ soundP xs≈ys

  soundP : {A : Set} {xs ys : Stream A} → xs ≈[ true ]P ys → xs ≈ ys
  soundP xs≈ys = soundW (whnf≈ xs≈ys)

------------------------------------------------------------------------
-- The equation given for fib has a unique solution

fib-rhs : Stream ℕ → Stream ℕ
fib-rhs ns = 0 ∷ ♯ (1 ∷ ♯ S.zipWith _+_ ns (S.tail ns))

fib-unique :
  ∀ ms ns → ms ≈ fib-rhs ms → ns ≈ fib-rhs ns → ms ≈[ true ]P ns
fib-unique ms ns ms≈ ns≈ =
  ms         ≈⟨ completeP ms≈ ⟩
  fib-rhs ms ≈⟨ 0 ∷ [ ♯ (1 ∷ zipWith _+_ (forget (fib-unique ms ns ms≈ ns≈))
                                         (tail (fib-unique ms ns ms≈ ns≈))) ] ⟩
  fib-rhs ns ≈⟨ completeP (SS.sym ns≈) ⟩
  ns         ∎
