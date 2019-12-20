------------------------------------------------------------------------
-- Another implementation of the Fibonacci sequence using tail, along
-- with some other examples
------------------------------------------------------------------------

module ArbitraryChunks where

open import Codata.Musical.Notation
open import Codata.Musical.Stream as S using (Stream; _≈_; _∷_)
open import Data.Bool
open import Data.Nat
open import Data.Vec as V using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality as P
  using (_≡_; refl; [_])

------------------------------------------------------------------------
-- Stream programs

-- StreamP m n A encodes programs generating streams in chunks of size
-- (at least) m, where the first chunk has size (at least) n.

infixr 5 _∷_

data StreamP (m : ℕ) : ℕ → Set → Set₁ where
  [_]     : ∀ {A} (xs : ∞ (StreamP m m A)) → StreamP m 0 A
  _∷_     : ∀ {n A} (x : A) (xs : StreamP m n A) → StreamP m (suc n) A
  forget  : ∀ {n A} (xs : StreamP m (suc n) A) → StreamP m n A
  tail    : ∀ {n A} (xs : StreamP m (suc n) A) → StreamP m n A
  zipWith : ∀ {n A B C} (f : A → B → C)
            (xs : StreamP m n A) (ys : StreamP m n B) → StreamP m n C
  map     : ∀ {n A B} (f : A → B) (xs : StreamP m n A) → StreamP m n B

data StreamW (m : ℕ) : ℕ → Set → Set₁ where
  [_] : ∀ {A} (xs : StreamP m m A) → StreamW m 0 A
  _∷_ : ∀ {n A} (x : A) (xs : StreamW m n A) → StreamW m (suc n) A

forgetW : ∀ {m n A} → StreamW (suc m) (suc n) A → StreamW (suc m) n A
forgetW {n = zero}  (x ∷ [ xs ]) = [ x ∷ forget xs ]
forgetW {n = suc n} (x ∷ xs)     = x ∷ forgetW xs

tailW : ∀ {m n A} → StreamW m (suc n) A → StreamW m n A
tailW (x ∷ xs) = xs

zipWithW : ∀ {m n A B C} → (A → B → C) →
           StreamW m n A → StreamW m n B → StreamW m n C
zipWithW f [ xs ]   [ ys ]   = [ zipWith f xs ys ]
zipWithW f (x ∷ xs) (y ∷ ys) = f x y ∷ zipWithW f xs ys

mapW : ∀ {m n A B} → (A → B) → StreamW m n A → StreamW m n B
mapW f [ xs ]   = [ map f xs ]
mapW f (x ∷ xs) = f x ∷ mapW f xs

whnf : ∀ {m n A} → StreamP (suc m) n A → StreamW (suc m) n A
whnf [ xs ]            = [ ♭ xs ]
whnf (x ∷ xs)          = x ∷ whnf xs
whnf (forget xs)       = forgetW (whnf xs)
whnf (tail xs)         = tailW (whnf xs)
whnf (zipWith f xs ys) = zipWithW f (whnf xs) (whnf ys)
whnf (map f xs)        = mapW f (whnf xs)

mutual

  ⟦_⟧W : ∀ {m n A} → StreamW (suc m) (suc n) A → Stream A
  ⟦ x ∷ [ xs ]   ⟧W = x ∷ ♯ ⟦ xs ⟧P
  ⟦ x ∷ (y ∷ xs) ⟧W = x ∷ ♯ ⟦ y ∷ xs ⟧W

  ⟦_⟧P : ∀ {m n A} → StreamP (suc m) (suc n) A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

------------------------------------------------------------------------
-- Some examples

-- The Fibonacci sequence.

fib : StreamP 1 1 ℕ
fib = 0 ∷ [ ♯ (1 ∷ zipWith _+_ (forget fib) (tail fib)) ]

-- Some sequence which is defined using (tail ∘ tail).

someSequence : StreamP 2 2 ℕ
someSequence =
  0 ∷ 1 ∷ [ ♯ (1 ∷ 2 ∷ zipWith _+_ (tail (tail someSequence))
                                   (forget (forget someSequence))) ]

------------------------------------------------------------------------
-- The definition of fib is correct

-- ⟦_⟧ is homomorphic with respect to zipWith/S.zipWith.

mutual

  zipWithW-hom :
    ∀ {m n A B C} (_∙_ : A → B → C)
    (xs : StreamW (suc m) (suc n) A) ys →
    ⟦ zipWithW _∙_ xs ys ⟧W ≈ S.zipWith _∙_ ⟦ xs ⟧W ⟦ ys ⟧W
  zipWithW-hom _∙_ (x ∷ [ xs ]) (y ∷ [ ys ])   =
    refl ∷ ♯ zipWith-hom _∙_ xs ys
  zipWithW-hom _∙_ (x ∷ x′ ∷ xs) (y ∷ y′ ∷ ys) =
    refl ∷ ♯ zipWithW-hom _∙_ (x′ ∷ xs) (y′ ∷ ys)

  zipWith-hom : ∀ {m n A B C} (_∙_ : A → B → C)
                (xs : StreamP (suc m) (suc n) A) ys →
                ⟦ zipWith _∙_ xs ys ⟧P ≈ S.zipWith _∙_ ⟦ xs ⟧P ⟦ ys ⟧P
  zipWith-hom _∙_ xs ys = zipWithW-hom _∙_ (whnf xs) (whnf ys)

-- forget is the identity on streams.

open import MapIterate using (_≈P_; _∷_; _≈⟨_⟩_; _∎; soundP)

mutual

  forgetW-lemma : ∀ {m n A} x (xs : StreamW (suc m) (suc n) A) →
                  ⟦ x ∷ forgetW xs ⟧W ≈P x ∷ ♯ ⟦ xs ⟧W
  forgetW-lemma x (x′ ∷ [ xs ])  = x ∷ ♯ (_ ≈⟨ forget-lemma x′ xs ⟩ x′ ∷ ♯ (_ ∎))
  forgetW-lemma x (x′ ∷ x″ ∷ xs) = x ∷ ♯ (_ ≈⟨ forgetW-lemma x′ (x″ ∷ xs) ⟩ x′ ∷ ♯ (_ ∎) )

  forget-lemma : ∀ {m n A} x (xs : StreamP (suc m) (suc n) A) →
                 ⟦ x ∷ forget xs ⟧P ≈P x ∷ ♯ ⟦ xs ⟧P
  forget-lemma x xs with whnf xs | P.inspect whnf xs
  ... | y ∷ y′ ∷ ys | [ eq ] = x ∷ ♯ helper eq
    where
    helper : whnf xs ≡ y ∷ y′ ∷ ys →
             ⟦ y ∷ forgetW (y′ ∷ ys) ⟧W ≈P ⟦ xs ⟧P
    helper eq rewrite eq = _ ≈⟨ forgetW-lemma y (y′ ∷ ys) ⟩ y ∷ ♯ (_ ∎)
  ... | y ∷ [ ys ]  | [ eq ] = x ∷ ♯ helper eq
    where
    helper : whnf xs ≡ y ∷ [ ys ] →
             ⟦ y ∷ forget ys ⟧P ≈P ⟦ xs ⟧P
    helper eq rewrite eq = _ ≈⟨ forget-lemma y ys ⟩ y ∷ ♯ (_ ∎)

-- The stream ⟦ fib ⟧P satisfies its intended defining equation.

open import Relation.Binary
module SS {A : Set} = Setoid (S.setoid A)

fib-correct :
  ⟦ fib ⟧P ≈ 0 ∷ ♯ (1 ∷ ♯ S.zipWith _+_ ⟦ fib ⟧P (S.tail ⟦ fib ⟧P))
fib-correct =
  refl ∷ ♯ (refl ∷ ♯ SS.trans
    (zipWith-hom _+_ (0 ∷ forget fib′) fib′)
    (S.zipWith-cong _+_ (SS.trans (soundP (forget-lemma 0 fib′))
                                  (refl ∷ ♯ SS.refl)) SS.refl))
  where fib′ = 1 ∷ zipWith _+_ (forget fib) (tail fib)

------------------------------------------------------------------------
-- map₂

-- A variant of S.map which processes streams in chunks of size 2.

map₂ : {A B : Set} → (A → B) → Stream A → Stream B
map₂ f (x ∷ xs) with ♭ xs
map₂ f (x ∷ xs) | y ∷ ys = f x ∷ ♯ (f y ∷ ♯ map₂ f (♭ ys))

-- This function is extensionally equal to S.map.

map≈map₂ : ∀ {A B} →
           (f : A → B) → (xs : Stream A) → S.map f xs ≈ map₂ f xs
map≈map₂ f (x ∷ xs) with ♭ xs | P.inspect ♭ xs
map≈map₂ f (x ∷ xs) | y ∷ ys | [ eq ] = refl ∷ ♯ helper eq
  where
  map-f-y∷ys = _

  helper : ∀ {xs} → xs ≡ y ∷ ys → S.map f xs ≈ map-f-y∷ys
  helper refl = refl ∷ ♯ map≈map₂ f (♭ ys)

-- However, as explained in "Beating the Productivity Checker Using
-- Embedded Languages", the two functions are not interchangeable
-- (assuming that pattern matching is evaluated strictly). Let us see
-- what happens when we use the language above. We can define the
-- stream of natural numbers using chunks of size 1 and 2.

nats : StreamP 1 1 ℕ
nats = 0 ∷ [ ♯ map suc nats ]

nats₂ : StreamP 2 2 ℕ
nats₂ = 0 ∷ 1 ∷ [ ♯ map suc nats₂ ]

-- The first use of map corresponds to S.map, and the second to map₂.
-- If we try to use map₂ in the first definition, then we get a type
-- error. The following code is not accepted.

-- nats : StreamP 2 1 ℕ
-- nats = 0 ∷ [ ♯ map suc nats ]
