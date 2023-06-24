------------------------------------------------------------------------
-- Yet another implementation of the Fibonacci sequence using tail
------------------------------------------------------------------------

module LargeCombinators where

open import Codata.Musical.Notation
open import Codata.Musical.Stream as S using (Stream; _∷_; _≈_)
open import Data.Nat
import Relation.Binary.PropositionalEquality as P

-- Stream programs. Note that the destructor tail is encapsulated in a
-- larger combinator, which also incorporates a constructor. This
-- ensures that the combinator can be used freely, with no risk of
-- destroying productivity.
--
-- Note that, in the general case, the implementation of whnf for the
-- "large combinator" may be quite tricky. In this case the
-- implementation turns out to be very simple, though.
--
-- The idea to use a "large combinator" is due to Thorsten Altenkirch.

infixr 5 _∷_

data StreamP (A : Set) : Set where
  _∷_     : (x : A) (xs : ∞ (StreamP A)) → StreamP A
  zipWith : (f : A → A → A) (xs ys : StreamP A) → StreamP A

  -- The intention is that ⟦ x ∷zipWith f · xs [tail ys ] ⟧P should be
  -- equal to x ∷ ♯ S.zipWith f ⟦ xs ⟧P (S.tail ⟦ ys ⟧P).

  _∷zipWith_·_[tail_] :
    (x : A) (f : A → A → A) (xs ys : StreamP A) → StreamP A

-- WHNFs.

data StreamW (A : Set) : Set where
  _∷_ : (x : A) (xs : StreamP A) → StreamW A

-- Stream programs can be turned into streams.

whnf : ∀ {A} → StreamP A → StreamW A
whnf (x ∷ xs) = x ∷ ♭ xs
whnf (x ∷zipWith f · xs′ [tail ys ]) with whnf ys
... | _ ∷ ys′ = x ∷ zipWith f xs′ ys′
whnf (zipWith f xs ys) with whnf xs | whnf ys
... | x ∷ xs′ | y ∷ ys′ = f x y ∷ zipWith f xs′ ys′

mutual

  ⟦_⟧W : ∀ {A} → StreamW A → Stream A
  ⟦ x ∷ xs ⟧W = x ∷ ♯ ⟦ xs ⟧P

  ⟦_⟧P : ∀ {A} → StreamP A → Stream A
  ⟦ xs ⟧P = ⟦ whnf xs ⟧W

-- The Fibonacci sequence.

fib : StreamP ℕ
fib = 0 ∷ ♯ (1 ∷zipWith _+_ · fib [tail fib ])

-- ⟦_⟧P is homomorphic with respect to zipWith/S.zipWith.

zipWith-hom :
  ∀ {A} (f : A → A → A) (xs ys : StreamP A) →
  ⟦ zipWith f xs ys ⟧P ≈ S.zipWith f ⟦ xs ⟧P ⟦ ys ⟧P
zipWith-hom f xs ys with whnf xs | whnf ys
... | x ∷ xs′ | y ∷ ys′ = P.refl ∷ ♯ zipWith-hom f xs′ ys′

-- The stream ⟦ fib ⟧P satisfies its intended defining equation.

fib-correct :
  ⟦ fib ⟧P ≈ 0 ∷ ♯ (1 ∷ ♯ (S.zipWith _+_ ⟦ fib ⟧P (S.tail ⟦ fib ⟧P)))
fib-correct =
  P.refl ∷ ♯ (P.refl ∷ ♯
    zipWith-hom _+_ fib (1 ∷zipWith _+_ · fib [tail fib ]))

-- For completeness, let us show that _∷zipWith_·_[tail_] is correctly
-- implemented.

open import Relation.Binary.PropositionalEquality as P using (_≡_; [_])

_∷zipWith_·_[tail_]-hom :
  ∀ {A} (x : A) (f : A → A → A) (xs ys : StreamP A) →
  ⟦ x ∷zipWith f · xs [tail ys ] ⟧P ≈
  x ∷ ♯ S.zipWith f ⟦ xs ⟧P (S.tail ⟦ ys ⟧P)
x ∷zipWith f · xs [tail ys ]-hom with whnf ys in eq
... | y ∷ ys′ = P.refl ∷ ♯ helper eq
  where
  helper : whnf ys ≡ y ∷ ys′ →
           ⟦ zipWith f xs ys′ ⟧P ≈
           S.zipWith f ⟦ xs ⟧P (S.tail ⟦ ys ⟧P)
  helper eq rewrite eq = zipWith-hom f xs ys′
