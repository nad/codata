------------------------------------------------------------------------
-- Pointwise equalities can be lifted
------------------------------------------------------------------------

module Stream.Pointwise where

open import Stream
open import Stream.Equality
open import Stream.Programs hiding (lift)
open import Data.Nat
open import Data.Fin
import Data.Vec  as Vec
import Data.Vec1 as Vec1
open Vec  using (Vec;  _∷_)
open Vec1 using (Vec₁; _∷_)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definitions

infix  8 _∞
infixl 7 _$_
infix  6 _⟨_⟩_

-- Expressions corresponding to pointwise definitions of streams.
-- Indexed on the number of variables.

-- It is possible to generalise this type, allowing variables to
-- correspond to streams containing elements of arbitrary type, and
-- letting the function arguments of _$_ and _⟨_⟩_ be more general.
-- However, this would complicate the development, so I hesitate to do
-- so without evidence that it would be genuinely useful.

data Pointwise A n : Set where
  var   : (x : Fin n) -> Pointwise A n
  _∞    : (x : A) -> Pointwise A n
  _$_   : (f : A -> A) (xs : Pointwise A n) -> Pointwise A n
  _⟨_⟩_ : (xs : Pointwise A n)
          (_∙_ : A -> A -> A)
          (ys : Pointwise A n) ->
          Pointwise A n

-- Stream semantics.

⟦_⟧ : forall {A n} ->
      Pointwise A n -> (Vec₁ (StreamProg A) n -> StreamProg A)
⟦ var x ⟧         ρ = Vec1.lookup x ρ
⟦ x ∞ ⟧           ρ = x ∞
⟦ f $ xs ⟧        ρ = f $ ⟦ xs ⟧ ρ
⟦ xs ⟨ _∙_ ⟩ ys ⟧ ρ = ⟦ xs ⟧ ρ ⟨ _∙_ ⟩ ⟦ ys ⟧ ρ

-- Pointwise semantics.

⟪_⟫ : forall {A n} -> Pointwise A n -> (Vec A n -> A)
⟪ var x ⟫         ρ = Vec.lookup x ρ
⟪ x ∞ ⟫           ρ = x
⟪ f $ xs ⟫        ρ = f (⟪ xs ⟫ ρ)
⟪ xs ⟨ _∙_ ⟩ ys ⟫ ρ = ⟪ xs ⟫ ρ ∙ ⟪ ys ⟫ ρ

------------------------------------------------------------------------
-- Some lemmas used below

private

  -- lookup is natural.

  lookup-nat : forall {A B n} (f : A -> B) (x : Fin n) ρ ->
               f (Vec1.lookup x ρ) ≡ Vec.lookup x (Vec1.map₁₀ f ρ)
  lookup-nat f zero    (x ∷ ρ) = ≡-refl
  lookup-nat f (suc i) (x ∷ ρ) = lookup-nat f i ρ

  lookup-nat' : forall {A B C n} (f : A -> C) (g : B -> C) (h : A -> B)
                (hyp : forall x -> f x ≡ g (h x)) (x : Fin n) ρ ->
                f (Vec1.lookup x ρ) ≡ g (Vec1.lookup x (Vec1.map h ρ))
  lookup-nat' f g h hyp zero    (x ∷ ρ) = hyp x
  lookup-nat' f g h hyp (suc i) (x ∷ ρ) =
    lookup-nat' f g h hyp i ρ

  -- tail(P) commutes with P⇒.

  tail-commutes : forall {A} (xs : StreamProg A) ->
                  tail (P⇒ xs) ≡ P⇒ (tailP xs)
  tail-commutes xs with P⇒′ xs
  tail-commutes xs | x ≺ xs′ = ≡-refl

------------------------------------------------------------------------
-- The two semantics above are related via the function lift

private

  -- Lifts a pointwise function to a function on stream programs.

  lift : forall {A B n} ->
         (Vec A n -> B) -> Vec₁ (StreamProg A) n -> StreamProg B
  lift f xs ~ ↓ f (Vec1.map₁₀ headP xs) ≺ lift f (Vec1.map tailP xs)

  -- lift is a congruence in its first argument.

  lift-cong : forall {A B n} {f g : Vec A n -> B} ->
              (forall ρ -> f ρ ≡ g ρ) ->
              forall ρ -> lift f ρ ≊ lift g ρ
  lift-cong hyp ρ ~
    ↓ hyp (Vec1.map₁₀ headP ρ) ≺ lift-cong hyp (Vec1.map tailP ρ)

  -- unfold xs ρ is the one-step unfolding of ⟦ xs ⟧ ρ. Note the
  -- similarity to lift.

  unfold : forall {A n} (xs : Pointwise A n) ρ -> StreamProg A
  unfold xs ρ = ↓ ⟪ xs ⟫ (Vec1.map₁₀ headP ρ) ≺
                  ⟦ xs ⟧ (Vec1.map   tailP ρ)

  unfold-lemma : forall {A n} (xs : Pointwise A n) ρ ->
                 ⟦ xs ⟧ ρ ≊ unfold xs ρ
  unfold-lemma (var x) ρ =
    Vec1.lookup x ρ
      ≣⟨ η ⟩
    headP (Vec1.lookup x ρ) ≺ tail (P⇒ (Vec1.lookup x ρ))
      ≡⟨ ≡-cong₂ _≺_ (lookup-nat headP x ρ)
                     (lookup-nat' (\xs -> tail (P⇒ xs)) P⇒ tailP
                                  tail-commutes x ρ) ⟩
    Vec.lookup x (Vec1.map₁₀ headP ρ) ≺
    P⇒ (Vec1.lookup x (Vec1.map tailP ρ))
      ≡⟨ ≡-sym η ⟩
    unfold (var x) ρ
      ▯
  unfold-lemma (x ∞)    ρ = x ∞ ▯
  unfold-lemma (f $ xs) ρ =
    f $ ⟦ xs ⟧ ρ
      ≊⟨ $-cong f (⟦ xs ⟧ ρ) (unfold xs ρ) (unfold-lemma xs ρ) ⟩
    f $ unfold xs ρ
      ▯
  unfold-lemma (xs ⟨ ∙ ⟩ ys) ρ =
    ⟦ xs ⟧ ρ ⟨ ∙ ⟩ ⟦ ys ⟧ ρ
      ≊⟨ ⟨ ∙ ⟩-cong (⟦ xs ⟧ ρ) (unfold xs ρ) (unfold-lemma xs ρ)
                    (⟦ ys ⟧ ρ) (unfold ys ρ) (unfold-lemma ys ρ) ⟩
    unfold xs ρ ⟨ ∙ ⟩ unfold ys ρ
      ▯

  -- The two semantics are related.

  main-lemma : forall {A n} (xs : Pointwise A n) ->
               forall ρ -> ⟦ xs ⟧ ρ ≊ lift ⟪ xs ⟫ ρ
  main-lemma xs ρ ~
    ⟦ xs ⟧ ρ
      ≊⟨ unfold-lemma xs ρ ⟩
    unfold xs ρ
      ≣⟨ η ⟩
    ⟪ xs ⟫ (Vec1.map₁₀ headP ρ) ≺ P⇒ (⟦ xs ⟧ (Vec1.map tailP ρ))
      ≅⟨ ↓ ≡-refl ≺ main-lemma xs (Vec1.map tailP ρ) ⟩
    lift ⟪ xs ⟫ ρ
      ▯

------------------------------------------------------------------------
-- To prove that two streams which are defined pointwise are equal, it
-- is enough to reason about a single (arbitrary) point

-- This function is a bit awkward to use, since the user has to come
-- up with a suitable environment manually. The alternative function
-- lift-pointwise below may be slightly easier to use.

pointwise' : forall {A n} (xs ys : Pointwise A n) ->
             (forall ρ -> ⟪ xs ⟫ ρ ≡ ⟪ ys ⟫ ρ) ->
             (forall ρ -> ⟦ xs ⟧ ρ ≊ ⟦ ys ⟧ ρ)
pointwise' xs ys hyp ρ =
  ⟦ xs ⟧ ρ
    ≊⟨ main-lemma xs ρ ⟩
  lift ⟪ xs ⟫ ρ
    ≊⟨ lift-cong hyp ρ ⟩
  lift ⟪ ys ⟫ ρ
    ≊⟨ ≅-sym (main-lemma ys ρ) ⟩
  ⟦ ys ⟧ ρ
    ▯

open import Data.Vec.N-ary
import Data.Vec.N-ary1 as N1

-- Applies the function to all possible variables.

app : forall {A} n ->
      N-ary n (Pointwise A n) (Pointwise A n) -> Pointwise A n
app n f = f $ⁿ Vec.map var (Vec.allFin n)

-- The type signature of this function may be a bit daunting, but once
-- n, f and g are instantiated with well-behaved concrete values the
-- remaining type evaluates nicely.

pointwise
  : forall {A} n (f g : N-ary n (Pointwise A n) (Pointwise A n)) ->
    Eq    n _≡_ (   curryⁿ ⟪ app n f ⟫) (   curryⁿ ⟪ app n g ⟫) ->
    N1.Eq n _≊_ (N1.curryⁿ ⟦ app n f ⟧) (N1.curryⁿ ⟦ app n g ⟧)
pointwise n f g hyp =
  N1.curryⁿ-pres ⟦ app n f ⟧ ⟦ app n g ⟧
    (pointwise' (app n f) (app n g)
      (curryⁿ-pres⁻¹ ⟪ app n f ⟫ ⟪ app n g ⟫ hyp))

------------------------------------------------------------------------
-- Some examples

private

  example₁ : suc $ 0 ∞ ≊ 1 ∞
  example₁ = pointwise 0 (suc $ 0 ∞) (1 ∞) ≡-refl

  example₂ : forall s -> suc $ s ≊ 1 ∞ ⟨ _+_ ⟩ s
  example₂ = pointwise 1 (\s -> suc $ s)
                         (\s -> 1 ∞ ⟨ _+_ ⟩ s)
                         (\_ -> ≡-refl)

  example₃ : forall s t u ->
             (s ⟨ _+_ ⟩ t) ⟨ _+_ ⟩ u ≊ s ⟨ _+_ ⟩ (t ⟨ _+_ ⟩ u)
  example₃ = pointwise 3 (\s t u -> (s ⟨ _+_ ⟩ t) ⟨ _+_ ⟩ u)
                         (\s t u ->  s ⟨ _+_ ⟩ (t ⟨ _+_ ⟩ u))
                         +-assoc
    where
    open import Data.Nat.Properties
    open import Algebra.Structures
    open IsCommutativeSemiring _ ℕ-isCommutativeSemiring
