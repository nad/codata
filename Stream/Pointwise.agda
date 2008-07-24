------------------------------------------------------------------------
-- Pointwise equalities can be lifted
------------------------------------------------------------------------

module Stream.Pointwise where

open import Stream
open import Stream.Equality
open import Data.Nat
open import Data.Fin
import Data.Vec as Vec
open Vec using (Vec; _∷_)
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Definitions

infix  8 _∞
infixl 7 _$_
infix  6 _⟨_⟩_

-- Expressions corresponding to pointwise definitions of streams.
-- Indexed on the number of variables.

data Pointwise A n : Set where
  var   : (x : Fin n) -> Pointwise A n
  _∞    : (x : A) -> Pointwise A n
  _$_   : (f : A -> A) (xs : Pointwise A n) -> Pointwise A n
  _⟨_⟩_ : (xs : Pointwise A n)
          (_∙_ : A -> A -> A)
          (ys : Pointwise A n) ->
          Pointwise A n

-- Stream semantics.

⟦_⟧ : forall {A n} -> Pointwise A n -> (Vec (Stream A) n -> Stream A)
⟦ var x ⟧         ρ = Vec.lookup x ρ
⟦ x ∞ ⟧           ρ = repeat x
⟦ f $ xs ⟧        ρ = map f (⟦ xs ⟧ ρ)
⟦ xs ⟨ _∙_ ⟩ ys ⟧ ρ = zipWith _∙_ (⟦ xs ⟧ ρ) (⟦ ys ⟧ ρ)

-- Pointwise semantics.

⟪_⟫ : forall {A n} -> Pointwise A n -> (Vec A n -> A)
⟪ var x ⟫         ρ = Vec.lookup x ρ
⟪ x ∞ ⟫           ρ = x
⟪ f $ xs ⟫        ρ = f (⟪ xs ⟫ ρ)
⟪ xs ⟨ _∙_ ⟩ ys ⟫ ρ = ⟪ xs ⟫ ρ ∙ ⟪ ys ⟫ ρ

------------------------------------------------------------------------
-- The two semantics above are related

private

  -- Lifts a pointwise function to a function on streams.

  lift : forall {A B n} ->
         (Vec A n -> B) -> Vec (Stream A) n -> Stream B
  lift f xs ~ f (Vec.map head xs) ≺ lift f (Vec.map tail xs)

  lift-cong : forall {A B n} {f g : Vec A n -> B} ->
              (forall ρ -> f ρ ≡ g ρ) ->
              forall ρ -> lift f ρ ≈ lift g ρ
  lift-cong hyp ρ ~
    hyp (Vec.map head ρ) ≺ lift-cong hyp (Vec.map tail ρ)

  lookup-map-lemma : forall {A B n} (f : A -> B) (x : Fin n) ρ ->
                     f (Vec.lookup x ρ) ≡ Vec.lookup x (Vec.map f ρ)
  lookup-map-lemma f zero    (x ∷ ρ) = ≡-refl
  lookup-map-lemma f (suc i) (x ∷ ρ) = lookup-map-lemma f i ρ

  η : forall {A} {xs : Stream A} -> xs ≡ head xs ≺ tail xs
  η {xs = x ≺ xs} = ≡-refl

  unfold : forall {A n} (xs : Pointwise A n) ρ ->
           ⟦ xs ⟧ ρ ≅ ⟪ xs ⟫ (Vec.map head ρ) ≺
                      ⟦ xs ⟧ (Vec.map tail ρ)
  unfold (var x) ρ ~
    Vec.lookup x ρ
      ≡⟨ η ⟩
    head (Vec.lookup x ρ) ≺ tail (Vec.lookup x ρ)
      ≡⟨ ≡-cong₂ _≺_ (lookup-map-lemma head x ρ)
                     (lookup-map-lemma tail x ρ) ⟩
    Vec.lookup x (Vec.map head ρ) ≺
    Vec.lookup x (Vec.map tail ρ)
      ∎
  unfold (x ∞) ρ ~
    repeat x
      ≡⟨ η ⟩
    x ≺ repeat x
      ∎
  unfold (f $ xs) ρ ~
    map f (⟦ xs ⟧ ρ)
      ≈⟨ map-cong f (unfold xs ρ) ⟩
    map f (⟪ xs ⟫ (Vec.map head ρ) ≺ ⟦ xs ⟧ (Vec.map tail ρ))
      ≡⟨ η ⟩
    f (⟪ xs ⟫ (Vec.map head ρ)) ≺ map f (⟦ xs ⟧ (Vec.map tail ρ))
      ∎
  unfold (xs ⟨ _∙_ ⟩ ys) ρ ~
    zipWith _∙_ (⟦ xs ⟧ ρ) (⟦ ys ⟧ ρ)
      ≈⟨ zipWith-cong _∙_ (unfold xs ρ) (unfold ys ρ) ⟩
    zipWith _∙_ (⟪ xs ⟫ (Vec.map head ρ) ≺ ⟦ xs ⟧ (Vec.map tail ρ))
                (⟪ ys ⟫ (Vec.map head ρ) ≺ ⟦ ys ⟧ (Vec.map tail ρ))
      ≡⟨ η ⟩
    ⟪ xs ⟫ (Vec.map head ρ) ∙ ⟪ ys ⟫ (Vec.map head ρ) ≺
    zipWith _∙_ (⟦ xs ⟧ (Vec.map tail ρ)) (⟦ ys ⟧ (Vec.map tail ρ))
      ∎

  main-lemma : forall {A n} (xs : Pointwise A n) ->
               forall ρ -> ⟦ xs ⟧ ρ ≅ lift ⟪ xs ⟫ ρ
  main-lemma xs ρ ~
    ⟦ xs ⟧ ρ
      ≈⟨ unfold xs ρ ⟩
    ⟪ xs ⟫ (Vec.map head ρ) ≺ ⟦ xs ⟧ (Vec.map tail ρ)
      ≈⟨ ↓ ≡-refl ≺ main-lemma xs (Vec.map tail ρ) ⟩
    lift ⟪ xs ⟫ ρ
      ∎

------------------------------------------------------------------------
-- To prove that two streams which are defined pointwise are equal, it
-- is enough to reason about a single (arbitrary) point

-- This function is a bit awkward to use, since the user has to come
-- up with a suitable environment manually. The alternative function
-- lift-pointwise below may be slightly easier to use.

lift-pointwise' : forall {A n} (xs ys : Pointwise A n) ->
                  (forall ρ -> ⟪ xs ⟫ ρ ≡ ⟪ ys ⟫ ρ) ->
                  (forall ρ -> ⟦ xs ⟧ ρ ≈ ⟦ ys ⟧ ρ)
lift-pointwise' xs ys hyp ρ = ≅⇒≈ (
  ⟦ xs ⟧ ρ
    ≈⟨ main-lemma xs ρ ⟩
  lift ⟪ xs ⟫ ρ
    ≈⟨ ≈⇒≅ (lift-cong hyp ρ) ⟩
  lift ⟪ ys ⟫ ρ
    ≈⟨ sym′ (main-lemma ys ρ) ⟩
  ⟦ ys ⟧ ρ
    ∎)

open import Data.Vec.N-ary

-- Applies the function to all possible variables.

app : forall {A} n ->
      N-ary n (Pointwise A n) (Pointwise A n) -> Pointwise A n
app n f = f $ⁿ Vec.map var (Vec.allFin n)

-- The type signature of this function may be a bit daunting, but once
-- n, f and g are instantiated with well-behaved concrete values the
-- remaining type evaluates nicely.

lift-pointwise
  : forall {A} n (f g : N-ary n (Pointwise A n) (Pointwise A n)) ->
    Eq n _≡_ (curryⁿ ⟪ app n f ⟫) (curryⁿ ⟪ app n g ⟫) ->
    Eq n _≈_ (curryⁿ ⟦ app n f ⟧) (curryⁿ ⟦ app n g ⟧)
lift-pointwise n f g hyp =
  curryⁿ-pres ⟦ app n f ⟧ ⟦ app n g ⟧
    (lift-pointwise' (app n f) (app n g)
      (curryⁿ-pres⁻¹ ⟪ app n f ⟫ ⟪ app n g ⟫ hyp))

------------------------------------------------------------------------
-- Some examples

private

  example₁ : map suc (repeat 0) ≈ repeat 1
  example₁ = lift-pointwise 0 (suc $ 0 ∞) (1 ∞) ≡-refl

  example₂ : forall xs -> map suc xs ≈ zipWith _+_ (repeat 1) xs
  example₂ = lift-pointwise 1 (\xs -> suc $ xs)
                              (\xs -> 1 ∞ ⟨ _+_ ⟩ xs)
                              (\x -> ≡-refl)

  open import Data.Nat.Properties
  open import Algebra.Structures

  example₃ : forall xs ys zs ->
             zipWith _+_ (zipWith _+_ xs ys) zs ≈
             zipWith _+_ xs (zipWith _+_ ys zs)
  example₃ = lift-pointwise 3 (\xs ys zs -> (xs ⟨ _+_ ⟩ ys) ⟨ _+_ ⟩ zs)
                              (\xs ys zs -> xs ⟨ _+_ ⟩ (ys ⟨ _+_ ⟩ zs))
                              (\x y z -> +-assoc x y z)
    where open IsCommutativeSemiring _ ℕ-isCommutativeSemiring
