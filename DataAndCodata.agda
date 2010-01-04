------------------------------------------------------------------------
-- Data and codata can sometimes be "unified"
------------------------------------------------------------------------

-- In Haskell one can define the partial list type once, and define
-- map once and for all for this type. In Agda one typically defines
-- the (finite) list type + map and separately the (potentially
-- infinite) colist type + map. This is not strictly necessary,
-- though: the two types can be unified. The gain may be small,
-- though.

module DataAndCodata where

open import Coinduction
open import Function
open import Relation.Binary.PropositionalEquality

------------------------------------------------------------------------
-- Conditional coinduction

data Rec : Set where
  μ : Rec
  ν : Rec

∞? : Rec → Set → Set
∞? μ = id
∞? ν = ∞

♯? : ∀ (r : Rec) {A} → A → ∞? r A
♯? μ = id
♯? ν = ♯_

♭? : ∀ (r : Rec) {A} → ∞? r A → A
♭? μ = id
♭? ν = ♭

------------------------------------------------------------------------
-- A type for definitely finite or potentially infinite lists

-- If the Rec parameter is μ, then the type contains finite lists, and
-- otherwise it contains potentially infinite lists.

infixr 5 _∷_

data List∞? (r : Rec) (A : Set) : Set where
  []  : List∞? r A
  _∷_ : A → ∞? r (List∞? r A) → List∞? r A

-- List equality.

infix 4 _≈_

data _≈_ {r A} : List∞? r A → List∞? r A → Set where
  []  : [] ≈ []
  _∷_ : ∀ {x y xs ys} →
        x ≡ y → ∞? r (♭? r xs ≈ ♭? r ys) → x ∷ xs ≈ y ∷ ys

-- μ-lists can be seen as ν-lists.

lift : ∀ {A} → List∞? μ A → List∞? ν A
lift []       = []
lift (x ∷ xs) = x ∷ ♯ lift xs

------------------------------------------------------------------------
-- The map function

-- Maps over any list. The definition contains separate cases for _∷_
-- depending on whether the Rec index is μ or ν, though.

map : ∀ {r A B} → (A → B) → List∞? r A → List∞? r B
map     f []       = []
map {μ} f (x ∷ xs) = f x ∷ map f xs        -- Structural recursion
                                           -- (guarded).
map {ν} f (x ∷ xs) = f x ∷ ♯ map f (♭ xs)  -- Guarded corecursion.

-- In Haskell the map function is automatically (in effect) parametric
-- in the Rec parameter. Here this property is not automatic, so I
-- have proved it manually:

map-parametric : ∀ {A B} (f : A → B) (xs : List∞? μ A) →
                 map f (lift xs) ≈ lift (map f xs)
map-parametric f []       = []
map-parametric f (x ∷ xs) = refl ∷ ♯ map-parametric f xs
