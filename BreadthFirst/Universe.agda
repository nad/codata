------------------------------------------------------------------------
-- The universe used to define breadth-first manipulations of trees
------------------------------------------------------------------------

module BreadthFirst.Universe where

open import Data.Product using (_×_; _,_)
open import Data.Colist  using (Colist; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Coinduction

open import Tree   using (Tree; node; leaf)
open import Stream using (Stream; _≺_)

infixr 5 _≺_ _∷_
infixr 4 _,_
infixr 2 _⊗_

-- Universe.

data Kind : Set where
  μ : Kind -- Codata.
  ν : Kind -- Data.

data U : Kind → Set1 where
  tree   : ∀ {k} (a : U k) → U ν
  stream : ∀ {k} (a : U k) → U ν
  colist : ∀ {k} (a : U k) → U ν
  _⊗_    : ∀ {k₁ k₂} (a : U k₁) (b : U k₂) → U μ
  ⌈_⌉    : (A : Set) → U μ

El : ∀ {k} → U k → Set
El (tree a)   = Tree.Tree (El a)
El (stream a) = Stream.Stream (El a)
El (colist a) = Colist (El a)
El (a ⊗ b)    = El a × El b
El ⌈ A ⌉      = A

-- Equality.

data Eq : ∀ {k} (a : U k) → El a → El a → Set1 where
  leaf : ∀ {k} {a : U k} → Eq (tree a) leaf leaf
  node : ∀ {k} {a : U k} {x x′ l l′ r r′}
         (l≈l′ : ∞₁ (Eq (tree a) (♭ l) (♭ l′)))
         (x≈x′ :     Eq a        x     x′     )
         (r≈r′ : ∞₁ (Eq (tree a) (♭ r) (♭ r′))) →
         Eq (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   :     Eq a              x      x′  )
         (xs≈xs′ : ∞₁ (Eq (stream a) (♭ xs) (♭ xs′))) →
         Eq (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {k} {a : U k} → Eq (colist a) [] []
  _∷_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   :     Eq a              x      x′  )
         (xs≈xs′ : ∞₁ (Eq (colist a) (♭ xs) (♭ xs′))) →
         Eq (colist a) (x ∷ xs) (x′ ∷ xs′)
  _,_  : ∀ {k₁ k₂} {a : U k₁} {b : U k₂} {x x′ y y′}
         (x≈x′ : Eq a x x′) (y≈y′ : Eq b y y′) →
         Eq (a ⊗ b) (x , y) (x′ , y′)
  ⌈_⌉  : ∀ {A} {x x′} (x≡x′ : x ≡ x′) → Eq ⌈ A ⌉ x x′

-- PrefixOf a xs ys is inhabited iff xs is a prefix of ys.

data PrefixOf {k} (a : U k) : Colist (El a) → Stream (El a) → Set1 where
  []  : ∀ {ys} → PrefixOf a [] ys
  _∷_ : ∀ {x y xs ys}
        (x≈y : Eq a x y) (p : ∞₁ (PrefixOf a (♭ xs) (♭ ys))) →
        PrefixOf a (x ∷ xs) (y ≺ ys)

-- Conditional coinduction.

∞? : Kind → Set1 → Set1
∞? μ = λ A → A
∞? ν = ∞₁

♭? : ∀ k {A} → ∞? k A → A
♭? μ x = x
♭? ν x = ♭₁ x
