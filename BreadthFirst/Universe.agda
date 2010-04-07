------------------------------------------------------------------------
-- The universe used to define breadth-first manipulations of trees
------------------------------------------------------------------------

module BreadthFirst.Universe where

open import Data.Product using (_×_; _,_)
open import Data.Colist using (Colist; []; _∷_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Coinduction

open import Stream using (Stream; _≺_)
open import Tree using (Tree; node; leaf)

infixr 5 _≺_ _∷_
infixr 4 _,_
infixr 2 _⊗_

data U : Set₁ where
  tree   : (a : U) → U
  stream : (a : U) → U
  colist : (a : U) → U
  _⊗_    : (a b : U) → U
  ⌈_⌉    : (A : Set) → U

El : U → Set
El (tree a)   = Tree.Tree (El a)
El (stream a) = Stream (El a)
El (colist a) = Colist (El a)
El (a ⊗ b)    = El a × El b
El ⌈ A ⌉      = A

-- Equality.

data Eq : ∀ a → El a → El a → Set₁ where
  leaf : ∀ {a} → Eq (tree a) leaf leaf
  node : ∀ {a x x′ l l′ r r′}
         (l≈l′ : ∞ (Eq (tree a) (♭ l) (♭ l′)))
         (x≈x′ :    Eq a        x     x′     )
         (r≈r′ : ∞ (Eq (tree a) (♭ r) (♭ r′))) →
         Eq (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {a x x′ xs xs′}
         (x≈x′   :    Eq a              x      x′  )
         (xs≈xs′ : ∞ (Eq (stream a) (♭ xs) (♭ xs′))) →
         Eq (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {a} → Eq (colist a) [] []
  _∷_  : ∀ {a x x′ xs xs′}
         (x≈x′   :    Eq a              x      x′  )
         (xs≈xs′ : ∞ (Eq (colist a) (♭ xs) (♭ xs′))) →
         Eq (colist a) (x ∷ xs) (x′ ∷ xs′)
  _,_  : ∀ {a b x x′ y y′}
         (x≈x′ : Eq a x x′) (y≈y′ : Eq b y y′) →
         Eq (a ⊗ b) (x , y) (x′ , y′)
  ⌈_⌉  : ∀ {A} {x x′} (x≡x′ : x ≡ x′) → Eq ⌈ A ⌉ x x′

-- PrefixOf a xs ys is inhabited iff xs is a prefix of ys.

data PrefixOf (a : U) : Colist (El a) → Stream (El a) → Set₁ where
  []  : ∀ {ys} → PrefixOf a [] ys
  _∷_ : ∀ {x y xs ys}
        (x≈y : Eq a x y) (p : ∞ (PrefixOf a (♭ xs) (♭ ys))) →
        PrefixOf a (x ∷ xs) (y ≺ ys)
