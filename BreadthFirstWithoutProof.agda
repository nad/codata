------------------------------------------------------------------------
-- Breadth-first labelling of trees
------------------------------------------------------------------------

-- This module just defines breadth-first labelling. For a full
-- development including a specification and proof, see BreadthFirst.

module BreadthFirstWithoutProof where

open import Coinduction
open import Data.Product
open import Data.Stream

open import Tree using (Tree; leaf; node)

------------------------------------------------------------------------
-- Universe

data Kind : Set where
  μ : Kind -- Codata.
  ν : Kind -- Data.

data U : Kind → Set₁ where
  tree   : ∀ {k} (a : U k) → U ν
  stream : ∀ {k} (a : U k) → U ν
  _⊗_    : ∀ {k₁ k₂} (a : U k₁) (b : U k₂) → U μ
  ⌈_⌉    : (A : Set) → U μ

El : ∀ {k} → U k → Set
El (tree a)   = Tree.Tree (El a)
El (stream a) = Stream (El a)
El (a ⊗ b)    = El a × El b
El ⌈ A ⌉      = A

-- Conditional coinduction.

∞? : Kind → Set₁ → Set₁
∞? μ = λ A → A
∞? ν = ∞

♭? : ∀ k {A} → ∞? k A → A
♭? μ x = x
♭? ν x = ♭ x

------------------------------------------------------------------------
-- Programs

infixr 5 _∷_
infixr 4 _,_
infix  3 ↓_

mutual

  -- The term WHNF is a bit of a misnomer here; only recursive
  -- /coinductive/ arguments are suspended (in the form of programs).

  data ElW : ∀ {k} → U k → Set₁ where
    leaf : ∀ {k} {a : U k} → ElW (tree a)
    node : ∀ {k} {a : U k}
           (l : ElP (tree a)) (x : ElW a) (r : ElP (tree a)) →
           ElW (tree a)
    _∷_  : ∀ {k} {a : U k}
           (x : ElW a) (xs : ElP (stream a)) → ElW (stream a)
    _,_  : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
           (x : ElW a) (y : ElW b) → ElW (a ⊗ b)
    ⌈_⌉  : ∀ {A} (x : A) → ElW ⌈ A ⌉

  data ElP : ∀ {k} → U k → Set₁ where
    ↓_  : ∀ {k} {a : U k} (w : ∞? k (ElW a)) → ElP a
    fst : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
          (p : ElP (a ⊗ b)) → ElP a
    snd : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
          (p : ElP (a ⊗ b)) → ElP b
    lab : ∀ {A B} (t : Tree A) (lss : ElP (stream ⌈ Stream B ⌉)) →
          ElP (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)

fstW : ∀ {k₁ k₂} {a : U k₁} {b : U k₂} → ElW (a ⊗ b) → ElW a
fstW (x , y) = x

sndW : ∀ {k₁ k₂} {a : U k₁} {b : U k₂} → ElW (a ⊗ b) → ElW b
sndW (x , y) = y

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).

labW : ∀ {A B} → Tree A → ElW (stream ⌈ Stream B ⌉) →
       ElW (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
labW leaf         lss                = (leaf , lss)
labW (node l _ r) (⌈ x ∷ ls ⌉ ∷ lss) =
  (node (fst l′,lss′) ⌈ x ⌉ (fst r′,lss″) , ⌈ ♭ ls ⌉ ∷ snd r′,lss″)
  where
  l′,lss′ = lab (♭ l) lss
  r′,lss″ = lab (♭ r) (snd l′,lss′)

whnf : ∀ {k} {a : U k} → ElP a → ElW a
whnf (↓_ {k} w)  = ♭? k w
whnf (fst p)     = fstW (whnf p)
whnf (snd p)     = sndW (whnf p)
whnf (lab t lss) = labW t (whnf lss)

mutual

  ⟦_⟧W : ∀ {k} {a : U k} → ElW a → El a
  ⟦ leaf       ⟧W = leaf
  ⟦ node l x r ⟧W = node (♯ ⟦ l ⟧) ⟦ x ⟧W (♯ ⟦ r ⟧)
  ⟦ x ∷ xs     ⟧W = ⟦ x ⟧W ∷ ♯ ⟦ xs ⟧
  ⟦ (x , y)    ⟧W = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦ ⌈ x ⌉      ⟧W = x

  ⟦_⟧ : ∀ {k} {a : U k} → ElP a → El a
  ⟦ p ⟧ = ⟦ whnf p ⟧W

------------------------------------------------------------------------
-- Breadth-first labelling

label′ : ∀ {A B} → Tree A → Stream B →
         ElP (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
label′ t ls = lab t (↓ ♯ (⌈ ls ⌉ ∷ snd (label′ t ls)))

label : ∀ {A B} → Tree A → Stream B → Tree B
label t ls = ⟦ fst (label′ t ls) ⟧
