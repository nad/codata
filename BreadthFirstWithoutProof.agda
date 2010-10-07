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

data U : Set₁ where
  tree   : (a : U) → U
  stream : (a : U) → U
  _⊗_    : (a b : U) → U
  ⌈_⌉    : (A : Set) → U

El : U → Set
El (tree a)   = Tree (El a)
El (stream a) = Stream (El a)
El (a ⊗ b)    = El a × El b
El ⌈ A ⌉      = A

------------------------------------------------------------------------
-- Programs

infixr 5 _∷_
infixr 4 _,_

mutual

  data ElP : U → Set₁ where
    ↓   : ∀ {a} (w : ElW a) → ElP a
    fst : ∀ {a b} (p : ElP (a ⊗ b)) → ElP a
    snd : ∀ {a b} (p : ElP (a ⊗ b)) → ElP b
    lab : ∀ {A B} (t : Tree A) (bss : ElP (stream ⌈ Stream B ⌉)) →
          ElP (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)

  -- The term WHNF is a bit of a misnomer here; only recursive
  -- /coinductive/ arguments are suspended (in the form of programs).

  data ElW : U → Set₁ where
    leaf : ∀ {a} → ElW (tree a)
    node : ∀ {a}
           (l : ∞ (ElP (tree a))) (x : ElW a) (r : ∞ (ElP (tree a))) →
           ElW (tree a)
    _∷_  : ∀ {a} (x : ElW a) (xs : ∞ (ElP (stream a))) → ElW (stream a)
    _,_  : ∀ {a b} (x : ElW a) (y : ElW b) → ElW (a ⊗ b)
    ⌈_⌉  : ∀ {A} (x : A) → ElW ⌈ A ⌉

fstW : ∀ {a b} → ElW (a ⊗ b) → ElW a
fstW (x , y) = x

sndW : ∀ {a b} → ElW (a ⊗ b) → ElW b
sndW (x , y) = y

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).

labW : ∀ {A B} → Tree A → ElW (stream ⌈ Stream B ⌉) →
       ElW (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
labW leaf         bss                = (leaf , bss)
labW (node l _ r) (⌈ b ∷ bs ⌉ ∷ bss) =
  (node (♯ fst x) ⌈ b ⌉ (♯ fst y) , ⌈ ♭ bs ⌉ ∷ ♯ snd y)
  where
  x = lab (♭ l) (♭ bss)
  y = lab (♭ r) (snd x)

whnf : ∀ {a} → ElP a → ElW a
whnf (↓ w)       = w
whnf (fst p)     = fstW (whnf p)
whnf (snd p)     = sndW (whnf p)
whnf (lab t bss) = labW t (whnf bss)

mutual

  ⟦_⟧W : ∀ {a} → ElW a → El a
  ⟦ leaf       ⟧W = leaf
  ⟦ node l x r ⟧W = node (♯ ⟦ ♭ l ⟧P) ⟦ x ⟧W (♯ ⟦ ♭ r ⟧P)
  ⟦ x ∷ xs     ⟧W = ⟦ x ⟧W ∷ ♯ ⟦ ♭ xs ⟧P
  ⟦ (x , y)    ⟧W = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦ ⌈ x ⌉      ⟧W = x

  ⟦_⟧P : ∀ {a} → ElP a → El a
  ⟦ p ⟧P = ⟦ whnf p ⟧W

------------------------------------------------------------------------
-- Breadth-first labelling

label′ : ∀ {A B} → Tree A → Stream B →
         ElP (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
label′ t bs = lab t (↓ (⌈ bs ⌉ ∷ ♯ snd (label′ t bs)))

label : ∀ {A B} → Tree A → Stream B → Tree B
label t bs = ⟦ fst (label′ t bs) ⟧P
