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

-- Program or WHNF?
--
-- The term WHNF is a bit of a misnomer here; only recursive
-- /coinductive/ arguments are suspended (in the form of programs).

data Kind : Set where
  p w : Kind

data ElP : Kind → U → Set₁ where
  leaf : ∀ {k a} → ElP k (tree a)
  node : ∀ {k a}
         (l : ∞ (ElP p (tree a))) (x : ElP k a)
         (r : ∞ (ElP p (tree a))) → ElP k (tree a)
  _∷_  : ∀ {k a}
         (x : ElP k a) (xs : ∞ (ElP p (stream a))) → ElP k (stream a)
  _,_  : ∀ {k a b} (x : ElP k a) (y : ElP k b) → ElP k (a ⊗ b)
  ⌈_⌉  : ∀ {k A} (x : A) → ElP k ⌈ A ⌉
  fst  : ∀ {a b} (t : ElP p (a ⊗ b)) → ElP p a
  snd  : ∀ {a b} (t : ElP p (a ⊗ b)) → ElP p b
  lab  : ∀ {A B} (t : Tree A) (bss : ElP p (stream ⌈ Stream B ⌉)) →
         ElP p (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)

fstW : ∀ {a b} → ElP w (a ⊗ b) → ElP w a
fstW (x , y) = x

sndW : ∀ {a b} → ElP w (a ⊗ b) → ElP w b
sndW (x , y) = y

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).

labW : ∀ {A B} → Tree A → ElP w (stream ⌈ Stream B ⌉) →
       ElP w (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
labW leaf         bss                = (leaf , bss)
labW (node l _ r) (⌈ b ∷ bs ⌉ ∷ bss) =
  (node (♯ fst x) ⌈ b ⌉ (♯ fst y) , ⌈ ♭ bs ⌉ ∷ ♯ snd y)
  where
  x = lab (♭ l) (♭ bss)
  y = lab (♭ r) (snd x)

whnf : ∀ {a} → ElP p a → ElP w a
whnf leaf         = leaf
whnf (node l x r) = node l (whnf x) r
whnf (x ∷ xs)     = whnf x ∷ xs
whnf (x , y)      = (whnf x , whnf y)
whnf ⌈ x ⌉        = ⌈ x ⌉
whnf (fst t)      = fstW (whnf t)
whnf (snd t)      = sndW (whnf t)
whnf (lab t bss)  = labW t (whnf bss)

mutual

  ⟦_⟧W : ∀ {a} → ElP w a → El a
  ⟦ leaf       ⟧W = leaf
  ⟦ node l x r ⟧W = node (♯ ⟦ ♭ l ⟧P) ⟦ x ⟧W (♯ ⟦ ♭ r ⟧P)
  ⟦ x ∷ xs     ⟧W = ⟦ x ⟧W ∷ ♯ ⟦ ♭ xs ⟧P
  ⟦ (x , y)    ⟧W = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦ ⌈ x ⌉      ⟧W = x

  ⟦_⟧P : ∀ {a} → ElP p a → El a
  ⟦ t ⟧P = ⟦ whnf t ⟧W

------------------------------------------------------------------------
-- Breadth-first labelling

label′ : ∀ {A B} → Tree A → Stream B →
         ElP p (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
label′ t bs = lab t (⌈ bs ⌉ ∷ ♯ snd (label′ t bs))

label : ∀ {A B} → Tree A → Stream B → Tree B
label t bs = ⟦ fst (label′ t bs) ⟧P
