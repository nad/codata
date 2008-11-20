------------------------------------------------------------------------
-- Programs used to define and specify breadth-first manipulations of
-- trees
------------------------------------------------------------------------

module BreadthFirst.Programs where

open import Data.List.NonEmpty
open import Data.Colist hiding (_++_)
open import Data.Product

open import BreadthFirst.Universe
open import Tree
open import Stream

infixr 5 _∷_ _≺_ _⊕⊕_
infixr 4 _,_
infix  3 ↓_

mutual

  -- The term WHNF is a bit of a misnomer here; only recursive
  -- /coinductive/ arguments are suspended (in the form of Progs).

  codata WHNFν : U ν -> Set1 where
    leaf   : forall {k} {a : U k} -> WHNFν (tree a)
    node   : forall {k} {a : U k}
             (l : Prog (tree a)) (x : WHNF a) (r : Prog (tree a)) ->
             WHNFν (tree a)
    _≺_    : forall {k} {a : U k}
             (x : WHNF a) (xs : Prog (stream a)) -> WHNFν (stream a)
    []     : forall {k} {a : U k} -> WHNFν (colist a)
    _∷_    : forall {k} {a : U k}
             (x : WHNF a) (xs : Prog (colist a)) -> WHNFν (colist a)

  data WHNFμ : U μ -> Set1 where
    _,_ : forall {k₁ k₂} {a : U k₁} {b : U k₂}
          (x : WHNF a) (y : WHNF b) -> WHNFμ (a ⊗ b)
    ⌈_⌉ : forall {A} (x : A) -> WHNFμ ⌈ A ⌉

  WHNF : forall {k} -> U k -> Set1
  WHNF {μ} a = WHNFμ a
  WHNF {ν} a = WHNFν a

  -- Note that higher-order functions are not handled well (see
  -- longZipWith): the arguments cannot be Progs, since this would
  -- make the type negative.

  data Prog : forall {k} -> U k -> Set1 where
    ↓_          : forall {k} {a : U k} (w : WHNF a) -> Prog a
    lab         : forall {k} {a : U k} {B}
                  (t : Prog (tree a)) (lss : Prog (stream ⌈ Stream B ⌉)) ->
                  Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
    fst         : forall {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) -> Prog a
    snd         : forall {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) -> Prog b
    longZipWith : forall {A}
                  (f : A -> A -> A) (xs ys : Prog (colist ⌈ A ⌉)) ->
                  Prog (colist ⌈ A ⌉)
    flatten     : forall {A}
                  (t : Prog (tree ⌈ A ⌉)) -> Prog (colist ⌈ List⁺ A ⌉)
    _⊕⊕_        : forall {k} {a : U k}
                  (xs ys : Prog (colist a)) -> Prog (colist a)

infixl 9 _·_ _⊛_

_·_ : forall {A B} -> (A -> B) -> WHNF ⌈ A ⌉ -> WHNF ⌈ B ⌉
f · ⌈ x ⌉ = ⌈ f x ⌉

_⊛_ : forall {A B} -> WHNF ⌈ (A -> B) ⌉ -> WHNF ⌈ A ⌉ -> WHNF ⌈ B ⌉
⌈ f ⌉ ⊛ x = f · x

⇒W : forall {k} (a : U k) -> El a -> WHNF a
⇒W (tree a)   (tree leaf)         ~ leaf
⇒W (tree a)   (tree (node l x r)) ~ node (↓ ⇒W (tree a) l) (⇒W a x)
                                         (↓ ⇒W (tree a) r)
⇒W (colist a) []                  ~ []
⇒W (colist a) (x ∷ xs)            ~ (⇒W a x) ∷ (↓ ⇒W (colist a) xs)
⇒W (stream a) (x ≺ xs)            ~ (⇒W a x) ≺ (↓ ⇒W (stream a) xs)
⇒W (a ⊗ b)    (x , y)             ~ (⇒W a x , ⇒W b y)
⇒W ⌈ A ⌉      x                   ~ ⌈ x ⌉

⇒P : forall {k} (a : U k) -> El a -> Prog a
⇒P a x = ↓ ⇒W a x

P⇒W : forall {k} {a : U k} -> Prog a -> WHNF a
P⇒W (↓ w) = w

P⇒W (longZipWith f xs ys) with P⇒W xs | P⇒W ys
... | x ∷ xs′ | y ∷ ys′ = f · x ⊛ y ∷ longZipWith f xs′ ys′
... | xs′     | []      = xs′
... | []      | ys′     = ys′

P⇒W (flatten t) with P⇒W t
... | leaf       = []
... | node l x r = [_] · x ∷ longZipWith _++_ (flatten l) (flatten r)

P⇒W (xs ⊕⊕ ys) with P⇒W xs
... | []      = P⇒W ys
... | x ∷ xs′ = x ∷ xs′ ⊕⊕ ys

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).
P⇒W (lab t lss) with P⇒W t
... | leaf       = (leaf , P⇒W lss)
... | node l _ r with P⇒W lss
...              | ⌈ x ≺ ls ⌉ ≺ lss′ =
  (node (fst l′,lss″) ⌈ x ⌉ (fst r′,lss‴) , ⌈ ls ⌉ ≺ (snd r′,lss‴))
  where
  l′,lss″ = lab l lss′
  r′,lss‴ = lab r (snd l′,lss″)

-- Note: Sharing is lost here.
P⇒W (fst p) with P⇒W p
... | (x , y) = x
P⇒W (snd p) with P⇒W p
... | (x , y) = y

W⇒ : forall {k} {a : U k} -> WHNF a -> El a
W⇒ {ν} leaf         ~ tree leaf
W⇒ {ν} (node l x r) ~ tree (node (W⇒ (P⇒W l)) (W⇒ x) (W⇒ (P⇒W r)))
W⇒ {ν} []           ~ []
W⇒ {ν} (x ∷ xs)     ~ W⇒ x ∷ W⇒ (P⇒W xs)
W⇒ {ν} (x ≺ xs)     ~ W⇒ x ≺ W⇒ (P⇒W xs)
W⇒ {μ} (x , y)      ~ (W⇒ x , W⇒ y)
W⇒ {μ} ⌈ x ⌉        ~ x

P⇒ : forall {k} {a : U k} -> Prog a -> El a
P⇒ p = W⇒ (P⇒W p)
