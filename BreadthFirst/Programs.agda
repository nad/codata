------------------------------------------------------------------------
-- Programs used to define and specify breadth-first manipulations of
-- trees
------------------------------------------------------------------------

module BreadthFirst.Programs where

open import Coinduction
open import Data.List.NonEmpty
open import Data.Colist hiding ([_]; _++_)
open import Data.Product

open import BreadthFirst.Universe
open import Tree
open import Stream hiding (_++_)

infixr 5 _∷_ _≺_ _⊕⊕_
infixr 4 _,_
infix  3 ↓_

mutual

  -- The term WHNF is a bit of a misnomer here; only recursive
  -- /coinductive/ arguments are suspended (in the form of Progs).

  data WHNFν : U ν → Set1 where
    leaf   : ∀ {k} {a : U k} → WHNFν (tree a)
    node   : ∀ {k} {a : U k}
             (l : ∞₁ (Prog (tree a))) (x : WHNF a)
             (r : ∞₁ (Prog (tree a))) →
             WHNFν (tree a)
    _≺_    : ∀ {k} {a : U k}
             (x : WHNF a) (xs : ∞₁ (Prog (stream a))) → WHNFν (stream a)
    []     : ∀ {k} {a : U k} → WHNFν (colist a)
    _∷_    : ∀ {k} {a : U k}
             (x : WHNF a) (xs : ∞₁ (Prog (colist a))) → WHNFν (colist a)

  data WHNFμ : U μ → Set1 where
    _,_ : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
          (x : WHNF a) (y : WHNF b) → WHNFμ (a ⊗ b)
    ⌈_⌉ : ∀ {A} (x : A) → WHNFμ ⌈ A ⌉

  WHNF : ∀ {k} → U k → Set1
  WHNF {μ} a = WHNFμ a
  WHNF {ν} a = WHNFν a

  -- Note that higher-order functions are not handled well (see
  -- longZipWith): the arguments cannot be Progs, since this would
  -- make the type negative.

  data Prog : ∀ {k} → U k → Set1 where
    ↓_          : ∀ {k} {a : U k} (w : WHNF a) → Prog a
    lab         : ∀ {k} {a : U k} {B}
                  (t : Prog (tree a)) (lss : Prog (stream ⌈ Stream B ⌉)) →
                  Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
    fst         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) → Prog a
    snd         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) → Prog b
    longZipWith : ∀ {A}
                  (f : A → A → A) (xs ys : Prog (colist ⌈ A ⌉)) →
                  Prog (colist ⌈ A ⌉)
    flatten     : ∀ {A}
                  (t : Prog (tree ⌈ A ⌉)) → Prog (colist ⌈ List⁺ A ⌉)
    _⊕⊕_        : ∀ {k} {a : U k}
                  (xs ys : Prog (colist a)) → Prog (colist a)

infixl 9 _·_ _⊛_

_·_ : ∀ {A B} → (A → B) → WHNF ⌈ A ⌉ → WHNF ⌈ B ⌉
f · ⌈ x ⌉ = ⌈ f x ⌉

_⊛_ : ∀ {A B} → WHNF ⌈ (A → B) ⌉ → WHNF ⌈ A ⌉ → WHNF ⌈ B ⌉
⌈ f ⌉ ⊛ x = f · x

mutual

  ⇒W : ∀ {k} (a : U k) → El a → WHNF a
  ⇒W (tree a)   leaf         = leaf
  ⇒W (tree a)   (node l x r) = node l′ (⇒W a x) r′
                               where l′ ~ ♯₁ ⇒P (tree a) (♭ l)
                                     r′ ~ ♯₁ ⇒P (tree a) (♭ r)
  ⇒W (colist a) []           = []
  ⇒W (colist a) (x ∷ xs)     = ⇒W a x ∷ xs′ where xs′ ~ ♯₁ ⇒P (colist a) (♭ xs)
  ⇒W (stream a) (x ≺ xs)     = ⇒W a x ≺ xs′ where xs′ ~ ♯₁ ⇒P (stream a) (♭ xs)
  ⇒W (a ⊗ b)    (x , y)      = (⇒W a x , ⇒W b y)
  ⇒W ⌈ A ⌉      x            = ⌈ x ⌉

  ⇒P : ∀ {k} (a : U k) → El a → Prog a
  ⇒P a x = ↓ ⇒W a x

P⇒W : ∀ {k} {a : U k} → Prog a → WHNF a
P⇒W (↓ w) = w

P⇒W (longZipWith f xs ys) with P⇒W xs | P⇒W ys
... | x ∷ xs′ | y ∷ ys′ = f · x ⊛ y ∷ ♯₁ longZipWith f (♭₁ xs′) (♭₁ ys′)
... | xs′     | []      = xs′
... | []      | ys′     = ys′

P⇒W (flatten t) with P⇒W t
... | leaf       = []
... | node l x r = [_] · x ∷ ♯₁ longZipWith _++_ (flatten (♭₁ l))
                                                 (flatten (♭₁ r))

P⇒W (xs ⊕⊕ ys) with P⇒W xs
... | []      = P⇒W ys
... | x ∷ xs′ = x ∷ ♯₁ (♭₁ xs′ ⊕⊕ ys)

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).
P⇒W (lab t lss) with P⇒W t
... | leaf       = (leaf , P⇒W lss)
... | node l _ r with P⇒W lss
...              | ⌈ x ≺ ls ⌉ ≺ lss′ =
  ( node (♯₁ fst l′,lss″) ⌈ x ⌉ (♯₁ fst r′,lss‴)
  , ⌈ ♭ ls ⌉ ≺ (♯₁ snd r′,lss‴)
  )
  where
  l′,lss″ = lab (♭₁ l) (♭₁ lss′)
  r′,lss‴ = lab (♭₁ r) (snd l′,lss″)

-- Note: Sharing is lost here.
P⇒W (fst p) with P⇒W p
... | (x , y) = x
P⇒W (snd p) with P⇒W p
... | (x , y) = y

mutual

  W⇒ : ∀ {k} {a : U k} → WHNF a → El a
  W⇒ {ν} leaf         = leaf
  W⇒ {ν} (node l x r) = node l′ (W⇒ x) r′
                        where l′ ~ ♯ P⇒ (♭₁ l)
                              r′ ~ ♯ P⇒ (♭₁ r)
  W⇒ {ν} []           = []
  W⇒ {ν} (x ∷ xs)     = W⇒ x ∷ xs′ where xs′ ~ ♯ P⇒ (♭₁ xs)
  W⇒ {ν} (x ≺ xs)     = W⇒ x ≺ xs′ where xs′ ~ ♯ P⇒ (♭₁ xs)
  W⇒ {μ} (x , y)      = (W⇒ x , W⇒ y)
  W⇒ {μ} ⌈ x ⌉        = x

  P⇒ : ∀ {k} {a : U k} → Prog a → El a
  P⇒ p = W⇒ (P⇒W p)
