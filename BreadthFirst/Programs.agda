------------------------------------------------------------------------
-- Programs used to define and specify breadth-first manipulations of
-- trees
------------------------------------------------------------------------

module BreadthFirst.Programs where

open import Coinduction
open import Data.List.NonEmpty using (List⁺; [_]; _⁺++⁺_)
open import Data.Colist hiding ([_])
open import Data.Product

open import BreadthFirst.Universe
open import Tree
open import Stream hiding (zipWith)

infixr 5 _∷_ _≺_
infixr 4 _,_
infix  3 ↓_

mutual

  -- The term WHNF is a bit of a misnomer here; only recursive
  -- /coinductive/ arguments are suspended (in the form of Progs).

  data WHNF : ∀ {k} → U k → Set1 where
    leaf : ∀ {k} {a : U k} → WHNF (tree a)
    node : ∀ {k} {a : U k}
           (l : Prog (tree a)) (x : WHNF a) (r : Prog (tree a)) →
           WHNF (tree a)
    _≺_  : ∀ {k} {a : U k}
           (x : WHNF a) (xs : Prog (stream a)) → WHNF (stream a)
    []   : ∀ {k} {a : U k} → WHNF (colist a)
    _∷_  : ∀ {k} {a : U k}
           (x : WHNF a) (xs : Prog (colist a)) → WHNF (colist a)
    _,_  : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
           (x : WHNF a) (y : WHNF b) → WHNF (a ⊗ b)
    ⌈_⌉  : ∀ {A} (x : A) → WHNF ⌈ A ⌉

  -- Note that higher-order functions are not handled well (see
  -- longZipWith): the arguments cannot be Progs, since this would
  -- make the type negative.

  -- The tree arguments to lab and flatten used to be tree programs,
  -- but a number of lemmas could be removed when they were turned
  -- into "actual" trees.

  data Prog : ∀ {k} → U k → Set1 where
    ↓_          : ∀ {k} {a : U k} (w : ∞? k (WHNF a)) → Prog a
    fst         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) → Prog a
    snd         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) → Prog b
    lab         : ∀ {A B}
                  (t : Tree A) (lss : Prog (stream ⌈ Stream B ⌉)) →
                  Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
    longZipWith : ∀ {A}
                  (f : A → A → A) (xs ys : Prog (colist ⌈ A ⌉)) →
                  Prog (colist ⌈ A ⌉)
    flatten     : ∀ {A} (t : Tree A) → Prog (colist ⌈ List⁺ A ⌉)

infixl 9 _·_ _⊛_

_·_ : ∀ {A B} → (A → B) → WHNF ⌈ A ⌉ → WHNF ⌈ B ⌉
f · ⌈ x ⌉ = ⌈ f x ⌉

_⊛_ : ∀ {A B} → WHNF ⌈ (A → B) ⌉ → WHNF ⌈ A ⌉ → WHNF ⌈ B ⌉
⌈ f ⌉ ⊛ x = f · x

whnf : ∀ {k} {a : U k} → Prog a → WHNF a
whnf (↓_ {k} w) = ♭? k w

-- Note: Sharing is lost here.
whnf (fst p) with whnf p
... | (x , y) = x

whnf (snd p) with whnf p
... | (x , y) = y

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).
whnf (lab leaf         lss) = (leaf , whnf lss)
whnf (lab (node l _ r) lss) with whnf lss
... | ⌈ x ≺ ls ⌉ ≺ lss′ =
  (node (fst l′,lss″) ⌈ x ⌉ (fst r′,lss‴) , ⌈ ♭ ls ⌉ ≺ snd r′,lss‴)
  where
  l′,lss″ = lab (♭ l) lss′
  r′,lss‴ = lab (♭ r) (snd l′,lss″)

whnf (longZipWith f xs ys) with whnf xs | whnf ys
... | x ∷ xs′ | y ∷ ys′ = f · x ⊛ y ∷ longZipWith f xs′ ys′
... | xs′     | []      = xs′
... | []      | ys′     = ys′

whnf (flatten leaf)         = []
whnf (flatten (node l x r)) =
  ⌈ [ x ] ⌉ ∷ longZipWith _⁺++⁺_ (flatten (♭ l)) (flatten (♭ r))

mutual

  reflect : ∀ {k} {a : U k} → WHNF a → El a
  reflect {ν} leaf         = leaf
  reflect {ν} (node l x r) = node (♯ ⟦ l ⟧) (reflect x) (♯ ⟦ r ⟧)
  reflect {ν} []           = []
  reflect {ν} (x ∷ xs)     = reflect x ∷ ♯ ⟦ xs ⟧
  reflect {ν} (x ≺ xs)     = reflect x ≺ ♯ ⟦ xs ⟧
  reflect {μ} (x , y)      = (reflect x , reflect y)
  reflect {μ} ⌈ x ⌉        = x

  ⟦_⟧ : ∀ {k} {a : U k} → Prog a → El a
  ⟦ p ⟧ = reflect (whnf p)
