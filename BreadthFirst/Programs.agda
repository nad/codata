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
open import Stream hiding (zipWith)
open import Tree

infixr 5 _≺_ _∷_
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
    _≺_  : ∀ {k} {a : U k}
           (x : ElW a) (xs : ElP (stream a)) → ElW (stream a)
    []   : ∀ {k} {a : U k} → ElW (colist a)
    _∷_  : ∀ {k} {a : U k}
           (x : ElW a) (xs : ElP (colist a)) → ElW (colist a)
    _,_  : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
           (x : ElW a) (y : ElW b) → ElW (a ⊗ b)
    ⌈_⌉  : ∀ {A} (x : A) → ElW ⌈ A ⌉

  -- Note that higher-order functions are not handled well (see
  -- longZipWith): the arguments cannot be programs, since this would
  -- make the type negative.

  -- The tree arguments to lab and flatten used to be tree programs,
  -- but a number of lemmas could be removed when they were turned
  -- into "actual" trees.

  data ElP : ∀ {k} → U k → Set₁ where
    ↓_          : ∀ {k} {a : U k} (w : ∞? k (ElW a)) → ElP a
    fst         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : ElP (a ⊗ b)) → ElP a
    snd         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : ElP (a ⊗ b)) → ElP b
    lab         : ∀ {A B}
                  (t : Tree A) (lss : ElP (stream ⌈ Stream B ⌉)) →
                  ElP (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
    longZipWith : ∀ {A} (f : A → A → A) (xs ys : ElP (colist ⌈ A ⌉)) →
                  ElP (colist ⌈ A ⌉)
    flatten     : ∀ {A} (t : Tree A) → ElP (colist ⌈ List⁺ A ⌉)

infixl 9 _·_ _⊛_

_·_ : ∀ {A B} → (A → B) → ElW ⌈ A ⌉ → ElW ⌈ B ⌉
f · ⌈ x ⌉ = ⌈ f x ⌉

_⊛_ : ∀ {A B} → ElW ⌈ (A → B) ⌉ → ElW ⌈ A ⌉ → ElW ⌈ B ⌉
⌈ f ⌉ ⊛ x = f · x

whnf : ∀ {k} {a : U k} → ElP a → ElW a
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

  ⟦_⟧W : ∀ {k} {a : U k} → ElW a → El a
  ⟦_⟧W {ν} leaf         = leaf
  ⟦_⟧W {ν} (node l x r) = node (♯ ⟦ l ⟧) ⟦ x ⟧W (♯ ⟦ r ⟧)
  ⟦_⟧W {ν} (x ≺ xs)     = ⟦ x ⟧W ≺ ♯ ⟦ xs ⟧
  ⟦_⟧W {ν} []           = []
  ⟦_⟧W {ν} (x ∷ xs)     = ⟦ x ⟧W ∷ ♯ ⟦ xs ⟧
  ⟦_⟧W {μ} (x , y)      = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦_⟧W {μ} ⌈ x ⌉        = x

  ⟦_⟧ : ∀ {k} {a : U k} → ElP a → El a
  ⟦ p ⟧ = ⟦ whnf p ⟧W
