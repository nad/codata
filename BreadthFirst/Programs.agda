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

  data ElW : U → Set₁ where
    leaf : ∀ {a} → ElW (tree a)
    node : ∀ {a}
           (l : ∞ (ElP (tree a))) (x : ElW a) (r : ∞ (ElP (tree a))) →
           ElW (tree a)
    _≺_  : ∀ {a} (x : ElW a) (xs : ∞ (ElP (stream a))) → ElW (stream a)
    []   : ∀ {a} → ElW (colist a)
    _∷_  : ∀ {a} (x : ElW a) (xs : ∞ (ElP (colist a))) → ElW (colist a)
    _,_  : ∀ {a b} (x : ElW a) (y : ElW b) → ElW (a ⊗ b)
    ⌈_⌉  : ∀ {A} (x : A) → ElW ⌈ A ⌉

  -- Note that higher-order functions are not handled well (see
  -- longZipWith): the arguments cannot be programs, since this would
  -- make the type negative.

  -- The tree arguments to lab and flatten used to be tree programs,
  -- but a number of lemmas could be removed when they were turned
  -- into "actual" trees.

  data ElP : U → Set₁ where
    ↓_          : ∀ {a} (w : ElW a) → ElP a
    fst         : ∀ {a b} (p : ElP (a ⊗ b)) → ElP a
    snd         : ∀ {a b} (p : ElP (a ⊗ b)) → ElP b
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

fstW : ∀ {a b} → ElW (a ⊗ b) → ElW a
fstW (x , y) = x

sndW : ∀ {a b} → ElW (a ⊗ b) → ElW b
sndW (x , y) = y

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).

labW : ∀ {A B} → Tree A → ElW (stream ⌈ Stream B ⌉) →
       ElW (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
labW leaf         bss                = (leaf , bss)
labW (node l _ r) (⌈ b ≺ bs ⌉ ≺ bss) =
  (node (♯ fst x) ⌈ b ⌉ (♯ fst y) , ⌈ ♭ bs ⌉ ≺ ♯ snd y)
  where
  x = lab (♭ l) (♭ bss)
  y = lab (♭ r) (snd x)

longZipWithW : ∀ {A} → (A → A → A) →
               (xs ys : ElW (colist ⌈ A ⌉)) → ElW (colist ⌈ A ⌉)
longZipWithW f (x ∷ xs) (y ∷ ys) = f · x ⊛ y ∷ ♯ longZipWith f (♭ xs) (♭ ys)
longZipWithW f xs       []       = xs
longZipWithW f []       ys       = ys

flattenW : ∀ {A} → Tree A → ElW (colist ⌈ List⁺ A ⌉)
flattenW leaf         = []
flattenW (node l x r) =
  ⌈ [ x ] ⌉ ∷ ♯ longZipWith _⁺++⁺_ (flatten (♭ l)) (flatten (♭ r))

whnf : ∀ {a} → ElP a → ElW a
whnf (↓ w)                 = w
whnf (fst p)               = fstW (whnf p)
whnf (snd p)               = sndW (whnf p)
whnf (lab t bss)           = labW t (whnf bss)
whnf (longZipWith f xs ys) = longZipWithW f (whnf xs) (whnf ys)
whnf (flatten t)           = flattenW t

mutual

  ⟦_⟧W : ∀ {a} → ElW a → El a
  ⟦ leaf         ⟧W = leaf
  ⟦ (node l x r) ⟧W = node (♯ ⟦ ♭ l ⟧) ⟦ x ⟧W (♯ ⟦ ♭ r ⟧)
  ⟦ (x ≺ xs)     ⟧W = ⟦ x ⟧W ≺ ♯ ⟦ ♭ xs ⟧
  ⟦ []           ⟧W = []
  ⟦ (x ∷ xs)     ⟧W = ⟦ x ⟧W ∷ ♯ ⟦ ♭ xs ⟧
  ⟦ (x , y)      ⟧W = (⟦ x ⟧W , ⟦ y ⟧W)
  ⟦ ⌈ x ⌉        ⟧W = x

  ⟦_⟧ : ∀ {a} → ElP a → El a
  ⟦ p ⟧ = ⟦ whnf p ⟧W
