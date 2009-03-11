------------------------------------------------------------------------
-- Programs used to define and specify breadth-first manipulations of
-- trees
------------------------------------------------------------------------

module BreadthFirst.Programs where

open import Coinduction
open import Data.List.NonEmpty using (List⁺; [_])
                               renaming (_++_ to _++⁺_)
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

  data Prog : ∀ {k} → U k → Set1 where
    ↓_          : ∀ {k} {a : U k} (w : ∞? k (WHNF a)) → Prog a
    fst         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) → Prog a
    snd         : ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
                  (p : Prog (a ⊗ b)) → Prog b
    lab         : ∀ {k} {a : U k} {B}
                  (t : Prog (tree a)) (lss : Prog (stream ⌈ Stream B ⌉)) →
                  Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
    longZipWith : ∀ {A}
                  (f : A → A → A) (xs ys : Prog (colist ⌈ A ⌉)) →
                  Prog (colist ⌈ A ⌉)
    flatten     : ∀ {A}
                  (t : Prog (tree ⌈ A ⌉)) → Prog (colist ⌈ List⁺ A ⌉)

infixl 9 _·_ _⊛_

_·_ : ∀ {A B} → (A → B) → WHNF ⌈ A ⌉ → WHNF ⌈ B ⌉
f · ⌈ x ⌉ = ⌈ f x ⌉

_⊛_ : ∀ {A B} → WHNF ⌈ (A → B) ⌉ → WHNF ⌈ A ⌉ → WHNF ⌈ B ⌉
⌈ f ⌉ ⊛ x = f · x

mutual

  reify : ∀ {k} (a : U k) → El a → WHNF a
  reify (tree a)   leaf         = leaf
  reify (tree a)   (node l x r) = node (⟦ tree a ∣ ♭ l ⟧⁻¹ν)
                                       (reify a x)
                                       (⟦ tree a ∣ ♭ r ⟧⁻¹ν)
  reify (colist a) []           = []
  reify (colist a) (x ∷ xs)     = reify a x ∷ ⟦ colist a ∣ ♭ xs ⟧⁻¹ν
  reify (stream a) (x ≺ xs)     = reify a x ≺ ⟦ stream a ∣ ♭ xs ⟧⁻¹ν
  reify (a ⊗ b)    (x , y)      = (reify a x , reify b y)
  reify ⌈ A ⌉      x            = ⌈ x ⌉

  private

    ⟦_∣_⟧⁻¹ν : (a : U ν) → El a → Prog a
    ⟦ a ∣ x ⟧⁻¹ν = ↓ ♯₁ reify a x

⟦_∣_⟧⁻¹ : ∀ {k} (a : U k) → El a → Prog a
⟦_∣_⟧⁻¹ {μ} = λ a x → ↓ (reify a x)
⟦_∣_⟧⁻¹ {ν} = ⟦_∣_⟧⁻¹ν

whnf : ∀ {k} {a : U k} → Prog a → WHNF a
whnf (↓_ {k} w) = ♭? k w

-- Note: Sharing is lost here.
whnf (fst p) with whnf p
... | (x , y) = x

whnf (snd p) with whnf p
... | (x , y) = y

-- Uses the n-th stream to label the n-th level in the tree. Returns
-- the remaining stream elements (for every level).
whnf (lab t lss) with whnf t
... | leaf       = (leaf , whnf lss)
... | node l _ r with whnf lss
...              | ⌈ x ≺ ls ⌉ ≺ lss′ =
  (node (fst l′,lss″) ⌈ x ⌉ (fst r′,lss‴) , ⌈ ♭ ls ⌉ ≺ snd r′,lss‴)
  where
  l′,lss″ = lab l lss′
  r′,lss‴ = lab r (snd l′,lss″)

whnf (longZipWith f xs ys) with whnf xs | whnf ys
... | x ∷ xs′ | y ∷ ys′ = f · x ⊛ y ∷ longZipWith f xs′ ys′
... | xs′     | []      = xs′
... | []      | ys′     = ys′

whnf (flatten t) with whnf t
... | leaf       = []
... | node l x r = [_] · x ∷ longZipWith _++⁺_ (flatten l) (flatten r)

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

lift : ∀ {k₁ k₂} {a : U k₁} {b : U k₂} →
       (Prog a → Prog b) → El a → El b
lift f x = ⟦ f ⟦ _ ∣ x ⟧⁻¹ ⟧
