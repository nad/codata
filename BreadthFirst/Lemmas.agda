------------------------------------------------------------------------
-- Some auxiliary operations and lemmas
------------------------------------------------------------------------

module BreadthFirst.Lemmas where

open import Coinduction
open import Function
import Data.List.NonEmpty as List⁺
open List⁺ using (List⁺; [_]; _∷_; _⁺++⁺_)
import Data.Vec as Vec
import Data.Colist as Colist
open Colist using (Colist; []; _∷_; concat; _++_)
open import Data.Product using (_,_)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using (_≡_) renaming (refl to ≡-refl)

open import BreadthFirst.Universe
open import BreadthFirst.Programs
open import Tree using (leaf; node; map)
import Stream
open Stream using (Stream; _≺_) renaming (_++_ to _++∞_)

------------------------------------------------------------------------
-- Some operations

zipWith : ∀ {A B} (f : A → B → B) → Colist A → Stream B → Stream B
zipWith f []       ys       = ys
zipWith f (x ∷ xs) (y ≺ ys) = f x y ≺ ♯ zipWith f (♭ xs) (♭ ys)

_⁺++∞_ : ∀ {A} → List⁺ A → Stream A → Stream A
xs ⁺++∞ ys = Colist.fromList (Vec.toList $ List⁺.toVec xs) ++∞ ys

_⁺++_ : ∀ {A} → List⁺ A → Colist A → Colist A
xs ⁺++ ys = Colist.fromList (Vec.toList $ List⁺.toVec xs) ++ ys

------------------------------------------------------------------------
-- Eq is an equivalence relation

refl : ∀ {k} {a : U k} x → Eq a x x
refl {a = tree a}   leaf         = leaf
refl {a = tree a}   (node l x r) = node (♯ refl (♭ l)) (refl x) (♯ refl (♭ r))
refl {a = stream a} (x ≺ xs)     = refl x ≺ ♯ refl (♭ xs)
refl {a = colist a} []           = []
refl {a = colist a} (x ∷ xs)     = refl x ∷ ♯ refl (♭ xs)
refl {a = a ⊗ b}    (x , y)      = (refl x , refl y)
refl {a = ⌈ A ⌉}    x            = ⌈ PropEq.refl ⌉

sym : ∀ {k} {a : U k} {x y} → Eq a x y → Eq a y x
sym {a = tree a}   leaf                  = leaf
sym {a = tree a}   (node l≈l′ x≈x′ r≈r′) = node (♯ sym (♭ l≈l′)) (sym x≈x′) (♯ sym (♭ r≈r′))
sym {a = stream a} (x≈x′ ≺ xs≈xs′)       = sym x≈x′ ≺ ♯ sym (♭ xs≈xs′)
sym {a = colist a} []                    = []
sym {a = colist a} (x≈x′ ∷ xs≈xs′)       = sym x≈x′ ∷ ♯ sym (♭ xs≈xs′)
sym {a = a ⊗ b}    (x≈x′ , y≈y′)         = (sym x≈x′ , sym y≈y′)
sym {a = ⌈ A ⌉}    ⌈ x≡x′ ⌉              = ⌈ PropEq.sym x≡x′ ⌉

trans : ∀ {k} {a : U k} {x y z} → Eq a x y → Eq a y z → Eq a x z
trans {a = tree a}   leaf leaf                = leaf
trans {a = tree a}   (node l≈l′ x≈x′ r≈r′)
                     (node l′≈l″ x′≈x″ r′≈r″) = node (♯ trans (♭ l≈l′) (♭ l′≈l″))
                                                     (trans x≈x′ x′≈x″)
                                                     (♯ trans (♭ r≈r′) (♭ r′≈r″))
trans {a = stream a} (x≈x′  ≺ xs≈xs′)
                     (x′≈x″ ≺ xs′≈xs″)        = trans x≈x′ x′≈x″ ≺ ♯ trans (♭ xs≈xs′) (♭ xs′≈xs″)
trans {a = colist a} [] []                    = []
trans {a = colist a} (x≈x′  ∷ xs≈xs′)
                     (x′≈x″ ∷ xs′≈xs″)        = trans x≈x′ x′≈x″ ∷ ♯ trans (♭ xs≈xs′) (♭ xs′≈xs″)
trans {a = a ⊗ b}    (x≈x′  , y≈y′)
                     (x′≈x″ , y′≈y″)          = (trans x≈x′ x′≈x″ , trans y≈y′ y′≈y″)
trans {a = ⌈ A ⌉}    ⌈ x≡x′  ⌉ ⌈ x′≡x″ ⌉      = ⌈ PropEq.trans x≡x′ x′≡x″ ⌉

------------------------------------------------------------------------
-- Productivity checker workaround for Eq

infixr 5 _≺_ _∷_
infixr 2 _≈⟨_⟩_ _≊⟨_⟩_
infix  2 _∎

data EqProg : ∀ {k} (a : U k) → El a → El a → Set1 where
  leaf : ∀ {k} {a : U k} → EqProg (tree a) leaf leaf
  node : ∀ {k} {a : U k} {x x′ l l′ r r′}
         (l≈l′ : ∞ (EqProg (tree a) (♭ l) (♭ l′)))
         (x≈x′ :    Eq           a     x     x′  )
         (r≈r′ : ∞ (EqProg (tree a) (♭ r) (♭ r′))) →
         EqProg (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   :    Eq             a     x      x′   )
         (xs≈xs′ : ∞ (EqProg (stream a) (♭ xs) (♭ xs′))) →
         EqProg (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {k} {a : U k} → EqProg (colist a) [] []
  _∷_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   :    Eq             a     x      x′   )
         (xs≈xs′ : ∞ (EqProg (colist a) (♭ xs) (♭ xs′))) →
         EqProg (colist a) (x ∷ xs) (x′ ∷ xs′)
  _,_  : ∀ {k₁ k₂} {a : U k₁} {b : U k₂} {x x′ y y′}
         (x≈x′ : Eq a x x′) (y≈y′ : Eq b y y′) →
         EqProg (a ⊗ b) (x , y) (x′ , y′)
  ⌈_⌉  : ∀ {A} {x x′} (x≡x′ : x ≡ x′) → EqProg ⌈ A ⌉ x x′

  _≊⟨_⟩_ : ∀ {k} {a : U k} x {y z}
           (x≈y : EqProg a x y) (y≈z : EqProg a y z) → EqProg a x z

  zipWith-cong :
    ∀ {k₁ k₂} {a : U k₁} {b : U k₂}
    {f : El a → El b → El b}
    (cong : ∀ {x x′ y y′} →
            Eq a x x′ → Eq b y y′ → Eq b (f x y) (f x′ y′))
    {xs xs′ ys ys′}
    (xs≈xs′ : EqProg (colist a) xs xs′)
    (ys≈ys′ : EqProg (stream b) ys ys′) →
    EqProg (stream b) (zipWith f xs ys) (zipWith f xs′ ys′)

data EqWHNF : ∀ {k} (a : U k) → El a → El a → Set1 where
  leaf : ∀ {k} {a : U k} → EqWHNF (tree a) leaf leaf
  node : ∀ {k} {a : U k} {x x′ l l′ r r′}
         (l≈l′ : EqProg (tree a) (♭ l) (♭ l′))
         (x≈x′ : Eq           a     x     x′ )
         (r≈r′ : EqProg (tree a) (♭ r) (♭ r′)) →
         EqWHNF (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   : Eq             a     x      x′  )
         (xs≈xs′ : EqProg (stream a) (♭ xs) (♭ xs′)) →
         EqWHNF (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {k} {a : U k} → EqWHNF (colist a) [] []
  _∷_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   : Eq             a     x      x′  )
         (xs≈xs′ : EqProg (colist a) (♭ xs) (♭ xs′)) →
         EqWHNF (colist a) (x ∷ xs) (x′ ∷ xs′)
  _,_  : ∀ {k₁ k₂} {a : U k₁} {b : U k₂} {x x′ y y′}
         (x≈x′ : Eq a x x′) (y≈y′ : Eq b y y′) →
         EqWHNF (a ⊗ b) (x , y) (x′ , y′)
  ⌈_⌉  : ∀ {A} {x x′} (x≡x′ : x ≡ x′) → EqWHNF ⌈ A ⌉ x x′

⟦_⟧≈⁻¹ : ∀ {k} {a : U k} {x y : El a} → Eq a x y → EqProg a x y
⟦ leaf                ⟧≈⁻¹ = leaf
⟦ node l≈l′ x≈x′ r≈r′ ⟧≈⁻¹ = node (♯ ⟦ ♭ l≈l′ ⟧≈⁻¹) x≈x′ (♯ ⟦ ♭ r≈r′ ⟧≈⁻¹)
⟦ x≈x′ ≺ xs≈xs′       ⟧≈⁻¹ = x≈x′ ≺ ♯ ⟦ ♭ xs≈xs′ ⟧≈⁻¹
⟦ []                  ⟧≈⁻¹ = []
⟦ x≈x′ ∷ xs≈xs′       ⟧≈⁻¹ = x≈x′ ∷ ♯ ⟦ ♭ xs≈xs′ ⟧≈⁻¹
⟦ (x≈x′ , y≈y′)       ⟧≈⁻¹ = (x≈x′ , y≈y′)
⟦ ⌈ x≡x′ ⌉            ⟧≈⁻¹ = ⌈ x≡x′ ⌉

whnf≈ : ∀ {k} {a : U k} {xs ys} → EqProg a xs ys → EqWHNF a xs ys
whnf≈ leaf                  = leaf
whnf≈ (node l≈l′ x≈x′ r≈r′) = node (♭ l≈l′) x≈x′ (♭ r≈r′)
whnf≈ (x≈x′ ≺ xs≈xs′)       = x≈x′ ≺ ♭ xs≈xs′
whnf≈ []                    = []
whnf≈ (x≈x′ ∷ xs≈xs′)       = x≈x′ ∷ ♭ xs≈xs′
whnf≈ (x≈x′ , y≈y′)         = (x≈x′ , y≈y′)
whnf≈ ⌈ x≡x′ ⌉              = ⌈ x≡x′ ⌉

whnf≈ ( _ ≊⟨ x≈y ⟩ y≈z) with whnf≈ x≈y | whnf≈ y≈z
whnf≈ (._ ≊⟨ x≈y ⟩ y≈z) | leaf           | leaf            = leaf
whnf≈ (._ ≊⟨ x≈y ⟩ y≈z) | node l≈l′  x≈x′  r≈r′
                        | node l′≈l″ x′≈x″ r′≈r″ = node (_ ≊⟨ l≈l′ ⟩ l′≈l″) (trans x≈x′ x′≈x″) (_ ≊⟨ r≈r′ ⟩ r′≈r″)
whnf≈ (._ ≊⟨ x≈y ⟩ y≈z) | []             | []              = []
whnf≈ (._ ≊⟨ x≈y ⟩ y≈z) | x≈y′ ∷ xs≈ys′  | y≈z′ ∷ ys≈zs′   = trans x≈y′ y≈z′ ∷ (_ ≊⟨ xs≈ys′ ⟩ ys≈zs′)
whnf≈ (._ ≊⟨ x≈y ⟩ y≈z) | x≈y′ ≺ xs≈ys′  | y≈z′ ≺ ys≈zs′   = trans x≈y′ y≈z′ ≺ (_ ≊⟨ xs≈ys′ ⟩ ys≈zs′)
whnf≈ (._ ≊⟨ x≈y ⟩ y≈z) | (x≈x′  , y≈y′) | (x′≈x″ , y′≈y″) = (trans x≈x′ x′≈x″ , trans y≈y′ y′≈y″)
whnf≈ ( _ ≊⟨ x≈y ⟩ y≈z) | ⌈ x≡x′  ⌉      | ⌈ x′≡x″ ⌉       = ⌈ PropEq.trans x≡x′ x′≡x″ ⌉

whnf≈ (zipWith-cong cong xs≈xs′ ys≈ys′) with whnf≈ xs≈xs′ | whnf≈ ys≈ys′
... | []            | ys≈ys″        = ys≈ys″
... | x≈x′ ∷ xs≈xs″ | y≈y′ ≺ ys≈ys″ =
  cong x≈x′ y≈y′ ≺ zipWith-cong cong xs≈xs″ ys≈ys″

mutual

  value≈ : ∀ {k} {a : U k} {xs ys} → EqWHNF a xs ys → Eq a xs ys
  value≈ leaf                  = leaf
  value≈ (node l≈l′ x≈x′ r≈r′) = node (♯ ⟦ l≈l′ ⟧≈) x≈x′ (♯ ⟦ r≈r′ ⟧≈)
  value≈ (x≈x′ ≺ xs≈xs′)       = x≈x′ ≺ ♯ ⟦ xs≈xs′ ⟧≈
  value≈ []                    = []
  value≈ (x≈x′ ∷ xs≈xs′)       = x≈x′ ∷ ♯ ⟦ xs≈xs′ ⟧≈
  value≈ (x≈x′ , y≈y′)         = (x≈x′ , y≈y′)
  value≈ ⌈ x≡x′ ⌉              = ⌈ x≡x′ ⌉

  ⟦_⟧≈ : ∀ {k} {a : U k} {xs ys} → EqProg a xs ys → Eq a xs ys
  ⟦ xs≈ys ⟧≈ = value≈ (whnf≈ xs≈ys)

_≈⟨_⟩_ : ∀ {k} {a : U k} x {y z}
         (x≈y : Eq a x y) (y≈z : EqProg a y z) → EqProg a x z
x ≈⟨ x≈y ⟩ y≈z = x ≊⟨ ⟦ x≈y ⟧≈⁻¹ ⟩ y≈z

_∎ : ∀ {k} {a : U k} x → EqProg a x x
x ∎ = ⟦ refl x ⟧≈⁻¹

------------------------------------------------------------------------
-- Productivity checker workaround for PrefixOf

infixr 2 _≋⟨_⟩_ _⊑⟨_⟩_

data PrefixOfProg {k} (a : U k) :
       Colist (El a) → Stream (El a) → Set1 where
  []       : ∀ {ys} → PrefixOfProg a [] ys
  ⁺++-mono : ∀ xs {ys ys′} (ys⊑ys′ : ∞ (PrefixOfProg a ys ys′)) →
             PrefixOfProg a (xs ⁺++ ys) (xs ⁺++∞ ys′)
  _≋⟨_⟩_   : ∀ xs {ys zs} (xs≈ys : Eq (colist a) xs ys)
             (ys⊑zs : PrefixOfProg a ys zs) → PrefixOfProg a xs zs
  _⊑⟨_⟩_   : ∀ xs {ys zs} (xs⊑ys : PrefixOfProg a xs ys)
             (ys≈zs : EqProg (stream a) ys zs) → PrefixOfProg a xs zs

data PrefixOfWHNF {k} (a : U k) :
       Colist (El a) → Stream (El a) → Set1 where
  []  : ∀ {ys} → PrefixOfWHNF a [] ys
  _∷_ : ∀ {x y xs ys}
        (x≈y : Eq a x y) (p : PrefixOfProg a (♭ xs) (♭ ys)) →
        PrefixOfWHNF a (x ∷ xs) (y ≺ ys)

whnf⊑ : ∀ {k} {a : U k} {xs ys} →
        PrefixOfProg a xs ys → PrefixOfWHNF a xs ys
whnf⊑ []                         = []

whnf⊑ (⁺++-mono [ x ]    ys⊑ys′) = refl x ∷ ♭ ys⊑ys′
whnf⊑ (⁺++-mono (x ∷ xs) ys⊑ys′) = refl x ∷ ⁺++-mono xs ys⊑ys′

whnf⊑ (._ ≋⟨ []          ⟩ _    ) = []
whnf⊑ (._ ≋⟨ x≈y ∷ xs≈ys ⟩ ys⊑zs) with whnf⊑ ys⊑zs
... | y≈z ∷ ys⊑zs′ = trans x≈y y≈z ∷ (_ ≋⟨ ♭ xs≈ys ⟩ ys⊑zs′)

whnf⊑ (._ ⊑⟨ xs⊑ys ⟩ ys≈zs) with whnf⊑ xs⊑ys | whnf≈ ys≈zs
... | []           | _            = []
... | x≈y ∷ xs⊑ys′ | y≈z ≺ ys≈zs′ = trans x≈y y≈z ∷ (_ ⊑⟨ xs⊑ys′ ⟩ ys≈zs′)

mutual

  value⊑ : ∀ {k} {a : U k} {xs ys} →
           PrefixOfWHNF a xs ys → PrefixOf a xs ys
  value⊑ []            = []
  value⊑ (x≈y ∷ xs⊑ys) = x≈y ∷ ♯ ⟦ xs⊑ys ⟧⊑

  ⟦_⟧⊑ : ∀ {k} {a : U k} {xs ys} →
         PrefixOfProg a xs ys → PrefixOf a xs ys
  ⟦ xs⊑ys ⟧⊑ = value⊑ (whnf⊑ xs⊑ys)

------------------------------------------------------------------------
-- More lemmas

⁺++∞-cong : ∀ {k} {a : U k} {xs xs′ ys ys′} →
            Eq ⌈ List⁺ (El a) ⌉ xs xs′ →
            Eq (stream a) ys ys′ →
            Eq (stream a) (xs ⁺++∞ ys) (xs′ ⁺++∞ ys′)
⁺++∞-cong {xs = [ x ]}  ⌈ ≡-refl ⌉ ys≈ys′ = refl x ≺ ♯ ys≈ys′
⁺++∞-cong {xs = x ∷ xs} ⌈ ≡-refl ⌉ ys≈ys′ =
  refl x ≺ ♯ ⁺++∞-cong {xs = xs} ⌈ ≡-refl ⌉ ys≈ys′

++-assoc : ∀ {k} {a : U k} xs ys zs →
           Eq (stream a) (xs ⁺++∞ (ys ⁺++∞ zs)) ((xs ⁺++⁺ ys) ⁺++∞ zs)
++-assoc [ x ]    ys zs = refl x ≺ ♯ refl (ys ⁺++∞ zs)
++-assoc (x ∷ xs) ys zs = refl x ≺ ♯ ++-assoc xs ys zs

zip-++-assoc : ∀ {k} {a : U k} xss yss (zss : Stream (Stream (El a))) →
               Eq (stream (stream a))
                  (zipWith _⁺++∞_ ⟦ xss ⟧ (zipWith _⁺++∞_ ⟦ yss ⟧ zss))
                  (zipWith _⁺++∞_ ⟦ longZipWith _⁺++⁺_ xss yss ⟧ zss)
zip-++-assoc xss yss (zs ≺ zss) with whnf xss | whnf yss
... | []            | []            = refl _
... | []            | ys     ∷ yss′ = refl _
... | xs     ∷ xss′ | []            = refl _
... | ⌈ xs ⌉ ∷ xss′ | ⌈ ys ⌉ ∷ yss′ =
  ++-assoc xs ys zs ≺ ♯ zip-++-assoc xss′ yss′ (♭ zss)

concat-lemma : ∀ {k} {a : U k} xs xss →
               Eq (colist a) (concat (xs ∷ xss))
                             (xs ⁺++ concat (♭ xss))
concat-lemma [ x ]    xss = refl x ∷ ♯ refl (concat (♭ xss))
concat-lemma (x ∷ xs) xss = refl x ∷ ♯ concat-lemma xs xss
