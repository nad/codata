------------------------------------------------------------------------
-- Some auxiliary operations and lemmas
------------------------------------------------------------------------

module BreadthFirst.Lemmas where

open import Coinduction
open import Function
open import Data.List using ([]; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; [_]; _∷_; _⁺++⁺_)
import Data.Vec as Vec
open import Data.Colist as Colist using (Colist; []; _∷_; concat; _++_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_) renaming (refl to ≡-refl)

open import BreadthFirst.Universe
open import BreadthFirst.Programs
open import Tree using (leaf; node; map)
open import Stream using (Stream; _≺_) renaming (_++_ to _++∞_)

------------------------------------------------------------------------
-- Some operations

zipWith : {A B : Set} (f : A → B → B) → Colist A → Stream B → Stream B
zipWith f []       ys       = ys
zipWith f (x ∷ xs) (y ≺ ys) = f x y ≺ ♯ zipWith f (♭ xs) (♭ ys)

_⁺++∞_ : {A : Set} → List⁺ A → Stream A → Stream A
xs ⁺++∞ ys = Colist.fromList (Vec.toList $ List⁺.toVec xs) ++∞ ys

_⁺++_ : {A : Set} → List⁺ A → Colist A → Colist A
xs ⁺++ ys = Colist.fromList (Vec.toList $ List⁺.toVec xs) ++ ys

------------------------------------------------------------------------
-- Eq is an equivalence relation

refl : ∀ {a} x → Eq a x x
refl {a = tree a}   leaf         = leaf
refl {a = tree a}   (node l x r) = node (♯ refl (♭ l)) (refl x) (♯ refl (♭ r))
refl {a = stream a} (x ≺ xs)     = refl x ≺ ♯ refl (♭ xs)
refl {a = colist a} []           = []
refl {a = colist a} (x ∷ xs)     = refl x ∷ ♯ refl (♭ xs)
refl {a = a ⊗ b}    (x , y)      = (refl x , refl y)
refl {a = ⌈ A ⌉}    x            = ⌈ PropEq.refl ⌉

sym : ∀ {a x y} → Eq a x y → Eq a y x
sym {a = tree a}   leaf                  = leaf
sym {a = tree a}   (node l≈l′ x≈x′ r≈r′) = node (♯ sym (♭ l≈l′)) (sym x≈x′) (♯ sym (♭ r≈r′))
sym {a = stream a} (x≈x′ ≺ xs≈xs′)       = sym x≈x′ ≺ ♯ sym (♭ xs≈xs′)
sym {a = colist a} []                    = []
sym {a = colist a} (x≈x′ ∷ xs≈xs′)       = sym x≈x′ ∷ ♯ sym (♭ xs≈xs′)
sym {a = a ⊗ b}    (x≈x′ , y≈y′)         = (sym x≈x′ , sym y≈y′)
sym {a = ⌈ A ⌉}    ⌈ x≡x′ ⌉              = ⌈ PropEq.sym x≡x′ ⌉

trans : ∀ {a x y z} → Eq a x y → Eq a y z → Eq a x z
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
infix  3 _∎
infixr 2 _≈⟨_⟩_ _≊⟨_⟩_

data EqP : ∀ a → El a → El a → Set₁ where
  leaf : ∀ {a} → EqP (tree a) leaf leaf
  node : ∀ {a x x′ l l′ r r′}
         (l≈l′ : ∞ (EqP (tree a) (♭ l) (♭ l′)))
         (x≈x′ :    Eq        a     x     x′  )
         (r≈r′ : ∞ (EqP (tree a) (♭ r) (♭ r′))) →
         EqP (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {a x x′ xs xs′}
         (x≈x′   :    Eq          a     x      x′   )
         (xs≈xs′ : ∞ (EqP (stream a) (♭ xs) (♭ xs′))) →
         EqP (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {a} → EqP (colist a) [] []
  _∷_  : ∀ {a x x′ xs xs′}
         (x≈x′   :    Eq          a     x      x′   )
         (xs≈xs′ : ∞ (EqP (colist a) (♭ xs) (♭ xs′))) →
         EqP (colist a) (x ∷ xs) (x′ ∷ xs′)
  _,_  : ∀ {a b x x′ y y′}
         (x≈x′ : Eq a x x′) (y≈y′ : Eq b y y′) →
         EqP (a ⊗ b) (x , y) (x′ , y′)
  ⌈_⌉  : ∀ {A x x′} (x≡x′ : x ≡ x′) → EqP ⌈ A ⌉ x x′

  _≊⟨_⟩_ : ∀ {a} x {y z}
           (x≈y : EqP a x y) (y≈z : EqP a y z) → EqP a x z

  zipWith-cong :
    ∀ {a b} {f : El a → El b → El b}
    (cong : ∀ {x x′ y y′} →
            Eq a x x′ → Eq b y y′ → Eq b (f x y) (f x′ y′))
    {xs xs′ ys ys′}
    (xs≈xs′ : EqP (colist a) xs xs′)
    (ys≈ys′ : EqP (stream b) ys ys′) →
    EqP (stream b) (zipWith f xs ys) (zipWith f xs′ ys′)

data EqW : ∀ a → El a → El a → Set₁ where
  leaf : ∀ {a} → EqW (tree a) leaf leaf
  node : ∀ {a x x′ l l′ r r′}
         (l≈l′ : EqP (tree a) (♭ l) (♭ l′))
         (x≈x′ : Eq        a     x     x′ )
         (r≈r′ : EqP (tree a) (♭ r) (♭ r′)) →
         EqW (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {a x x′ xs xs′}
         (x≈x′   : Eq          a     x      x′  )
         (xs≈xs′ : EqP (stream a) (♭ xs) (♭ xs′)) →
         EqW (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {a} → EqW (colist a) [] []
  _∷_  : ∀ {a x x′ xs xs′}
         (x≈x′   : Eq          a     x      x′  )
         (xs≈xs′ : EqP (colist a) (♭ xs) (♭ xs′)) →
         EqW (colist a) (x ∷ xs) (x′ ∷ xs′)
  _,_  : ∀ {a b x x′ y y′}
         (x≈x′ : Eq a x x′) (y≈y′ : Eq b y y′) →
         EqW (a ⊗ b) (x , y) (x′ , y′)
  ⌈_⌉  : ∀ {A x x′} (x≡x′ : x ≡ x′) → EqW ⌈ A ⌉ x x′

⟦_⟧≈⁻¹ : ∀ {a} {x y : El a} → Eq a x y → EqP a x y
⟦ leaf                ⟧≈⁻¹ = leaf
⟦ node l≈l′ x≈x′ r≈r′ ⟧≈⁻¹ = node (♯ ⟦ ♭ l≈l′ ⟧≈⁻¹) x≈x′ (♯ ⟦ ♭ r≈r′ ⟧≈⁻¹)
⟦ x≈x′ ≺ xs≈xs′       ⟧≈⁻¹ = x≈x′ ≺ ♯ ⟦ ♭ xs≈xs′ ⟧≈⁻¹
⟦ []                  ⟧≈⁻¹ = []
⟦ x≈x′ ∷ xs≈xs′       ⟧≈⁻¹ = x≈x′ ∷ ♯ ⟦ ♭ xs≈xs′ ⟧≈⁻¹
⟦ (x≈x′ , y≈y′)       ⟧≈⁻¹ = (x≈x′ , y≈y′)
⟦ ⌈ x≡x′ ⌉            ⟧≈⁻¹ = ⌈ x≡x′ ⌉

whnf≈ : ∀ {a xs ys} → EqP a xs ys → EqW a xs ys
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

  value≈ : ∀ {a xs ys} → EqW a xs ys → Eq a xs ys
  value≈ leaf                  = leaf
  value≈ (node l≈l′ x≈x′ r≈r′) = node (♯ ⟦ l≈l′ ⟧≈) x≈x′ (♯ ⟦ r≈r′ ⟧≈)
  value≈ (x≈x′ ≺ xs≈xs′)       = x≈x′ ≺ ♯ ⟦ xs≈xs′ ⟧≈
  value≈ []                    = []
  value≈ (x≈x′ ∷ xs≈xs′)       = x≈x′ ∷ ♯ ⟦ xs≈xs′ ⟧≈
  value≈ (x≈x′ , y≈y′)         = (x≈x′ , y≈y′)
  value≈ ⌈ x≡x′ ⌉              = ⌈ x≡x′ ⌉

  ⟦_⟧≈ : ∀ {a xs ys} → EqP a xs ys → Eq a xs ys
  ⟦ xs≈ys ⟧≈ = value≈ (whnf≈ xs≈ys)

_≈⟨_⟩_ : ∀ {a} x {y z}
         (x≈y : Eq a x y) (y≈z : EqP a y z) → EqP a x z
x ≈⟨ x≈y ⟩ y≈z = x ≊⟨ ⟦ x≈y ⟧≈⁻¹ ⟩ y≈z

_∎ : ∀ {a} x → EqP a x x
x ∎ = ⟦ refl x ⟧≈⁻¹

------------------------------------------------------------------------
-- Productivity checker workaround for PrefixOf

infixr 2 _≋⟨_⟩_ _⊑⟨_⟩_

data PrefixOfP (a : U) :
       Colist (El a) → Stream (El a) → Set₁ where
  []       : ∀ {ys} → PrefixOfP a [] ys
  ⁺++-mono : ∀ xs {ys ys′} (ys⊑ys′ : ∞ (PrefixOfP a ys ys′)) →
             PrefixOfP a (xs ⁺++ ys) (xs ⁺++∞ ys′)
  _≋⟨_⟩_   : ∀ xs {ys zs} (xs≈ys : Eq (colist a) xs ys)
             (ys⊑zs : PrefixOfP a ys zs) → PrefixOfP a xs zs
  _⊑⟨_⟩_   : ∀ xs {ys zs} (xs⊑ys : PrefixOfP a xs ys)
             (ys≈zs : EqP (stream a) ys zs) → PrefixOfP a xs zs

data PrefixOfW (a : U) :
       Colist (El a) → Stream (El a) → Set₁ where
  []  : ∀ {ys} → PrefixOfW a [] ys
  _∷_ : ∀ {x y xs ys}
        (x≈y : Eq a x y) (p : PrefixOfP a (♭ xs) (♭ ys)) →
        PrefixOfW a (x ∷ xs) (y ≺ ys)

whnf⊑ : ∀ {a xs ys} →
        PrefixOfP a xs ys → PrefixOfW a xs ys
whnf⊑ [] = []

whnf⊑ (⁺++-mono (x ∷ [])        ys⊑ys′) = refl x ∷ ♭ ys⊑ys′
whnf⊑ (⁺++-mono (x ∷ (x′ ∷ xs)) ys⊑ys′) =
  refl x ∷ ⁺++-mono (x′ ∷ xs) ys⊑ys′

whnf⊑ (._ ≋⟨ []          ⟩ _    ) = []
whnf⊑ (._ ≋⟨ x≈y ∷ xs≈ys ⟩ ys⊑zs) with whnf⊑ ys⊑zs
... | y≈z ∷ ys⊑zs′ = trans x≈y y≈z ∷ (_ ≋⟨ ♭ xs≈ys ⟩ ys⊑zs′)

whnf⊑ (._ ⊑⟨ xs⊑ys ⟩ ys≈zs) with whnf⊑ xs⊑ys | whnf≈ ys≈zs
... | []           | _            = []
... | x≈y ∷ xs⊑ys′ | y≈z ≺ ys≈zs′ = trans x≈y y≈z ∷ (_ ⊑⟨ xs⊑ys′ ⟩ ys≈zs′)

mutual

  value⊑ : ∀ {a xs ys} → PrefixOfW a xs ys → PrefixOf a xs ys
  value⊑ []            = []
  value⊑ (x≈y ∷ xs⊑ys) = x≈y ∷ ♯ ⟦ xs⊑ys ⟧⊑

  ⟦_⟧⊑ : ∀ {a xs ys} → PrefixOfP a xs ys → PrefixOf a xs ys
  ⟦ xs⊑ys ⟧⊑ = value⊑ (whnf⊑ xs⊑ys)

------------------------------------------------------------------------
-- More lemmas

⁺++∞-cong : ∀ {a xs xs′ ys ys′} →
            Eq ⌈ List⁺ (El a) ⌉ xs xs′ →
            Eq (stream a) ys ys′ →
            Eq (stream a) (xs ⁺++∞ ys) (xs′ ⁺++∞ ys′)
⁺++∞-cong {xs = x ∷ []}        ⌈ ≡-refl ⌉ ys≈ys′ = refl x ≺ ♯ ys≈ys′
⁺++∞-cong {xs = x ∷ (x′ ∷ xs)} ⌈ ≡-refl ⌉ ys≈ys′ =
  refl x ≺ ♯ ⁺++∞-cong {xs = x′ ∷ xs} ⌈ ≡-refl ⌉ ys≈ys′

++-assoc : ∀ {a} xs ys zs →
           Eq (stream a) (xs ⁺++∞ (ys ⁺++∞ zs)) ((xs ⁺++⁺ ys) ⁺++∞ zs)
++-assoc (x ∷ [])        ys zs = refl x ≺ ♯ refl (ys ⁺++∞ zs)
++-assoc (x ∷ (x′ ∷ xs)) ys zs = refl x ≺ ♯ ++-assoc (x′ ∷ xs) ys zs

zip-++-assoc : ∀ {a} xss yss (zss : Stream (Stream (El a))) →
               Eq (stream (stream a))
                  (zipWith _⁺++∞_ ⟦ xss ⟧ (zipWith _⁺++∞_ ⟦ yss ⟧ zss))
                  (zipWith _⁺++∞_ ⟦ longZipWith _⁺++⁺_ xss yss ⟧ zss)
zip-++-assoc xss yss (zs ≺ zss) with whnf xss | whnf yss
... | []            | []            = refl _
... | []            | ys     ∷ yss′ = refl _
... | xs     ∷ xss′ | []            = refl _
... | ⌈ xs ⌉ ∷ xss′ | ⌈ ys ⌉ ∷ yss′ =
  ++-assoc xs ys zs ≺ ♯ zip-++-assoc (♭ xss′) (♭ yss′) (♭ zss)

concat-lemma : ∀ {a} xs xss →
               Eq (colist a) (concat (xs ∷ xss))
                             (xs ⁺++ concat (♭ xss))
concat-lemma (x ∷ [])        xss = refl x ∷ ♯ refl (concat (♭ xss))
concat-lemma (x ∷ (x′ ∷ xs)) xss = refl x ∷ ♯ concat-lemma (x′ ∷ xs) xss
