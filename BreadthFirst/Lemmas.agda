------------------------------------------------------------------------
-- Some auxiliary operations and lemmas
------------------------------------------------------------------------

module BreadthFirst.Lemmas where

open import Coinduction
open import Data.Function
import Data.List.NonEmpty as List⁺
open List⁺ using (List⁺; [_]; _∷_) renaming (_++_ to _++⁺_)
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
zipWith f (x ∷ xs) (y ≺ ys) = f x y ≺ zipWith′
  where zipWith′ ~ ♯ zipWith f (♭ xs) (♭ ys)

_⁺++∞_ : ∀ {A} → List⁺ A → Stream A → Stream A
xs ⁺++∞ ys = Colist.fromList (Vec.toList $ List⁺.toVec xs) ++∞ ys

_⁺++_ : ∀ {A} → List⁺ A → Colist A → Colist A
xs ⁺++ ys = Colist.fromList (Vec.toList $ List⁺.toVec xs) ++ ys

------------------------------------------------------------------------
-- Eq is an equivalence relation

refl : ∀ {k} {a : U k} x → Eq a x x
refl {a = tree a}   leaf         = leaf
refl {a = tree a}   (node l x r) = node l′ (refl x) r′
                                   where l′ ~ ♯₁ refl (♭ l)
                                         r′ ~ ♯₁ refl (♭ r)
refl {a = stream a} (x ≺ xs)     = refl x ≺ xs′ where xs′ ~ ♯₁ refl (♭ xs)
refl {a = colist a} []           = []
refl {a = colist a} (x ∷ xs)     = refl x ∷ xs′ where xs′ ~ ♯₁ refl (♭ xs)
refl {a = a ⊗ b}    (x , y)      = (refl x , refl y)
refl {a = ⌈ A ⌉}    x            = ⌈ PropEq.refl ⌉

sym : ∀ {k} {a : U k} {x y} → Eq a x y → Eq a y x
sym {a = tree a}   leaf                  = leaf
sym {a = tree a}   (node l≈l′ x≈x′ r≈r′) = node l′ (sym x≈x′) r′
                                           where l′ ~ ♯₁ sym (♭₁ l≈l′)
                                                 r′ ~ ♯₁ sym (♭₁ r≈r′)
sym {a = stream a} (x≈x′ ≺ xs≈xs′)       = sym x≈x′ ≺ xs′
                                           where xs′ ~ ♯₁ sym (♭₁ xs≈xs′)
sym {a = colist a} []                    = []
sym {a = colist a} (x≈x′ ∷ xs≈xs′)       = sym x≈x′ ∷ xs′
                                           where xs′ ~ ♯₁ sym (♭₁ xs≈xs′)
sym {a = a ⊗ b}    (x≈x′ , y≈y′)         = (sym x≈x′ , sym y≈y′)
sym {a = ⌈ A ⌉}    ⌈ x≡x′ ⌉              = ⌈ PropEq.sym x≡x′ ⌉

trans : ∀ {k} {a : U k} {x y z} → Eq a x y → Eq a y z → Eq a x z
trans {a = tree a}   leaf leaf                = leaf
trans {a = tree a}   (node l≈l′ x≈x′ r≈r′)
                     (node l′≈l″ x′≈x″ r′≈r″) = node l′ (trans x≈x′ x′≈x″) r′
                                                where l′ ~ ♯₁ trans (♭₁ l≈l′) (♭₁ l′≈l″)
                                                      r′ ~ ♯₁ trans (♭₁ r≈r′) (♭₁ r′≈r″)
trans {a = stream a} (x≈x′  ≺ xs≈xs′)
                     (x′≈x″ ≺ xs′≈xs″)        = trans x≈x′ x′≈x″ ≺ xs′
                                                where xs′ ~ ♯₁ trans (♭₁ xs≈xs′) (♭₁ xs′≈xs″)
trans {a = colist a} [] []                    = []
trans {a = colist a} (x≈x′  ∷ xs≈xs′)
                     (x′≈x″ ∷ xs′≈xs″)        = trans x≈x′ x′≈x″ ∷ xs′
                                                where xs′ ~ ♯₁ trans (♭₁ xs≈xs′) (♭₁ xs′≈xs″)
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
         (l≈l′ : ∞₁ (EqProg (tree a) (♭ l) (♭ l′)))
         (x≈x′ :     Eq           a     x     x′  )
         (r≈r′ : ∞₁ (EqProg (tree a) (♭ r) (♭ r′))) →
         EqProg (tree a) (node l x r) (node l′ x′ r′)
  _≺_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   :     Eq             a     x      x′   )
         (xs≈xs′ : ∞₁ (EqProg (stream a) (♭ xs) (♭ xs′))) →
         EqProg (stream a) (x ≺ xs) (x′ ≺ xs′)
  []   : ∀ {k} {a : U k} → EqProg (colist a) [] []
  _∷_  : ∀ {k} {a : U k} {x x′ xs xs′}
         (x≈x′   :     Eq             a     x      x′   )
         (xs≈xs′ : ∞₁ (EqProg (colist a) (♭ xs) (♭ xs′))) →
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

  longZipWith-cong :
    ∀ {A} f xs₁ xs₂ ys₁ ys₂
    (xs₁≈xs₂ : EqProg (colist ⌈ A ⌉) ⟦ xs₁ ⟧ ⟦ xs₂ ⟧)
    (ys₁≈ys₂ : EqProg (colist ⌈ A ⌉) ⟦ ys₁ ⟧ ⟦ ys₂ ⟧) →
    EqProg (colist ⌈ A ⌉) ⟦ longZipWith f xs₁ ys₁ ⟧
                          ⟦ longZipWith f xs₂ ys₂ ⟧

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
⟦ node l≈l′ x≈x′ r≈r′ ⟧≈⁻¹ = node ⟦⟧≈⁻¹ˡ x≈x′ ⟦⟧≈⁻¹ʳ
                             where ⟦⟧≈⁻¹ˡ ~ ♯₁ ⟦ ♭₁ l≈l′ ⟧≈⁻¹
                                   ⟦⟧≈⁻¹ʳ ~ ♯₁ ⟦ ♭₁ r≈r′ ⟧≈⁻¹
⟦ x≈x′ ≺ xs≈xs′       ⟧≈⁻¹ = x≈x′ ≺ ⟦⟧≈⁻¹′ where ⟦⟧≈⁻¹′ ~ ♯₁ ⟦ ♭₁ xs≈xs′ ⟧≈⁻¹
⟦ []                  ⟧≈⁻¹ = []
⟦ x≈x′ ∷ xs≈xs′       ⟧≈⁻¹ = x≈x′ ∷ ⟦⟧≈⁻¹′ where ⟦⟧≈⁻¹′ ~ ♯₁ ⟦ ♭₁ xs≈xs′ ⟧≈⁻¹
⟦ (x≈x′ , y≈y′)       ⟧≈⁻¹ = (x≈x′ , y≈y′)
⟦ ⌈ x≡x′ ⌉            ⟧≈⁻¹ = ⌈ x≡x′ ⌉

whnf≈ : ∀ {k} {a : U k} {xs ys} → EqProg a xs ys → EqWHNF a xs ys
whnf≈ leaf                  = leaf
whnf≈ (node l≈l′ x≈x′ r≈r′) = node (♭₁ l≈l′) x≈x′ (♭₁ r≈r′)
whnf≈ (x≈x′ ≺ xs≈xs′)       = x≈x′ ≺ ♭₁ xs≈xs′
whnf≈ []                    = []
whnf≈ (x≈x′ ∷ xs≈xs′)       = x≈x′ ∷ ♭₁ xs≈xs′
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

whnf≈ (longZipWith-cong f xs₁ xs₂ ys₁ ys₂ xs₁≈xs₂ ys₁≈ys₂)
  with whnf xs₁ | whnf xs₂ | whnf ys₁ | whnf ys₂
     | whnf≈ xs₁≈xs₂ | whnf≈ ys₁≈ys₂
... | ⌈ _ ⌉ ∷ _ | ⌈ _ ⌉ ∷ _ | ⌈ _ ⌉ ∷ ys′ | ⌈ _ ⌉ ∷ ys″
    | ⌈ x ⌉ ∷ xs | ⌈ y ⌉ ∷ ys =
  ⌈ PropEq.cong₂ f x y ⌉ ∷ longZipWith-cong f _ _ ys′ ys″ xs ys
... | []    | []    | _ ∷ _ | _ ∷ _ | [] | ys = ys
... | _ ∷ _ | _ ∷ _ | []    | []    | xs | [] = xs
... | []    | []    | []    | []    | [] | [] = []
... | _ ∷ _ | []    | _     | _     | () | _
... | []    | _ ∷ _ | _     | _     | () | _
... | _     | _     | _ ∷ _ | []    | _  | ()
... | _     | _     | []    | _ ∷ _ | _  | ()

mutual

  value≈ : ∀ {k} {a : U k} {xs ys} → EqWHNF a xs ys → Eq a xs ys
  value≈ leaf                  = leaf
  value≈ (node l≈l′ x≈x′ r≈r′) = node value≈ˡ x≈x′ value≈ʳ
                                 where value≈ˡ ~ ♯₁ ⟦ l≈l′ ⟧≈
                                       value≈ʳ ~ ♯₁ ⟦ r≈r′ ⟧≈
  value≈ (x≈x′ ≺ xs≈xs′)       = x≈x′ ≺ value≈′ where value≈′ ~ ♯₁ ⟦ xs≈xs′ ⟧≈
  value≈ []                    = []
  value≈ (x≈x′ ∷ xs≈xs′)       = x≈x′ ∷ value≈′ where value≈′ ~ ♯₁ ⟦ xs≈xs′ ⟧≈
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
  ⁺++-mono : ∀ xs {ys ys′} (ys⊑ys′ : ∞₁ (PrefixOfProg a ys ys′)) →
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

whnf⊑ (⁺++-mono [ x ]    ys⊑ys′) = refl x ∷ ♭₁ ys⊑ys′
whnf⊑ (⁺++-mono (x ∷ xs) ys⊑ys′) = refl x ∷ ⁺++-mono xs ys⊑ys′

whnf⊑ (._ ≋⟨ []          ⟩ _    ) = []
whnf⊑ (._ ≋⟨ x≈y ∷ xs≈ys ⟩ ys⊑zs) with whnf⊑ ys⊑zs
... | y≈z ∷ ys⊑zs′ = trans x≈y y≈z ∷ (_ ≋⟨ ♭₁ xs≈ys ⟩ ys⊑zs′)

whnf⊑ (._ ⊑⟨ xs⊑ys ⟩ ys≈zs) with whnf⊑ xs⊑ys | whnf≈ ys≈zs
... | []           | _            = []
... | x≈y ∷ xs⊑ys′ | y≈z ≺ ys≈zs′ = trans x≈y y≈z ∷ (_ ⊑⟨ xs⊑ys′ ⟩ ys≈zs′)

mutual

  value⊑ : ∀ {k} {a : U k} {xs ys} →
           PrefixOfWHNF a xs ys → PrefixOf a xs ys
  value⊑ []            = []
  value⊑ (x≈y ∷ xs⊑ys) = x≈y ∷ value⊑′ where value⊑′ ~ ♯₁ ⟦ xs⊑ys ⟧⊑

  ⟦_⟧⊑ : ∀ {k} {a : U k} {xs ys} →
         PrefixOfProg a xs ys → PrefixOf a xs ys
  ⟦ xs⊑ys ⟧⊑ = value⊑ (whnf⊑ xs⊑ys)

------------------------------------------------------------------------
-- Some congruences

map-cong : ∀ {A B} (f : A → B) {t₁ t₂} →
           Eq (tree ⌈ A ⌉) t₁ t₂ →
           Eq (tree ⌈ B ⌉) (map f t₁) (map f t₂)
map-cong f leaf                = leaf
map-cong f (node l≈ ⌈ x≡ ⌉ r≈) = node mapˡ ⌈ PropEq.cong f x≡ ⌉ mapʳ
  where
  mapˡ ~ ♯₁ map-cong f (♭₁ l≈)
  mapʳ ~ ♯₁ map-cong f (♭₁ r≈)

concat-cong : ∀ {k} {a : U k} {xss yss} →
              Eq (colist ⌈ List⁺ (El a) ⌉) xss yss →
              Eq (colist a) (concat xss) (concat yss)
concat-cong []                                     = []
concat-cong (_∷_ {x = [ x ]}  ⌈ ≡-refl ⌉ xss≈xss′) = refl x ∷ concat-cong′
  where concat-cong′ ~ ♯₁ concat-cong (♭₁ xss≈xss′)
concat-cong (_∷_ {x = x ∷ xs} ⌈ ≡-refl ⌉ xss≈xss′) =
  refl x ∷ ♯₁ concat-cong (_∷_ {x = xs} ⌈ ≡-refl ⌉ xss≈xss′)

flatten-cong :
  ∀ {A} t₁ t₂ →
  Eq (tree ⌈ A ⌉) ⟦ t₁ ⟧ ⟦ t₂ ⟧ →
  EqProg (colist ⌈ List⁺ A ⌉) ⟦ flatten t₁ ⟧ ⟦ flatten t₂ ⟧
flatten-cong t₁ t₂ t₁≈t₂                 with whnf t₁ | whnf t₂
flatten-cong t₁ t₂ leaf                  | leaf             | leaf              = []
flatten-cong t₁ t₂ ()                    | leaf             | node _ _ _
flatten-cong t₁ t₂ ()                    | node _ _ _       | leaf
flatten-cong t₁ t₂ (node l ⌈ ≡-refl ⌉ r) | node l′ ⌈ _ ⌉ r′ | node l″ ⌈ ._ ⌉ r″ =
  ⌈ ≡-refl ⌉ ∷ flatten-cong′
  where
  flatten-cong′ ~ ♯₁
    longZipWith-cong _++⁺_ _ _ (flatten r′) (flatten r″)
                     (flatten-cong l′ l″ (♭₁ l))
                     (flatten-cong r′ r″ (♭₁ r))

⁺++∞-cong : ∀ {k} {a : U k} {xs xs′ ys ys′} →
            Eq ⌈ List⁺ (El a) ⌉ xs xs′ →
            Eq (stream a) ys ys′ →
            Eq (stream a) (xs ⁺++∞ ys) (xs′ ⁺++∞ ys′)
⁺++∞-cong {xs = [ x ]}  ⌈ ≡-refl ⌉ ys≈ys′ = refl x ≺ ♯₁ ys≈ys′
⁺++∞-cong {xs = x ∷ xs} ⌈ ≡-refl ⌉ ys≈ys′ =
  refl x ≺ ♯₁ ⁺++∞-cong {xs = xs} ⌈ ≡-refl ⌉ ys≈ys′

------------------------------------------------------------------------
-- More lemmas

reflect-reify : ∀ {k} (a : U k) (x : El a) →
                Eq a (reflect (reify a x)) x
reflect-reify (tree a)   leaf         = leaf
reflect-reify (tree a)   (node l x r) = node l′ (reflect-reify a x) r′
                                        where l′ ~ ♯₁ reflect-reify (tree a) (♭ l)
                                              r′ ~ ♯₁ reflect-reify (tree a) (♭ r)
reflect-reify (stream a) (x ≺ xs)     = reflect-reify a x ≺ xs′
                                        where xs′ ~ ♯₁ reflect-reify (stream a) (♭ xs)
reflect-reify (colist a) []           = []
reflect-reify (colist a) (x ∷ xs)     = reflect-reify a x ∷ xs′
                                        where xs′ ~ ♯₁ reflect-reify (colist a) (♭ xs)
reflect-reify (a ⊗ b)    (x , y)      = (reflect-reify a x , reflect-reify b y)
reflect-reify ⌈ A ⌉      x            = ⌈ ≡-refl ⌉

-- ⟦_∣_⟧⁻¹ is a right inverse of ⟦_⟧.

right-inverse : ∀ {k} {a : U k} (x : El a) → Eq a ⟦ ⟦ a ∣ x ⟧⁻¹ ⟧ x
right-inverse {μ} x = reflect-reify _ x
right-inverse {ν} x = reflect-reify _ x

++-assoc : ∀ {k} {a : U k} xs ys zs →
           Eq (stream a) (xs ⁺++∞ (ys ⁺++∞ zs)) ((xs ++⁺ ys) ⁺++∞ zs)
++-assoc [ x ]    ys zs = refl x ≺ ♯₁ refl (ys ⁺++∞ zs)
++-assoc (x ∷ xs) ys zs = refl x ≺ ♯₁ ++-assoc xs ys zs

zip-++-assoc : ∀ {k} {a : U k} xss yss (zss : Stream (Stream (El a))) →
               Eq (stream (stream a))
                  (zipWith _⁺++∞_ ⟦ xss ⟧ (zipWith _⁺++∞_ ⟦ yss ⟧ zss))
                  (zipWith _⁺++∞_ ⟦ longZipWith _++⁺_ xss yss ⟧ zss)
zip-++-assoc xss yss (zs ≺ zss) with whnf xss | whnf yss
... | []            | []            = refl _
... | []            | ys     ∷ yss′ = refl _
... | xs     ∷ xss′ | []            = refl _
... | ⌈ xs ⌉ ∷ xss′ | ⌈ ys ⌉ ∷ yss′ =
  ++-assoc xs ys zs ≺ zip-++-assoc′
  where zip-++-assoc′ ~ ♯₁ zip-++-assoc xss′ yss′ (♭ zss)

concat-lemma : ∀ {k} {a : U k} xs xss →
               Eq (colist a) (concat (xs ∷ xss))
                             (xs ⁺++ concat (♭ xss))
concat-lemma [ x ]    xss = refl x ∷ ♯₁ refl (concat (♭ xss))
concat-lemma (x ∷ xs) xss = refl x ∷ ♯₁ concat-lemma xs xss