------------------------------------------------------------------------
-- Breadth-first labelling of trees
------------------------------------------------------------------------

module BreadthFirst where

open import Coinduction
open import Data.Function
open import Data.Unit
open import Data.List.NonEmpty using () renaming (_++_ to _++⁺_)
open import Data.Colist using ([]; _∷_; concat)
import Relation.Binary.PropositionalEquality as PropEq
open PropEq using () renaming (refl to ≡-refl)

open import BreadthFirst.Universe
open import BreadthFirst.Programs
open import BreadthFirst.Lemmas
open import Tree using (Tree; map)
open import Stream using (Stream; _≺_)

------------------------------------------------------------------------
-- Breadth-first labelling

label′ : ∀ {k} {a : U k} {B} → Prog (tree a) → Stream B →
         Prog (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
label′ t ls = lab t (↓ ♯₁ (⌈ ls ⌉ ≺ snd (label′ t ls)))

label : ∀ {A B} → Tree A → Stream B → Tree B
label {A} t ls = ⟦ fst (label′ ⟦ tree ⌈ A ⌉ ∣ t ⟧⁻¹ ls) ⟧

------------------------------------------------------------------------
-- Breadth-first labelling preserves the shape of the tree

shape-preserved′ : ∀ {k} {a : U k} {B} (t : Prog (tree a))
                   (lss : Prog (stream ⌈ Stream B ⌉)) →
                   Eq (tree ⌈ ⊤ ⌉) (map (const tt) ⟦ fst (lab t lss) ⟧)
                                   (map (const tt) ⟦ t ⟧)
shape-preserved′ t lss with whnf t
... | leaf       = leaf
... | node l _ r with whnf lss
...              | ⌈ x ≺ ls ⌉ ≺ lss′ =
  node (♯₁ shape-preserved′ l lss′) ⌈ ≡-refl ⌉
       (♯₁ shape-preserved′ r _)

shape-preserved : ∀ {A B} (t : Tree A) (ls : Stream B) →
                  Eq (tree ⌈ ⊤ ⌉) (map (const tt) (label t ls))
                                  (map (const tt) t)
shape-preserved {A} t ls = ⟦
  map (const tt) (label t ls)           ≈⟨ shape-preserved′ ⟦ a ∣ t ⟧⁻¹ _ ⟩
  map (const tt) (reflect (reify a t))  ≈⟨ map-cong (const tt)
                                                    (reflect-reify a t) ⟩
  map (const tt) t                      ∎ ⟧≈
  where a = tree ⌈ A ⌉

------------------------------------------------------------------------
-- Breadth-first labelling uses the right labels

invariant : ∀ {k} {a : U k} {B} (t : Prog (tree a)) lss →
            EqProg (stream (stream ⌈ B ⌉))
                   ⟦ lss ⟧
                   (zipWith _⁺++∞_ ⟦ flatten (fst (lab t lss)) ⟧
                                   ⟦ snd (lab t lss) ⟧)
invariant t lss with whnf t
... | leaf       = ⟦ lss ⟧ ∎
... | node l _ r with whnf lss
...              | ⌈ x ≺ ls ⌉ ≺ lss′ =
  (⌈ ≡-refl ⌉ ≺ ♯₁ refl (♭ ls)) ≺ ♯₁ (
    ⟦ lss′ ⟧                                    ≊⟨ invariant l lss′ ⟩
    zipWith _⁺++∞_ ⟦ flatten (fst l′) ⟧
                   ⟦ snd l′ ⟧                   ≊⟨ zipWith-cong ⁺++∞-cong
                                                     (⟦ flatten (fst l′) ⟧ ∎)
                                                     (invariant r (snd l′)) ⟩
    zipWith _⁺++∞_
      ⟦ flatten (fst l′) ⟧
      (zipWith _⁺++∞_ ⟦ flatten (fst r′) ⟧
                      ⟦ snd r′ ⟧)               ≈⟨ zip-++-assoc (flatten (fst l′))
                                                                (flatten (fst r′))
                                                                ⟦ snd r′ ⟧ ⟩
    zipWith _⁺++∞_
      ⟦ longZipWith _++⁺_ (flatten (fst l′))
                          (flatten (fst r′)) ⟧
      ⟦ snd r′ ⟧                                ∎)
  where
  l′ = lab l lss′
  r′ = lab r (snd l′)

prefix-lemma : ∀ {k} {a : U k} xs xss yss →
               Eq (stream (stream a))
                  (xs ≺ ♯ xss) (zipWith _⁺++∞_ yss xss) →
               PrefixOfProg a (concat yss) xs
prefix-lemma xs xss         []         _            = []
prefix-lemma xs (xs′ ≺ xss) (ys ∷ yss) (xs≈ ≺ xss≈) =
  concat (ys ∷ yss)      ≋⟨ concat-lemma ys yss ⟩
  ys ⁺++ concat (♭ yss)  ⊑⟨ ⁺++-mono ys (♯₁ prefix-lemma xs′ (♭ xss) (♭ yss) ⟦ lemma ⟧≈) ⟩
  ys ⁺++∞ xs′            ≈⟨ sym xs≈ ⟩
  xs                     ∎
  where
  lemma =
    xs′ ≺ _ {- ♯ ♭ xss -}           ≈⟨ refl xs′ ≺ ♯₁ refl (♭ xss) ⟩
    xs′ ≺ xss                       ≈⟨ ♭₁ xss≈ ⟩
    zipWith _⁺++∞_ (♭ yss) (♭ xss)  ∎

is-prefix : ∀ {A B} (t : Tree A) (ls : Stream B) →
            PrefixOf ⌈ B ⌉ (concat (lift flatten (label t ls))) ls
is-prefix {A} {B} t ls = ⟦
  concat ⟦ flatten fst-l  ⟧  ≋⟨ concat-cong ⟦ flatten-cong fst-l (fst l) (right-inverse ⟦ fst l ⟧) ⟧≈ ⟩
  concat ⟦ flatten (fst l)⟧  ⊑⟨ prefix-lemma ls ⟦ snd l ⟧ ⟦ flatten (fst l) ⟧
                                  ⟦ ls ≺ _ {- ♯ ⟦ snd l ⟧ -}                      ≈⟨ refl ls ≺ ♯₁ refl ⟦ snd l ⟧ ⟩
                                    ⟦ ↓_ {a = stream ⌈ Stream B ⌉}
                                         (♯₁ (⌈ ls ⌉ ≺ snd (label′ t′ ls))) ⟧     ≊⟨ invariant t′ _ ⟩
                                    zipWith _⁺++∞_ ⟦ flatten (fst l) ⟧ ⟦ snd l ⟧  ∎ ⟧≈ ⟩
  ls                         ∎ ⟧⊑
  where
  t′    = ⟦ tree ⌈ A ⌉ ∣ t ⟧⁻¹
  l     = label′ t′ ls
  fst-l = ⟦ _ ∣ ⟦ fst l ⟧ ⟧⁻¹
