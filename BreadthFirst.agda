------------------------------------------------------------------------
-- Breadth-first labelling of trees
------------------------------------------------------------------------

module BreadthFirst where

open import Coinduction
open import Function
open import Data.Unit
open import Data.List.NonEmpty using (_⁺++⁺_)
open import Data.Colist using ([]; _∷_; concat)
open import Relation.Binary.PropositionalEquality as PropEq
  using () renaming (refl to ≡-refl)

open import BreadthFirst.Universe
open import BreadthFirst.Programs
open import BreadthFirst.Lemmas
open import Tree using (Tree; leaf; node; map)
open import Stream using (Stream; _≺_)

------------------------------------------------------------------------
-- Breadth-first labelling

label′ : ∀ {A B} → Tree A → Stream B →
         ElP (tree ⌈ B ⌉ ⊗ stream ⌈ Stream B ⌉)
label′ t ls = lab t (↓ (⌈ ls ⌉ ≺ ♯ snd (label′ t ls)))

label : ∀ {A B} → Tree A → Stream B → Tree B
label t ls = ⟦ fst (label′ t ls) ⟧

------------------------------------------------------------------------
-- Breadth-first labelling preserves the shape of the tree

shape-preserved′ : ∀ {A B} (t : Tree A)
                   (lss : ElP (stream ⌈ Stream B ⌉)) →
                   Eq (tree ⌈ ⊤ ⌉) (map (const tt) ⟦ fst (lab t lss) ⟧)
                                   (map (const tt) t)
shape-preserved′ leaf         lss = leaf
shape-preserved′ (node l _ r) lss with whnf lss
... | ⌈ x ≺ ls ⌉ ≺ lss′ =
  node (♯ shape-preserved′ (♭ l) (♭ lss′)) ⌈ ≡-refl ⌉
       (♯ shape-preserved′ (♭ r) (snd (lab (♭ l) (♭ lss′))))

shape-preserved : ∀ {A B} (t : Tree A) (ls : Stream B) →
                  Eq (tree ⌈ ⊤ ⌉) (map (const tt) (label t ls))
                                  (map (const tt) t)
shape-preserved t ls = shape-preserved′ t (↓ (⌈ ls ⌉ ≺ _))

------------------------------------------------------------------------
-- Breadth-first labelling uses the right labels

invariant : ∀ {A B} (t : Tree A) lss →
            EqP (stream (stream ⌈ B ⌉))
                ⟦ lss ⟧
                (zipWith _⁺++∞_ ⟦ flatten ⟦ fst (lab t lss) ⟧ ⟧
                                ⟦ snd (lab t lss) ⟧)
invariant leaf         lss = ⟦ lss ⟧ ∎
invariant (node l _ r) lss with whnf lss
... | ⌈ x ≺ ls ⌉ ≺ lss′ =
  (⌈ ≡-refl ⌉ ≺ ♯ refl (♭ ls)) ≺ ♯ (
    ⟦ ♭ lss′ ⟧                                     ≊⟨ invariant (♭ l) (♭ lss′) ⟩
    zipWith _⁺++∞_ ⟦ flatten ⟦ fst l′ ⟧ ⟧
                   ⟦ snd l′ ⟧                      ≊⟨ zipWith-cong ⁺++∞-cong
                                                        (⟦ flatten ⟦ fst l′ ⟧ ⟧ ∎)
                                                        (invariant (♭ r) (snd l′)) ⟩
    zipWith _⁺++∞_
      ⟦ flatten ⟦ fst l′ ⟧ ⟧
      (zipWith _⁺++∞_ ⟦ flatten ⟦ fst r′ ⟧ ⟧
                      ⟦ snd r′ ⟧)                  ≈⟨ zip-++-assoc (flatten ⟦ fst l′ ⟧)
                                                                   (flatten ⟦ fst r′ ⟧)
                                                                   ⟦ snd r′ ⟧ ⟩
    zipWith _⁺++∞_
      ⟦ longZipWith _⁺++⁺_ (flatten ⟦ fst l′ ⟧)
                           (flatten ⟦ fst r′ ⟧) ⟧
      ⟦ snd r′ ⟧                                   ∎)
  where
  l′ = lab (♭ l) (♭ lss′)
  r′ = lab (♭ r) (snd l′)

prefix-lemma : ∀ {a} xs xss yss →
               Eq (stream (stream a))
                  (xs ≺ ♯ xss) (zipWith _⁺++∞_ yss xss) →
               PrefixOfP a (concat yss) xs
prefix-lemma xs xss         []         _            = []
prefix-lemma xs (xs′ ≺ xss) (ys ∷ yss) (xs≈ ≺ xss≈) =
  concat (ys ∷ yss)      ≋⟨ concat-lemma ys yss ⟩
  ys ⁺++ concat (♭ yss)  ⊑⟨ ⁺++-mono ys (♯ prefix-lemma xs′ (♭ xss) (♭ yss) ⟦ lemma ⟧≈) ⟩
  ys ⁺++∞ xs′            ≈⟨ sym xs≈ ⟩
  xs                     ∎
  where
  lemma =
    xs′ ≺ _ {- ♯ ♭ xss -}           ≈⟨ refl xs′ ≺ ♯ refl (♭ xss) ⟩
    xs′ ≺ xss                       ≈⟨ ♭ xss≈ ⟩
    zipWith _⁺++∞_ (♭ yss) (♭ xss)  ∎

is-prefix : ∀ {A B} (t : Tree A) (ls : Stream B) →
            PrefixOf ⌈ B ⌉ (concat ⟦ flatten (label t ls) ⟧) ls
is-prefix {B = B} t ls =
  ⟦ prefix-lemma ls ⟦ snd l ⟧ ⟦ flatten ⟦ fst l ⟧ ⟧
      ⟦ ls ≺ _ {- ♯ ⟦ snd l ⟧ -}                        ≈⟨ refl ls ≺ ♯ refl ⟦ snd l ⟧ ⟩
        ⟦ ↓ (⌈ ls ⌉ ≺ _) ⟧                              ≊⟨ invariant t (↓ ⌈ ls ⌉ ≺ _) ⟩
        zipWith _⁺++∞_ ⟦ flatten ⟦ fst l ⟧ ⟧ ⟦ snd l ⟧  ∎ ⟧≈ ⟧⊑
  where l = label′ t ls
