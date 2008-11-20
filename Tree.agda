------------------------------------------------------------------------
-- Possibly infinite binary trees
------------------------------------------------------------------------

module Tree where

open import Relation.Binary.PropositionalEquality

mutual

  data TreeD (A : Set) : Set where
    leaf : TreeD A
    node : (l : Tree A) (x : A) (r : Tree A) -> TreeD A

  codata Tree (A : Set) : Set where
    tree : (d : TreeD A) -> Tree A

destruct : forall {A} -> Tree A -> TreeD A
destruct (tree d) = d

map : forall {A B} -> (A -> B) -> Tree A -> Tree B
map f t with destruct t
map f t | leaf       ~ tree leaf
map f t | node l x r ~ tree (node (map f l) (f x) (map f r))

mutual

  data _≈D_ {A : Set} : (t₁ t₂ : TreeD A) -> Set where
    leaf : leaf ≈D leaf
    node : forall {l₁ l₂ x₁ x₂ r₁ r₂}
           (l≈ : l₁ ≈ l₂) (x≡ : x₁ ≡ x₂) (r≈ : r₁ ≈ r₂) ->
           node l₁ x₁ r₁ ≈D node l₂ x₂ r₂

  codata _≈_ {A : Set} (t₁ t₂ : Tree A) : Set where
    tree : (d≈ : destruct t₁ ≈D destruct t₂) -> t₁ ≈ t₂

destruct≈ : forall {A} {t₁ t₂ : Tree A} ->
            t₁ ≈ t₂ -> destruct t₁ ≈D destruct t₂
destruct≈ (tree eq) = eq

refl : forall {A} (t : Tree A) -> t ≈ t
refl (tree leaf)         ~ tree leaf
refl (tree (node l x r)) ~ tree (node (refl l) ≡-refl (refl r))

trans : forall {A} {t₁ t₂ t₃ : Tree A} ->
        t₁ ≈ t₂ -> t₂ ≈ t₃ -> t₁ ≈ t₃
trans t₁≈t₂ t₂≈t₃ with destruct≈ t₁≈t₂ | destruct≈ t₂≈t₃
trans {t₁ = tree ._} {tree ._} {tree ._} t₁≈t₂ t₂≈t₃ | leaf          | leaf             ~ tree leaf
trans {t₁ = tree ._} {tree ._} {tree ._} t₁≈t₂ t₂≈t₃ | node l≈ x≡ r≈ | node l≈′ x≡′ r≈′ ~
  tree (node (trans l≈ l≈′) (≡-trans x≡ x≡′) (trans r≈ r≈′))

map-cong : forall {A B} (f : A -> B) {t₁ t₂ : Tree A} ->
           t₁ ≈ t₂ -> map f t₁ ≈ map f t₂
map-cong f t₁≈t₂ with destruct≈ t₁≈t₂
map-cong f {tree ._} {tree ._} t₁≈t₂ | leaf          ~ tree leaf
map-cong f {tree ._} {tree ._} t₁≈t₂ | node l≈ x≡ r≈ ~
  tree (node (map-cong f l≈) (≡-cong f x≡) (map-cong f r≈))
