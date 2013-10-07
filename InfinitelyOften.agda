------------------------------------------------------------------------
-- Various definitions of "true infinitely often", and some proofs
-- showing that this property commutes with binary sums (in the
-- double-negation monad, and sometimes with extra assumptions)
------------------------------------------------------------------------

module InfinitelyOften where

open import Algebra
open import Category.Monad
open import Coinduction
open import Data.Empty
open import Data.Nat as Nat
import Data.Nat.Properties as NatProp
open import Data.Product as Prod hiding (map)
open import Data.Sum hiding (map)
open import Data.Unit using (tt)
open import Function
open import Function.Equality using (_⟨$⟩_)
open import Function.Equivalence
  using (_⇔_; equivalence; module Equivalence)
import Function.Related as Related
open import Level using (Lift; lift; lower)
open import Relation.Binary hiding (_⇒_)
open import Relation.Nullary
open import Relation.Nullary.Negation
import Relation.Nullary.Universe as Univ
open import Relation.Unary
private
  open module M {f} = RawMonad {f = f} ¬¬-Monad
  module NatOrder   = DecTotalOrder       Nat.decTotalOrder
  module NatLattice = DistributiveLattice NatProp.distributiveLattice

------------------------------------------------------------------------
-- Above

module Above where

  -- P Above i holds if P holds somewhere above i (perhaps at i
  -- itself).

  _Above_ : (ℕ → Set) → (ℕ → Set)
  P Above i = ∃ λ j → i ≤ j × P j

  -- Conversion lemma.

  move-suc : ∀ {P i} → P Above suc i ⇔ (P ∘ suc) Above i
  move-suc {P} {i} = equivalence ⇒ ⇐
    where
    ⇒ : P Above suc i → (P ∘ suc) Above i
    ⇒ (.(1 + j) , s≤s {n = j} i≤j , P[1+j]) = (j , i≤j , P[1+j])

    ⇐ : (P ∘ suc) Above i → P Above suc i
    ⇐ (j , i≤j , P[1+j]) = (1 + j , s≤s i≤j , P[1+j])

  -- A closure lemma.

  stable-up :
    ∀ {P} →
    (∀ i → Stable (P Above i)) → (∀ i → Stable ((P ∘ suc) Above i))
  stable-up stable i ¬¬P∘suc⇑i =
    Equivalence.to move-suc ⟨$⟩
      stable (1 + i) (_⟨$⟩_ (Equivalence.from move-suc) <$> ¬¬P∘suc⇑i)

------------------------------------------------------------------------
-- Has upper bound

module Has-upper-bound where

  open Above using (_Above_)

  -- P Has-upper-bound i means that P does not hold for any j ≥ i.

  _Has-upper-bound_ : (ℕ → Set) → (ℕ → Set)
  P Has-upper-bound i = ∀ j → i ≤ j → ¬ P j

  -- A closure lemma.

  up : ∀ {P i} → P Has-upper-bound i → (P ∘ suc) Has-upper-bound i
  up ¬p = λ j i≤j → ¬p (suc j) (NatProp.≤-step i≤j)

  -- A conversion lemma.

  move-suc : ∀ {P i} →
             P Has-upper-bound suc i ⇔ (P ∘ suc) Has-upper-bound i
  move-suc {P} {i} = equivalence ⇒ ⇐
    where
    ⇒ : P Has-upper-bound suc i → (P ∘ suc) Has-upper-bound i
    ⇒ P↯[1+i] j i≤j P[1+j] = P↯[1+i] (1 + j) (s≤s i≤j) P[1+j]

    ⇐ : (P ∘ suc) Has-upper-bound i → P Has-upper-bound suc i
    ⇐ P∘suc↯i .(1 + j) (s≤s {n = j} i≤j) Pj = P∘suc↯i j i≤j Pj

  -- _Has-upper-bound_ and _Above_ are mutually inconsistent.

  mutually-inconsistent :
    ∀ {P i} → P Has-upper-bound i ⇔ ¬ (P Above i)
  mutually-inconsistent {P} {i} = equivalence ⇒ ⇐
    where
    ⇒ : P Has-upper-bound i → ¬ (P Above i)
    ⇒ P↯i (j , i≤j , Pj) = P↯i j i≤j Pj

    ⇐ : ¬ (P Above i) → P Has-upper-bound i
    ⇐ ¬P⇑i j i≤j Pj = ¬P⇑i (j , i≤j , Pj)

------------------------------------------------------------------------
-- Below

module Below where

  open Above using (_Above_)

  -- P Below i holds if P holds everywhere below i (including at i).

  _Below_ : (ℕ → Set) → (ℕ → Set)
  P Below i = ∀ j → j ≤ i → P j

  -- _Below_ P has a comonadic structure (at least if morphism
  -- equality is trivial).

  map : ∀ {P Q} → P ⊆ Q → _Below_ P ⊆ _Below_ Q
  map P⊆Q P⇓i j j≤i = P⊆Q (P⇓i j j≤i)

  counit : ∀ {P} → _Below_ P ⊆ P
  counit P⇓i = P⇓i _ NatOrder.refl

  cojoin : ∀ {P} → _Below_ P ⊆ _Below_ (_Below_ P)
  cojoin P⇓i = λ j j≤i k k≤j → P⇓i _ (NatOrder.trans k≤j j≤i)

  -- _Above_ (_Below_ P) is pointwise equivalent to _Below_ P.

  ⇑⇓⇔⇓ : ∀ {P} i → (_Below_ P) Above i ⇔ P Below i
  ⇑⇓⇔⇓ {P} i = equivalence ⇒ ⇐
    where
    ⇒ : (_Below_ P) Above i → P Below i
    ⇒ (j , i≤j , P⇓j) k k≤i = P⇓j k (NatOrder.trans k≤i i≤j)

    ⇐ : P Below i → (_Below_ P) Above i
    ⇐ P⇓i = (i , NatOrder.refl , P⇓i)

------------------------------------------------------------------------
-- Mixed inductive/coinductive definition of "true infinitely often"

module Mixed where

  open Above using (_Above_)

  -- Inf P means that P is true for infinitely many natural numbers.

  data Inf (P : ℕ → Set) : Set where
    now  : (p : P 0) (inf : ∞ (Inf (P ∘ suc))) → Inf P
    skip :           (inf :    Inf (P ∘ suc) ) → Inf P

  -- Inf commutes with binary sums in the double-negation monad if one
  -- of the predicates satisfies a certain stability condition.

  up : ∀ {P} → Inf P → Inf (P ∘ suc)
  up (now p inf) = ♭ inf
  up (skip  inf) = inf

  filter₁ : ∀ {P Q} → Inf (P ∪ Q) → ¬ ∃ Q → Inf P
  filter₁ (now (inj₁ p) inf) ¬q = now p (♯ filter₁ (♭ inf) (¬q ∘ Prod.map suc id))
  filter₁ (now (inj₂ q) inf) ¬q = ⊥-elim (¬q (0 , q))
  filter₁ (skip         inf) ¬q = skip (filter₁ inf (¬q ∘ Prod.map suc id))

  filter₂ : ∀ {P Q} → (∀ i → Stable (Q Above i)) →
            Inf (P ∪ Q) → ¬ Inf P → Inf Q
  filter₂ {P} {Q} stable p∪q ¬p = helper witness stable p∪q ¬p
    where
    open Related.EquationalReasoning

    witness : ∃ Q
    witness = Prod.map id proj₂ $ stable 0 (
      ¬ (Q Above 0)  ∼⟨ contraposition (Prod.map id (_,_ z≤n)) ⟩
      ¬ ∃ Q          ∼⟨ filter₁ p∪q ⟩
      Inf P          ∼⟨ ¬p ⟩
      ⊥              ∎)

    helper : ∀ {P Q} →
             ∃ Q → (∀ i → Stable (Q Above i)) →
             Inf (P ∪ Q) → ¬ Inf P → Inf Q
    helper (zero  , q) stable p∪q ¬p = now q (♯ filter₂     (Above.stable-up stable) (up p∪q) (¬p ∘ skip))
    helper (suc i , q) stable p∪q ¬p = skip (helper (i , q) (Above.stable-up stable) (up p∪q) (¬p ∘ skip))

  commutes : ∀ {P Q} → (∀ i → Stable (Q Above i)) →
             Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
  commutes stable p∪q =
    call/cc λ ¬[p⊎q] →
    return $ inj₂ $ filter₂ stable p∪q (¬[p⊎q] ∘ inj₁)

------------------------------------------------------------------------
-- Alternative inductive/coinductive definition of "true infinitely
-- often"

module Alternative where

  open Mixed using (now; skip)

  -- Always P means that P holds for every natural number.

  data Always (P : ℕ → Set) : Set where
    now : (p : P 0) (next : ∞ (Always (P ∘ suc))) → Always P

  -- Eventually P means that P holds for some natural number.

  data Eventually (P : ℕ → Set) : Set where
    now   : (p : P 0) → Eventually P
    later : (p : Eventually (P ∘ suc)) → Eventually P

  -- Inf P means that P is true for infinitely many natural numbers.

  Inf : (ℕ → Set) → Set
  Inf P = Always (λ n → Eventually (P ∘ _+_ n))

  -- This definition is equivalent to the previous one.

  up : ∀ P → Inf P → Inf (P ∘ suc)
  up _ (now _ inf) = ♭ inf

  equivalent : ∀ {P} → Inf P ⇔ Mixed.Inf P
  equivalent = equivalence ⇒ ⇐
    where
    ⇒ : ∀ {P} → Inf P → Mixed.Inf P
    ⇒ (now p inf) = ⇒′ p (♭ inf)
      where
      ⇒′ : ∀ {P} → Eventually P → Inf (P ∘ suc) → Mixed.Inf P
      ⇒′     (now   p) inf = now p (♯ ⇒ inf)
      ⇒′ {P} (later p) inf = skip (⇒′ p (up (P ∘ suc) inf))

    ⇐ : ∀ {P} → Mixed.Inf P → Inf P
    ⇐ inf = now (eventually inf) (♯ ⇐ (Mixed.up inf))
      where
      eventually : ∀ {P} → Mixed.Inf P → Eventually P
      eventually (now p _)  = now p
      eventually (skip inf) = later (eventually inf)

------------------------------------------------------------------------
-- Functional/inductive definition of "true infinitely often"

module Functional where

  open Mixed using (now; skip)
  open Above using (_Above_)

  -- Inf P means that P is true for infinitely many natural numbers.

  Inf : (ℕ → Set) → Set
  Inf P = ∀ i → P Above i

  -- This definition is equivalent to the ones above.

  up : ∀ {P} → Inf P → Inf (P ∘ suc)
  up ∀iP⇑i i = Equivalence.to Above.move-suc ⟨$⟩ ∀iP⇑i (suc i)

  equivalent : ∀ {P} → Inf P ⇔ Mixed.Inf P
  equivalent = equivalence ⇒ ⇐
    where
    ⇒ : ∀ {P} → Inf P → Mixed.Inf P
    ⇒ {P} inf with inf 0
    ... | (j , _ , p) = helper inf j p
      where
      helper : ∀ {P} → Inf P → ∀ j → P j → Mixed.Inf P
      helper inf zero    p = now p (♯ ⇒ (up inf))
      helper inf (suc n) p = skip (helper (up inf) n p)

    ⇐ : ∀ {P} → Mixed.Inf P → Inf P
    ⇐ (now p inf) zero    = (0 , z≤n , p)
    ⇐ (skip  inf) zero    = Prod.map suc (Prod.map (const z≤n) id) $ ⇐ inf zero
    ⇐ inf         (suc i) = Prod.map suc (Prod.map s≤s         id) $
                              ⇐ (Mixed.up inf) i

  -- Inf is a functor (at least if morphism equality is trivial).

  map : ∀ {P₁ P₂} → P₁ ⊆ P₂ → Inf P₁ → Inf P₂
  map P₁⊆P₂ inf = λ i → Prod.map id (Prod.map id P₁⊆P₂) (inf i)

------------------------------------------------------------------------
-- Definition of "only true finitely often"

module Fin where

  open Mixed using (now; skip)
  open Has-upper-bound using (_Has-upper-bound_)

  -- Fin P means that P is only true for finitely many natural
  -- numbers.

  Fin : (ℕ → Set) → Set
  Fin P = ∃ λ i → P Has-upper-bound i

  -- Fin implies the negation of Mixed.Inf.

  ⇐ : ∀ {P} → Fin P → ¬ Mixed.Inf P
  ⇐ = uncurry ⇐′
    where
    ⇐′ : ∀ {P} i → P Has-upper-bound i → ¬ Mixed.Inf P
    ⇐′ zero    fin (now p inf) = fin 0 z≤n p
    ⇐′ zero    fin (skip  inf) = ⇐′ zero (λ j i≤j → fin (suc j) z≤n) inf
    ⇐′ (suc i) fin inf         =
      ⇐′ i (Equivalence.to Has-upper-bound.move-suc ⟨$⟩ fin)
         (Mixed.up inf)

  -- The other direction (with a double-negated conclusion) implies
  -- that Mixed.Inf commutes with binary sums (in the double-negation
  -- monad).

  filter : ∀ {P Q} → Mixed.Inf (P ∪ Q) → Fin P → Mixed.Inf Q
  filter inf (i , fin) = filter′ inf i fin
    where
    filter′ : ∀ {P Q} →
              Mixed.Inf (P ∪ Q) →
              ∀ i → P Has-upper-bound i → Mixed.Inf Q
    filter′ (now (inj₁ p) inf) 0       fin = ⊥-elim (fin 0 z≤n p)
    filter′ (now (inj₁ p) inf) (suc i) fin = skip (filter′ (♭ inf) i (Equivalence.to Has-upper-bound.move-suc ⟨$⟩ fin))
    filter′ (now (inj₂ q) inf) i       fin = now q (♯ filter′ (♭ inf) i (Has-upper-bound.up fin))
    filter′ (skip         inf) i       fin = skip (filter′ inf i (Has-upper-bound.up fin))

  commutes : ∀ {P Q} → (¬ Mixed.Inf P → ¬ ¬ Fin P) →
             Mixed.Inf (P ∪ Q) → ¬ ¬ (Mixed.Inf P ⊎ Mixed.Inf Q)
  commutes ⇒ p∪q =
    call/cc               λ ¬[p⊎q] →
    ⇒ (¬[p⊎q] ∘ inj₁) >>= λ fin →
    return $ inj₂ (filter p∪q fin)

  -- Fin is preserved by binary sums.

  ∪-preserves : ∀ {P Q} → Fin P → Fin Q → Fin (P ∪ Q)
  ∪-preserves {P} {Q} (i , ¬p) (j , ¬q) = (i ⊔ j , helper)
    where
    open ≤-Reasoning

    helper : ∀ k → i ⊔ j ≤ k → ¬ (P ∪ Q) k
    helper k i⊔j≤k (inj₁ p) = ¬p k (begin
      i      ≤⟨ NatProp.m≤m⊔n i j ⟩
      i ⊔ j  ≤⟨ i⊔j≤k ⟩
      k      ∎) p
    helper k i⊔j≤k (inj₂ q) = ¬q k (begin
      j      ≤⟨ NatProp.m≤m⊔n j i ⟩
      j ⊔ i  ≡⟨ NatLattice.∧-comm j i ⟩
      i ⊔ j  ≤⟨ i⊔j≤k ⟩
      k      ∎) q

------------------------------------------------------------------------
-- Double-negation shift lemmas

module Double-negation-shift where

  open Below using (_Below_)

  -- General double-negation shift property.

  DNS : (ℕ → Set) → Set
  DNS P = (∀ i → ¬ ¬ P i) → ¬ ¬ (∀ i → P i)

  -- DNS holds for stable predicates.

  Stable⇒DNS : ∀ {P} → (∀ i → Stable (P i)) → DNS P
  Stable⇒DNS stable ∀¬¬P = λ ¬∀P → ¬∀P (λ i → stable i (∀¬¬P i))

  -- DNS follows from excluded middle.

  EM⇒DNS : ∀ {P} → Excluded-Middle Level.zero → DNS P
  EM⇒DNS {P} em hyp = return hyp′
    where
    hyp′ : ∀ i → P i
    hyp′ i = decidable-stable em (hyp i)

  -- DNS follows from the double-negation of excluded middle.

  ¬¬EM⇒DNS : ∀ {P} → ¬ ¬ Excluded-Middle Level.zero → DNS P
  ¬¬EM⇒DNS em hyp =
    ¬¬-map lower (em >>= λ em → ¬¬-map lift (EM⇒DNS em hyp))

  -- DNS respects predicate equivalence.

  respects : ∀ {P₁ P₂} → (∀ i → P₁ i ⇔ P₂ i) → DNS P₁ → DNS P₂
  respects P₁⇔P₂ dns ∀i¬¬P₂i ¬∀iP₂i =
    dns (λ i ¬P₁i → ∀i¬¬P₂i i (λ P₂i →
                      ¬P₁i (Equivalence.from (P₁⇔P₂ i) ⟨$⟩ P₂i)))
        (λ ∀iP₁i → ¬∀iP₂i (λ i → Equivalence.to (P₁⇔P₂ i) ⟨$⟩ ∀iP₁i i))

  -- Double-negation shift property restricted to predicates which are
  -- downwards closed.

  DNS⇓ : (ℕ → Set) → Set
  DNS⇓ P =
    (∀ {i j} → i ≥ j → P i → P j) →
    (∀ i → ¬ ¬ P i) → ¬ ¬ (∀ i → P i)

  -- Certain instances of DNS imply other instances of DNS⇓, and vice
  -- versa.

  DNS⇒DNS⇓ : ∀ {P} → DNS (_Below_ P) → DNS⇓ P
  DNS⇒DNS⇓ {P} shift downwards-closed ∀i¬¬Pi =
    _∘_ Below.counit <$> shift (λ i → unit <$> ∀i¬¬Pi i)
    where
    unit : P ⊆ _Below_ P
    unit Pi j j≤i = downwards-closed j≤i Pi

  -- The following lemma is due to Thierry Coquand (but the proof,
  -- including any inelegance, is due to me).

  DNS⇓⇒DNS : ∀ {P} → DNS⇓ (_Below_ P) → DNS P
  DNS⇓⇒DNS {P} shift ∀¬¬P = _∘_ Below.counit <$> ¬¬∀P⇓
    where
    P⇓-downwards-closed : ∀ {i j} → i ≥ j → P Below i → P Below j
    P⇓-downwards-closed i≥j P⇓i = λ j′ j′≤j →
      P⇓i j′ (NatOrder.trans j′≤j i≥j)

    Q : ℕ → Set
    Q i = ∀ {j} → j ≤′ i → P j

    q-zero : P 0 → Q 0
    q-zero P0 ≤′-refl = P0

    q-suc : ∀ {i} → P (suc i) → Q i → Q (suc i)
    q-suc P1+i Qi ≤′-refl       = P1+i
    q-suc P1+i Qi (≤′-step j≤i) = Qi j≤i

    ∀¬¬Q : ∀ i → ¬ ¬ Q i
    ∀¬¬Q zero    = q-zero <$> ∀¬¬P zero
    ∀¬¬Q (suc i) = q-suc  <$> ∀¬¬P (suc i) ⊛ ∀¬¬Q i

    ∀¬¬P⇓ : ∀ i → ¬ ¬ (P Below i)
    ∀¬¬P⇓ i = (λ Qi j j≤i → Qi (NatProp.≤⇒≤′ j≤i)) <$> ∀¬¬Q i

    ¬¬∀P⇓ : ¬ ¬ (∀ i → P Below i)
    ¬¬∀P⇓ = shift P⇓-downwards-closed ∀¬¬P⇓

------------------------------------------------------------------------
-- "Non-constructive" definition of "true infinitely often"

module NonConstructive where

  open Fin using (Fin)
  open Above using (_Above_)
  open Below using (_Below_)
  open Has-upper-bound using (_Has-upper-bound_)
  open Double-negation-shift using (DNS; DNS⇓)

  -- Inf P means that P is true for infinitely many natural numbers.

  Inf : (ℕ → Set) → Set
  Inf P = ¬ Fin P

  -- Inf commutes with binary sums (in the double-negation monad).

  commutes : ∀ {P Q} → Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
  commutes p∪q =
    call/cc λ ¬[p⊎q] →
    (λ ¬p ¬q → ⊥-elim (p∪q $ Fin.∪-preserves ¬p ¬q))
      <$> ¬[p⊎q] ∘ inj₁ ⊛ ¬[p⊎q] ∘ inj₂

  -- Inf is a functor (at least if morphism equality is trivial).

  map : ∀ {P₁ P₂} → P₁ ⊆ P₂ → Inf P₁ → Inf P₂
  map P₁⊆P₂ ¬fin = λ fin →
    ¬fin (Prod.map id (λ never j i≤j P₁j → never j i≤j (P₁⊆P₂ P₁j)) fin)

  -- If we have a constructive proof of "true infinitely often", then
  -- we get a "non-constructive" proof as well.

  ⇒ : ∀ {P} → Functional.Inf P → Inf P
  ⇒ inf (i , fin) with inf i
  ... | (j , i≤j , p) = fin j i≤j p

  -- The other direction can be proved iff we have a double-negation
  -- shift lemma.

  Other-direction : (ℕ → Set) → Set
  Other-direction P = Inf P → ¬ ¬ Functional.Inf P

  equivalent₁ : ∀ {P} → Other-direction P ⇔ DNS (_Above_ P)
  equivalent₁ = equivalence ⇒shift shift⇒
    where
    shift⇒ : ∀ {P} → DNS (_Above_ P) → Other-direction P
    shift⇒ shift ¬fin =
      shift (λ i ¬p →
        ¬fin (i , Equivalence.from
                    Has-upper-bound.mutually-inconsistent ⟨$⟩ ¬p))

    ⇒shift : ∀ {P} → Other-direction P → DNS (_Above_ P)
    ⇒shift hyp p =
      hyp (uncurry (λ i fin →
        p i (Equivalence.to
               Has-upper-bound.mutually-inconsistent ⟨$⟩ fin)))

  equivalent₂ : ∀ {P} → Other-direction (_Below_ P) ⇔ DNS P
  equivalent₂ {P} = equivalence ⇒shift shift⇒
    where
    shift⇒ : DNS P → Other-direction (_Below_ P)
    shift⇒ shift inf ¬inf =
      shift (λ i ¬Pi →
               inf (i , λ j i≤j ∀k≤j[Pk] → ¬Pi (∀k≤j[Pk] i i≤j)))
            (λ ∀iPi → ¬inf (λ i → i , NatOrder.refl , λ j j≤i → ∀iPi j))

    ⇒shift : ∀ {P} → Other-direction (_Below_ P) → DNS P
    ⇒shift {P} =
      Other-direction (_Below_ P)                 ∼⟨ (λ other₁ →
        Inf (_Below_ (_Below_ P))                       ∼⟨ map Below.counit ⟩
        Inf (_Below_ P)                                 ∼⟨ other₁ ⟩
        ¬ ¬ Functional.Inf (_Below_ P)                  ∼⟨ _<$>_ (Functional.map Below.cojoin) ⟩
        ¬ ¬ Functional.Inf (_Below_ (_Below_ P))        ∎) ⟩
      Other-direction (_Below_ (_Below_ P))       ∼⟨ _⟨$⟩_ (Equivalence.to equivalent₁) ⟩
      DNS (_Above_ (_Below_ (_Below_ P)))         ∼⟨ Double-negation-shift.respects Below.⇑⇓⇔⇓ ⟩
      DNS (_Below_ (_Below_ P))                   ∼⟨ Double-negation-shift.DNS⇒DNS⇓ ⟩
      DNS⇓ (_Below_ P)                            ∼⟨ Double-negation-shift.DNS⇓⇒DNS ⟩
      DNS P                                       ∎
      where open Related.EquationalReasoning

  equivalent : (∀ P → Other-direction P) ⇔ (∀ P → DNS P)
  equivalent =
    equivalence (λ other P → _⟨$⟩_ (Equivalence.to   equivalent₂)
                                   (other (_Below_ P)))
                (λ shift P → _⟨$⟩_ (Equivalence.from equivalent₁)
                                   (shift (_Above_ P)))

  -- Some lemmas used below.

  up : ∀ {P} → Inf P → Inf (P ∘ suc)
  up =
    contraposition
      (Prod.map suc (_⟨$⟩_ (Equivalence.from Has-upper-bound.move-suc)))

  witness : ∀ {P} → Inf P → ¬ ¬ ∃ P
  witness ¬fin ¬p = ¬fin (0 , λ i _ Pi → ¬p (i , Pi))

------------------------------------------------------------------------
-- Definition of "true infinitely often" which uses double-negation

module DoubleNegated where

  open Fin using (Fin)
  open Has-upper-bound using (_Has-upper-bound_)

  infixl 4 _⟪$⟫_

  mutual

    -- Inf P means that P is true for infinitely many natural numbers.

    data Inf (P : ℕ → Set) : Set₁ where
      now  : (p : P 0) (inf : ∞ (¬¬Inf (P ∘ suc))) → Inf P
      skip :           (inf :      Inf (P ∘ suc) ) → Inf P

    data ¬¬Inf (P : ℕ → Set) : Set₁ where
      _⟪$⟫_ : {A : Set} (f : A → Inf P) (m : ¬ ¬ A) → ¬¬Inf P

  -- ¬¬Inf is equivalent to the non-constructive definition given
  -- above.

  expand : ∀ {P} → ¬¬Inf P → ¬ ¬ Inf P
  expand (f ⟪$⟫ m) = λ ¬inf → m (¬inf ∘ f)

  ¬¬equivalent : ∀ {P} → NonConstructive.Inf P ⇔ ¬¬Inf P
  ¬¬equivalent = equivalence ⇒ ⇐
    where
    ⇒ : ∀ {P} → NonConstructive.Inf P → ¬¬Inf P
    ⇒ ¬fin = helper ¬fin ⟪$⟫ NonConstructive.witness ¬fin
      where
      helper : ∀ {P} → NonConstructive.Inf P → ∃ P → Inf P
      helper ¬fin (zero  , p) = now p (♯ ⇒ (NonConstructive.up ¬fin))
      helper ¬fin (suc i , p) =
        skip (helper (NonConstructive.up ¬fin) (i , p))

    ⇐ : ∀ {P} → ¬¬Inf P → NonConstructive.Inf P
    ⇐ ¬¬inf (i , fin) = ⇐′ ¬¬inf i fin
      where
      mutual
        ⇐′ : ∀ {P} → ¬¬Inf P → ∀ i → ¬ P Has-upper-bound i
        ⇐′ ¬¬inf i fin = ¬¬-map (helper i fin) (expand ¬¬inf) id

        helper : ∀ {P} → ∀ i → P Has-upper-bound i → ¬ Inf P
        helper i       ¬p (skip  inf)   = helper i (Has-upper-bound.up ¬p) inf
        helper zero    ¬p (now p inf)   = ¬p 0 z≤n p
        helper (suc i) ¬p (now p ¬¬inf) =
          ⇐′ (♭ ¬¬inf) i (λ j i≤j → ¬p (suc j) (s≤s i≤j))

  -- Inf is equivalent to the non-constructive definition given above
  -- (in the double-negation monad).

  ⇐ : ∀ {P} → Inf P → NonConstructive.Inf P
  ⇐ {P} =
    Inf P                  ∼⟨ (λ inf → const inf ⟪$⟫ return tt) ⟩
    ¬¬Inf P                ∼⟨ _⟨$⟩_ (Equivalence.from ¬¬equivalent) ⟩
    NonConstructive.Inf P  ∎
    where open Related.EquationalReasoning

  ⇒ : ∀ {P} → NonConstructive.Inf P → ¬ ¬ Inf P
  ⇒ {P} =
    NonConstructive.Inf P  ∼⟨ _⟨$⟩_ (Equivalence.to ¬¬equivalent) ⟩
    ¬¬Inf P                ∼⟨ expand ⟩
    ¬ ¬ Inf P              ∎
    where open Related.EquationalReasoning

  equivalent : ∀ {P} → ¬ ¬ (NonConstructive.Inf P ⇔ Inf P)
  equivalent {P} =
    (λ ⇒′ → equivalence (⇒′ ∘ lift) ⇐) <$>
      Univ.¬¬-pull (Univ._⇒_ _ Univ.Id) (λ inf → ⇒ (lower inf))

  -- Inf commutes with binary sums (in the double-negation monad).

  commutes : ∀ {P Q} → Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
  commutes {P} {Q} p∪q =
    negated-stable $ ¬¬-map helper $ NonConstructive.commutes (⇐ p∪q)
    where
    helper : NonConstructive.Inf P ⊎ NonConstructive.Inf Q →
             ¬ ¬ (Inf P ⊎ Inf Q)
    helper (inj₁ p) = λ ¬p∪q → ⇒ p (¬p∪q ∘ inj₁)
    helper (inj₂ q) = λ ¬p∪q → ⇒ q (¬p∪q ∘ inj₂)

-- You may wonder why double-negation is introduced in a roundabout
-- way in ¬¬Inf above. The reason is that the more direct definition,
-- used in DoubleNegated₂ below, is not strictly positive. Furthermore
-- DoubleNegated₂.equivalent is not accepted by the termination
-- checker.

{-
module DoubleNegated₂ where

  open DoubleNegated using (now; skip; _⟪$⟫_)

  data Inf (P : ℕ → Set) : Set where
    now  : (p : P 0) (inf : ∞ (¬ ¬ Inf (P ∘ suc))) → Inf P
    skip :           (inf :        Inf (P ∘ suc) ) → Inf P

  equivalent : ∀ {P} → DoubleNegated.Inf P ⇔ Inf P
  equivalent = equivalence ⇒ ⇐
    where
    ⇐ : ∀ {P} → Inf P → DoubleNegated.Inf P
    ⇐ (now p inf) = now p (♯ (⇐ ⟪$⟫ ♭ inf))
    ⇐ (skip  inf) = skip (⇐ inf)

    ⇒ : ∀ {P} → DoubleNegated.Inf P → Inf P
    ⇒ (now p inf) with ♭ inf
    ... | f ⟪$⟫ m = now p (♯ λ ¬inf → m (λ x → ¬inf (⇒ (f x))))
    ⇒ (skip  inf) = skip (⇒ inf)
-}
