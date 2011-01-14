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
open import Function
open import Data.Nat as Nat
import Data.Nat.Properties as NatProp
open import Data.Product as Prod
open import Data.Sum
open import Data.Unit using (tt)
open import Relation.Binary
open import Relation.Nullary
open import Relation.Nullary.Negation
open import Relation.Unary
open RawMonad ¬¬-Monad
private
  module NatOrder   = DecTotalOrder       Nat.decTotalOrder
  module NatLattice = DistributiveLattice NatProp.distributiveLattice

------------------------------------------------------------------------
-- Mixed inductive/coinductive definition of "true infinitely often"

module Mixed where

  -- Inf P means that P is true for infinitely many natural numbers.

  data Inf (P : ℕ → Set) : Set where
    now  : (p : P 0) (inf : ∞ (Inf (P ∘ suc))) → Inf P
    skip :           (inf :    Inf (P ∘ suc) ) → Inf P

  up : ∀ {P} → Inf P → Inf (P ∘ suc)
  up (now p inf) = ♭ inf
  up (skip  inf) = inf

  filter₁ : ∀ {P Q} → Inf (P ∪ Q) → ¬ ∃ Q → Inf P
  filter₁ (now (inj₁ p) inf) ¬q = now p (♯ filter₁ (♭ inf) (¬q ∘ Prod.map suc id))
  filter₁ (now (inj₂ q) inf) ¬q = ⊥-elim (¬q (0 , q))
  filter₁ (skip         inf) ¬q = skip (filter₁ inf (¬q ∘ Prod.map suc id))

  filter₂ : ∀ {P Q} → (∀ n → Stable (∃ (Q ∘ _+_ n))) →
            Inf (P ∪ Q) → ¬ Inf P → Inf Q
  filter₂ stable p∪q ¬p =
    helper (stable 0 (¬p ∘ filter₁ p∪q)) stable p∪q ¬p
    where
    helper : ∀ {P Q} →
             ∃ Q → (∀ n → Stable (∃ (Q ∘ _+_ n))) →
             Inf (P ∪ Q) → ¬ Inf P → Inf Q
    helper (zero  , q) stable p∪q ¬p = now q (♯ filter₂     (stable ∘ suc) (up p∪q) (¬p ∘ skip))
    helper (suc i , q) stable p∪q ¬p = skip (helper (i , q) (stable ∘ suc) (up p∪q) (¬p ∘ skip))

  -- Note that the assumption of stability here follows from Markov's
  -- principle, if Q is decidable.

  commutes : ∀ {P Q} → (∀ n → Stable (∃ (Q ∘ _+_ n))) →
             Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
  commutes stable p∪q =
    call/cc λ ¬[p⊎q] →
    return $ inj₂ $ filter₂ stable p∪q (¬[p⊎q] ∘ inj₁)

------------------------------------------------------------------------
-- Alternative inductive/coinductive definition of "true infinitely
-- often"

module Alternative where

  open Mixed using (now; skip)

  data Always (P : ℕ → Set) : Set where
    now : (p : P 0) (next : ∞ (Always (P ∘ suc))) → Always P

  data Eventually (P : ℕ → Set) : Set where
    now   : (p : P 0) → Eventually P
    later : (p : Eventually (P ∘ suc)) → Eventually P

  Inf : (ℕ → Set) → Set
  Inf P = Always (λ n → Eventually (P ∘ _+_ n))

  -- This definition is equivalent to the previous one.

  up : ∀ P → Inf P → Inf (P ∘ suc)
  up _ (now _ inf) = ♭ inf

  ⇐ : ∀ {P} → Inf P → Mixed.Inf P
  ⇐     (now (now   p) inf) = now p (♯ ⇐ (♭ inf))
  ⇐ {P} (now (later p) inf) = skip (⇐ (now p (♯ up (P ∘ suc) (♭ inf))))

  ⇒ : ∀ {P} → Mixed.Inf P → Inf P
  ⇒ inf = now (eventually inf) (♯ ⇒ (Mixed.up inf))
    where
    eventually : ∀ {P} → Mixed.Inf P → Eventually P
    eventually (now p _)  = now p
    eventually (skip inf) = later (eventually inf)

------------------------------------------------------------------------
-- Functional/inductive definition of "true infinitely often"

module Functional where

  open Mixed using (now; skip)

  Inf : (ℕ → Set) → Set
  Inf P = ∀ i → ∃ λ j → i ≤ j × P j

  -- This definition is equivalent to the ones above.

  up : ∀ {P} → Inf P → Inf (P ∘ suc)
  up inf i with inf (suc i)
  ... | (._ , s≤s i≤j , p) = (_ , i≤j , p)

  ⇐ : ∀ {P} → Inf P → Mixed.Inf P
  ⇐ {P} inf with inf 0
  ... | (j , _ , p) = helper inf j p
    where
    helper : ∀ {P} → Inf P → ∀ j → P j → Mixed.Inf P
    helper inf zero    p = now p (♯ ⇐ (up inf))
    helper inf (suc n) p = skip (helper (up inf) n p)

  ⇒ : ∀ {P} → Mixed.Inf P → Inf P
  ⇒ (now p inf) zero    = (0 , z≤n , p)
  ⇒ (skip  inf) zero    = Prod.map suc (Prod.map (const z≤n) id) $ ⇒ inf zero
  ⇒ inf         (suc i) = Prod.map suc (Prod.map s≤s         id) $
                            ⇒ (Mixed.up inf) i

------------------------------------------------------------------------
-- Definition of "only true finitely often"

module Fin where

  open Mixed using (Inf; now; skip)

  Fin : (ℕ → Set) → Set
  Fin P = ∃ λ i → ∀ j → i ≤ j → ¬ P j

  up : ∀ {P : ℕ → Set} {i} →
       (∀ j → i ≤ j → ¬ P j) → (∀ j → i ≤ j → ¬ P (suc j))
  up ¬p = λ j i≤j → ¬p (suc j) (NatProp.≤-step i≤j)

  up′ : ∀ {P : ℕ → Set} {i} →
        (∀ j → suc i ≤ j → ¬ P j) → (∀ j → i ≤ j → ¬ P (suc j))
  up′ ¬p = λ j i≤j → ¬p (suc j) (s≤s i≤j)

  ⇐ : ∀ {P} → Fin P → ¬ Inf P
  ⇐ (zero  , fin) (now p inf) = fin 0 z≤n p
  ⇐ (zero  , fin) (skip  inf) = ⇐ (zero , λ j i≤j → fin (suc j) z≤n) inf
  ⇐ (suc i , fin) inf         = ⇐ (i , up′ fin) (Mixed.up inf)

  -- The other direction, ¬ Inf P → ¬ ¬ Fin P, is equivalent to a
  -- double-negation shift lemma. See NonConstructive.⇐ below.

  filter : ∀ {P Q} → Inf (P ∪ Q) → Fin P → Inf Q
  filter inf (i , fin) = filter′ inf i fin
    where
    filter′ : ∀ {P Q} → Inf (P ∪ Q) → ∀ i → (∀ j → i ≤ j → ¬ P j) → Inf Q
    filter′ (now (inj₁ p) inf) 0       fin = ⊥-elim (fin 0 z≤n p)
    filter′ (now (inj₁ p) inf) (suc i) fin = skip (filter′ (♭ inf) i (up′ fin))
    filter′ (now (inj₂ q) inf) i       fin = now q (♯ filter′ (♭ inf) i (up fin))
    filter′ (skip         inf) i       fin = skip (filter′ inf i (up fin))

  commutes : ∀ {P Q} → (¬ Inf P → ¬ ¬ Fin P) →
             Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
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
-- "Non-constructive" definition of "true infinitely often"

module NonConstructive where

  open Fin using (Fin)

  Inf : (ℕ → Set) → Set
  Inf P = ¬ Fin P

  commutes : ∀ {P Q} → Inf (P ∪ Q) → ¬ ¬ (Inf P ⊎ Inf Q)
  commutes p∪q =
    call/cc λ ¬[p⊎q] →
    (λ ¬p ¬q → ⊥-elim (p∪q $ Fin.∪-preserves ¬p ¬q))
      <$> ¬[p⊎q] ∘ inj₁ ⊛ ¬[p⊎q] ∘ inj₂

  up : ∀ {P} → Inf P → Inf (P ∘ suc)
  up {P} ¬fin (i , fin) = ¬fin (suc i , helper)
    where
    helper : ∀ j → 1 + i ≤ j → ¬ P j
    helper ._ (s≤s i≤j) = fin _ i≤j

  witness : ∀ {P} → Inf P → ¬ ¬ ∃ P
  witness ¬fin ¬p = ¬fin (0 , λ i _ Pi → ¬p (i , Pi))

  -- If we have a constructive proof of "true infinitely often", then
  -- we get a "non-constructive" proof as well.

  ⇒ : ∀ {P} → Functional.Inf P → Inf P
  ⇒ inf (i , fin) with inf i
  ... | (j , i≤j , p) = fin j i≤j p

  -- The other direction can be proved if we have a double-negation
  -- shift lemma.

  DoubleNegationShiftLemma₁ : Set₁
  DoubleNegationShiftLemma₁ =
    {P : ℕ → Set} →
    let Q = λ (i : ℕ) → ∃ λ j → i ≤ j × P j in
    (∀ i → ¬ ¬ Q i) → ¬ ¬ (∀ i → Q i)

  ⇐ : DoubleNegationShiftLemma₁ →
      ∀ {P} → Inf P → ¬ ¬ Functional.Inf P
  ⇐ shift ¬fin =
    shift (λ i ¬p → ¬fin (i , λ j i≤j p → ¬p (j , i≤j , p)))

  -- In fact, it is equivalent to this lemma.

  shift : (∀ {P} → Inf P → ¬ ¬ Functional.Inf P) →
          DoubleNegationShiftLemma₁
  shift hyp {P} p = hyp (uncurry (λ i fin → p i (helper fin)))
    where
    helper : ∀ {i} → ((j : ℕ) → i ≤ j → ¬ P j) → ¬ ∃ λ j → i ≤ j × P j
    helper fin (j , i≤j , p) = fin j i≤j p

  -- This lemma is in turn equivalent to the general double-negation
  -- shift property restricted to predicates which are downwards
  -- closed.

  DoubleNegationShiftLemma₂ : Set₁
  DoubleNegationShiftLemma₂ =
    {P : ℕ → Set} →
    (∀ {i j} → i ≥ j → P i → P j) →
    (∀ i → ¬ ¬ P i) → ¬ ¬ (∀ i → P i)

  ₁⇒₂ : DoubleNegationShiftLemma₁ → DoubleNegationShiftLemma₂
  ₁⇒₂ shift {P} downwards-closed ¬¬p =
    (λ hyp i → ⇦ i (hyp i)) <$> shift (λ i → ⇨ i <$> ¬¬p i)
    where
    Q : ℕ → Set
    Q i = ∀ j → j ≤ i → P j

    ⇦ : ∀ i → (∃ λ j → i ≤ j × Q j) → P i
    ⇦ i (j , i≤j , q) = q i i≤j

    ⇨ : ∀ i → P i → (∃ λ j → i ≤ j × Q j)
    ⇨ i p = (i , NatOrder.refl , λ j j≤i → downwards-closed j≤i p)

  ₂⇒₁ : DoubleNegationShiftLemma₂ → DoubleNegationShiftLemma₁
  ₂⇒₁ shift =
    shift (λ i≥j → Prod.map id (Prod.map (NatOrder.trans i≥j) id))

  -- Finally this lemma is equivalent to the general double-negation
  -- shift property. This was observed by Thierry Coquand.

  DoubleNegationShiftLemma : Set₁
  DoubleNegationShiftLemma =
    {P : ℕ → Set} →
    (∀ i → ¬ ¬ P i) → ¬ ¬ (∀ i → P i)

  ⇒₂ : DoubleNegationShiftLemma → DoubleNegationShiftLemma₂
  ⇒₂ shift _ = shift

  ₂⇒ : DoubleNegationShiftLemma₂ → DoubleNegationShiftLemma
  ₂⇒ shift {P} ∀¬¬P = ∀Q→∀P <$> ¬¬∀Q
    where
    Q : ℕ → Set
    Q i = ∀ {j} → j ≤′ i → P j

    ∀Q→∀P : (∀ i → Q i) → (∀ i → P i)
    ∀Q→∀P ∀Q = λ i → ∀Q i ≤′-refl

    Q-downwards-closed : ∀ {i j} → i ≥ j → Q i → Q j
    Q-downwards-closed i≥j Qi = λ j′≤j →
      Qi (NatProp.≤⇒≤′ (NatOrder.trans (NatProp.≤′⇒≤ j′≤j) i≥j))

    q-zero : P 0 → Q 0
    q-zero P0 ≤′-refl = P0

    q-suc : ∀ {i} → P (suc i) → Q i → Q (suc i)
    q-suc P1+i Qi ≤′-refl       = P1+i
    q-suc P1+i Qi (≤′-step j≤i) = Qi j≤i

    ∀¬¬Q : ∀ i → ¬ ¬ Q i
    ∀¬¬Q zero    = q-zero <$> ∀¬¬P zero
    ∀¬¬Q (suc i) = q-suc  <$> ∀¬¬P (suc i) ⊛ ∀¬¬Q i

    ¬¬∀Q : ¬ ¬ (∀ i → Q i)
    ¬¬∀Q = shift Q-downwards-closed ∀¬¬Q

------------------------------------------------------------------------
-- Definition of "true infinitely often" which uses double-negation

module DoubleNegated where

  open Fin using (Fin)

  infixl 4 _⟨$⟩_

  mutual

    data Inf (P : ℕ → Set) : Set₁ where
      now  : (p : P 0) (inf : ∞ (¬¬Inf (P ∘ suc))) → Inf P
      skip :           (inf :      Inf (P ∘ suc) ) → Inf P

    data ¬¬Inf (P : ℕ → Set) : Set₁ where
      _⟨$⟩_ : {A : Set} (f : A → Inf P) (m : ¬ ¬ A) → ¬¬Inf P

  -- ¬¬Inf is equivalent to the non-constructive definition given
  -- above.

  expand : ∀ {P} → ¬¬Inf P → ¬ ¬ Inf P
  expand (f ⟨$⟩ m) = λ ¬inf → m (¬inf ∘ f)

  ⇒¬¬ : ∀ {P} → NonConstructive.Inf P → ¬¬Inf P
  ⇒¬¬ {P} ¬fin = helper ¬fin ⟨$⟩ NonConstructive.witness ¬fin
    where
    helper : ∀ {P} → NonConstructive.Inf P → ∃ P → Inf P
    helper ¬fin (zero  , p) = now p (♯ ⇒¬¬ (NonConstructive.up ¬fin))
    helper ¬fin (suc i , p) =
      skip (helper (NonConstructive.up ¬fin) (i , p))

  ¬¬⇐ : ∀ {P} → ¬¬Inf P → NonConstructive.Inf P
  ¬¬⇐ ¬¬inf (i , fin) = ¬¬⇐′ ¬¬inf i fin
    where
    mutual
      ¬¬⇐′ : ∀ {P} → ¬¬Inf P → ∀ i → ¬ (∀ j → i ≤ j → ¬ P j)
      ¬¬⇐′ ¬¬inf i fin = ¬¬-map (helper i fin) (expand ¬¬inf) id

      helper : ∀ {P} → ∀ i → (∀ j → i ≤ j → ¬ P j) → ¬ Inf P
      helper i       ¬p (skip  inf)   = helper i (Fin.up ¬p) inf
      helper zero    ¬p (now p inf)   = ¬p 0 z≤n p
      helper (suc i) ¬p (now p ¬¬inf) =
        ¬¬⇐′ (♭ ¬¬inf) i (λ j i≤j → ¬p (suc j) (s≤s i≤j))

  ⇐ : ∀ {P} → Inf P → NonConstructive.Inf P
  ⇐ = ¬¬⇐ ∘ λ inf → const inf ⟨$⟩ return tt

  ⇒ : ∀ {P} → NonConstructive.Inf P → ¬ ¬ Inf P
  ⇒ = expand ∘ ⇒¬¬

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
-- used in Inf below, is not strictly positive. Furthermore several
-- definitions in DoubleNegated₂ are not accepted by the termination
-- checker (filter₁, filter₂ and ⇒).

{-
module DoubleNegated₂ where

  open DoubleNegated using (now; skip; _⟨$⟩_)

  data Inf (P : ℕ → Set) : Set where
    now  : (p : P 0) (inf : ∞ (¬ ¬ Inf (P ∘ suc))) → Inf P
    skip :           (inf :        Inf (P ∘ suc) ) → Inf P

  up : ∀ {P} → Inf P → ¬ ¬ Inf (P ∘ suc)
  up (now p inf) = ♭ inf
  up (skip  inf) = return inf

  filter₁ : ∀ {P Q} → Inf (P ∪ Q) → ¬ ∃ Q → Inf P
  filter₁ (now (inj₁ p) inf) ¬q = now p (♯ (♭ inf >>= λ inf →
                                            return (filter₁ inf (¬q ∘ Prod.map suc id))))
  filter₁ (now (inj₂ q) inf) ¬q = ⊥-elim (¬q (0 , q))
  filter₁ (skip         inf) ¬q = skip (filter₁ inf (¬q ∘ Prod.map suc id))

  filter₂ : ∀ {P Q} → ¬ ¬ Inf (P ∪ Q) → ¬ Inf P → ¬ ¬ Inf Q
  filter₂ ¬¬p∪q ¬p =
    stable >>= λ s   →
    ¬¬p∪q  >>= λ p∪q →
    return (helper (s (¬p ∘ filter₁ p∪q)) ¬¬p∪q ¬p)
    where
    helper : ∀ {P Q} → ∃ Q → ¬ ¬ Inf (P ∪ Q) → ¬ Inf P → Inf Q
    helper (zero  , q) p∪q ¬p = now q (♯ filter₂     (up =<< p∪q) (¬p ∘ skip))
    helper (suc i , q) p∪q ¬p = skip (helper (i , q) (up =<< p∪q) (¬p ∘ skip))

  ⇐ : ∀ {P} → Inf P → DoubleNegated.Inf P
  ⇐ (now p inf) = now p (♯ (⇐ ⟨$⟩ ♭ inf))
  ⇐ (skip  inf) = skip (⇐ inf)

  ⇒ : ∀ {P} → DoubleNegated.Inf P → Inf P
  ⇒ (now p inf) with ♭ inf
  ... | f ⟨$⟩ m = now p (♯ λ ¬inf → m (λ x → ¬inf (⇒ (f x))))
  ⇒ (skip  inf) = skip (⇒ inf)

  ¬¬⇒ : ∀ {P} → DoubleNegated.¬¬Inf P → ¬ ¬ Inf P
  ¬¬⇒ inf = λ ¬inf → DoubleNegated.expand inf (¬inf ∘ ⇒)
-}
