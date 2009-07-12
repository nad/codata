------------------------------------------------------------------------
-- Total parser combinators
------------------------------------------------------------------------

module TotalParserCombinators where

open import Algebra
open import Coinduction
open import Data.Bool using (Bool; true; false; not; _∧_; _∨_)
import Data.Bool.Properties as Bool
private
  module Bool-CS = CommutativeSemiring Bool.commutativeSemiring-∧-∨
open import Data.Function
open import Data.List using (List; []; _∷_; _++_; [_])
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.String using () renaming (String to Tok)
open DecSetoid Data.String.decSetoid using (_≟_)

infixl 10 _·_
infixl  5 _∣_

------------------------------------------------------------------------
-- Conditional coinduction

∞? : Bool → Set → Set
∞? true  = ∞
∞? false = id₁

♯? : ∀ (b : Bool) {A} → A → ∞? b A
♯? true  = ♯_
♯? false = id

♭? : ∀ (b : Bool) {A} → ∞? b A → A
♭? true  = ♭
♭? false = id

-- A lemma.

♭?♯? : ∀ b {A} {x : A} → ♭? b (♯? b x) ≡ x
♭?♯? true  = refl
♭?♯? false = refl

------------------------------------------------------------------------
-- Parser combinators

-- The index is true if the corresponding language contains the empty
-- string (is nullable).

data P : Bool → Set where
  ∅        : P false
  ε        : P true
  tok      : Tok → P false
  _∣_      : ∀ {n₁ n₂} → P n₁ →              P n₂  → P (n₁ ∨ n₂)
  _·_      : ∀ {n₁ n₂} → P n₁ → ∞? (not n₁) (P n₂) → P (n₁ ∧ n₂)
  nonempty : ∀ {n} → P n → P false

------------------------------------------------------------------------
-- Semantics

-- The semantics is defined inductively: s ∈ p iff the string s is
-- contained in the language defined by p.

infix 4 _∈_

data _∈_ : ∀ {n} → List Tok → P n → Set where
  ε        : [] ∈ ε
  tok      : ∀ {t} → [ t ] ∈ tok t
  ∣ˡ       : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
             s ∈ p₁ → s ∈ p₁ ∣ p₂
  ∣ʳ       : ∀ {s n₁ n₂} {p₁ : P n₁} {p₂ : P n₂} →
             s ∈ p₂ → s ∈ p₁ ∣ p₂
  _·_      : ∀ {s₁ s₂ n₁ n₂} {p₁ : P n₁} {p₂ : ∞? (not n₁) (P n₂)} →
             s₁ ∈ p₁ → s₂ ∈ ♭? (not n₁) p₂ →
             s₁ ++ s₂ ∈ p₁ · p₂
  nonempty : ∀ {n t s} {p : P n} →
             t ∷ s ∈ p → t ∷ s ∈ nonempty p

-- A lemma.

cast : ∀ {n} {p p′ : P n} {s} → p ≡ p′ → s ∈ p → s ∈ p′
cast refl s∈ = s∈

------------------------------------------------------------------------
-- Example: Kleene star

-- This definition works for any argument parser.

_⋆ : ∀ {n} → P n → P true
p ⋆ = ε ∣ nonempty p · ♯ (p ⋆)

-- The intended semantics of the Kleene star.

infixr 5 _∷_
infix  4 _∈[_]⋆

data _∈[_]⋆ {n} : List Tok → P n → Set where
  []  : ∀ {p}       → [] ∈[ p ]⋆
  _∷_ : ∀ {s₁ s₂ p} → s₁ ∈ p → s₂ ∈[ p ]⋆ → s₁ ++ s₂ ∈[ p ]⋆

-- The definition of _⋆ above is correct.

⋆-sound : ∀ {s n} {p : P n} → s ∈ p ⋆ → s ∈[ p ]⋆
⋆-sound (∣ˡ ε)                    = []
⋆-sound (∣ʳ (nonempty pr₁ · pr₂)) = pr₁ ∷ ⋆-sound pr₂

⋆-complete : ∀ {s n} {p : P n} → s ∈[ p ]⋆ → s ∈ p ⋆
⋆-complete []                    = ∣ˡ ε
⋆-complete (_∷_ {[]}    pr₁ pr₂) = ⋆-complete pr₂
⋆-complete (_∷_ {_ ∷ _} pr₁ pr₂) =
  ∣ʳ {n₁ = true} (nonempty pr₁ · ⋆-complete pr₂)

------------------------------------------------------------------------
-- Nullability

-- The nullability index is correct.

⇒ : ∀ {n} {p : P n} → [] ∈ p → n ≡ true
⇒ pr = ⇒′ pr refl
  where
  ⇒′ : ∀ {n s} {p : P n} → s ∈ p → s ≡ [] → n ≡ true
  ⇒′ ε                     refl = refl
  ⇒′ tok                   ()
  ⇒′ (∣ˡ pr₁)              refl with ⇒ pr₁
  ⇒′ (∣ˡ pr₁)              refl | refl = refl
  ⇒′ (∣ʳ pr₂)              refl with ⇒ pr₂
  ⇒′ (∣ʳ {n₁ = n₁} pr₂)    refl | refl = proj₂ Bool-CS.zero n₁
  ⇒′ (_·_ {[]}    pr₁ pr₂) refl = cong₂ _∧_ (⇒ pr₁) (⇒ pr₂)
  ⇒′ (_·_ {_ ∷ _} pr₁ pr₂) ()
  ⇒′ (nonempty p)          ()

⇐ : ∀ {n} (p : P n) → n ≡ true → [] ∈ p
⇐ ∅                            ()
⇐ ε                            refl = ε
⇐ (tok t)                      ()
⇐ (_∣_ {true}           p₁ p₂) refl = ∣ˡ (⇐ p₁ refl)
⇐ (_∣_ {false} {true}   p₁ p₂) refl = ∣ʳ {p₁ = p₁} (⇐ p₂ refl)
⇐ (_∣_ {false} {false}  p₁ p₂) ()
⇐ (_·_ {true}  p₁ p₂)          refl = ⇐ p₁ refl · ⇐ p₂ refl
⇐ (_·_ {false} p₁ p₂)          ()
⇐ (nonempty p)                 ()

-- We can decide if the empty string belongs to a given language.

nullable? : ∀ {n} (p : P n) → Dec ([] ∈ p)
nullable? {true}  p = yes (⇐ p refl)
nullable? {false} p = no helper
  where
  helper : ¬ [] ∈ p
  helper []∈p with ⇒ []∈p
  ... | ()

------------------------------------------------------------------------
-- Derivative

-- The index of the derivative. Mostly left implicit.

∂n : ∀ {n} → P n → Tok → Bool
∂n ∅                   t = _
∂n ε                   t = _
∂n (tok t′)            t with t ≟ t′
∂n (tok .t)            t | yes refl = _
∂n (tok t′)            t | no  t≢t′ = _
∂n (p₁ ∣ p₂)           t = _
∂n (_·_ {true}  p₁ p₂) t = _
∂n (_·_ {false} p₁ p₂) t = _
∂n (nonempty p)        t = _

-- ∂ p t is the "derivative" of p with respect to t. It is specified
-- by the equivalence s ∈ ∂ p t ⇔ t ∷ s ∈ p (proved below).

∂ : ∀ {n} (p : P n) (t : Tok) → P (∂n p t)
∂ ∅                   t = ∅
∂ ε                   t = ∅
∂ (tok t′)            t with t ≟ t′
∂ (tok .t)            t | yes refl = ε
∂ (tok t′)            t | no  t≢t′ = ∅
∂ (p₁ ∣ p₂)           t = ∂ p₁ t ∣ ∂ p₂ t
∂ (_·_ {true} p₁ p₂)  t = ∂ p₁ t · ♯? (not (∂n p₁ t)) p₂
                        ∣ ∂ p₂ t
∂ (_·_ {false} p₁ p₂) t = ∂ p₁ t · ♯? (not (∂n p₁ t)) (♭ p₂)
∂ (nonempty p)        t = ∂ p t

-- ∂ is correct.

∂-sound : ∀ {s n} {p : P n} {t} → s ∈ ∂ p t → t ∷ s ∈ p
∂-sound = ∂-sound′ _ _
  where
  ∂-sound′ : ∀ {s n} (p : P n) t → s ∈ ∂ p t → t ∷ s ∈ p
  ∂-sound′ ∅                   t ()
  ∂-sound′ ε                   t ()
  ∂-sound′ (tok t′)            t _              with t ≟ t′
  ∂-sound′ (tok .t)            t ε              | yes refl = tok
  ∂-sound′ (tok t′)            t ()             | no  t≢t′
  ∂-sound′ (p₁ ∣ p₂)           t (∣ˡ ∈₁)        = ∣ˡ (∂-sound′ p₁ t ∈₁)
  ∂-sound′ (p₁ ∣ p₂)           t (∣ʳ ∈₂)        = ∣ʳ {p₁ = p₁} (∂-sound′ p₂ t ∈₂)
  ∂-sound′ (_·_ {true}  p₁ p₂) t (∣ˡ (∈₁ · ∈₂)) = ∂-sound′ p₁ t ∈₁ · cast (♭?♯? (not (∂n p₁ t))) ∈₂
  ∂-sound′ (_·_ {true}  p₁ p₂) t (∣ʳ ∈₂)        = ⇐ p₁ refl · ∂-sound′ p₂ t ∈₂
  ∂-sound′ (_·_ {false} p₁ p₂) t (∈₁ · ∈₂)      = ∂-sound′ p₁ t ∈₁ · cast (♭?♯? (not (∂n p₁ t))) ∈₂
  ∂-sound′ (nonempty p)        t ∈              = nonempty (∂-sound ∈)

∂-complete : ∀ {s n} {p : P n} {t} → t ∷ s ∈ p → s ∈ ∂ p t
∂-complete {t = t} t∷s∈ = ∂-complete′ _ t∷s∈ refl
  where
  ∂-complete′ : ∀ {s s′ n} (p : P n) → s′ ∈ p → s′ ≡ t ∷ s → s ∈ ∂ p t
  ∂-complete′         ∅        ()  refl
  ∂-complete′         ε        ()  refl
  ∂-complete′         (tok t′) _   refl with t ≟ t′
  ∂-complete′         (tok .t) tok refl | yes refl = ε
  ∂-complete′ {[]}    (tok .t) tok refl | no  t≢t′ with t≢t′ refl
  ∂-complete′ {[]}    (tok .t) tok refl | no  t≢t′ | ()
  ∂-complete′ {_ ∷ _} (tok t′) ()  refl | no  t≢t′
  ∂-complete′ (p₁ ∣ p₂)           (∣ˡ ∈₁)              refl = ∣ˡ (∂-complete ∈₁)
  ∂-complete′ (p₁ ∣ p₂)           (∣ʳ ∈₂)              refl = ∣ʳ {p₁ = ∂ p₁ t} (∂-complete ∈₂)
  ∂-complete′ (_·_ {true}  p₁ p₂) (_·_ {[]}     ∈₁ ∈₂) refl = ∣ʳ {p₁ = ∂ p₁ t · _} (∂-complete ∈₂)
  ∂-complete′ (_·_ {true}  p₁ p₂) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∣ˡ (∂-complete ∈₁ · cast (sym (♭?♯? (not (∂n p₁ t)))) ∈₂)
  ∂-complete′ (_·_ {false} p₁ p₂) (_·_ {[]}     ∈₁ ∈₂) refl with ⇒ ∈₁
  ∂-complete′ (_·_ {false} p₁ p₂) (_·_ {[]}     ∈₁ ∈₂) refl | ()
  ∂-complete′ (_·_ {false} p₁ p₂) (_·_ {._ ∷ _} ∈₁ ∈₂) refl = ∂-complete ∈₁ · cast (sym (♭?♯? (not (∂n p₁ t)))) ∈₂
  ∂-complete′ (nonempty p)        (nonempty ∈)         refl = ∂-complete ∈

------------------------------------------------------------------------
-- _∈_ is decidable

-- _∈?_ runs a parser (recogniser). Note that the result is yes or no
-- plus a /proof/ verifying that the answer is correct.

infix 4 _∈?_

_∈?_ : ∀ {n} (s : List Tok) (p : P n) → Dec (s ∈ p)
[]    ∈? p = nullable? p
t ∷ s ∈? p with s ∈? ∂ p t
t ∷ s ∈? p | yes s∈∂pt = yes (∂-sound s∈∂pt)
t ∷ s ∈? p | no  s∉∂pt = no  (s∉∂pt ∘ ∂-complete)
