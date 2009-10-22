------------------------------------------------------------------------
-- This module proves that the context-sensitive language aⁿbⁿcⁿ can
-- be recognised
------------------------------------------------------------------------

module TotalParserCombinators.NotOnlyContextFree where

open import Algebra
open import Coinduction
open import Data.Bool using (Bool; true; false)
open import Data.Function
open import Data.List as List using (List; []; _∷_; _++_; [_])
private
  module ListMonoid {A} = Monoid (List.monoid A)
open import Data.Nat as Nat using (ℕ; zero; suc; _+_)
import Data.Nat.Properties as NatProp
open NatProp.SemiringSolver
private
  module NatCS = CommutativeSemiring NatProp.commutativeSemiring
open import Data.Product
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open ≡-Reasoning

import TotalParserCombinators

------------------------------------------------------------------------
-- The alphabet

data Tok : Set where
  a b c : Tok

_≟_ : Decidable (_≡_ {A = Tok})
a ≟ a = yes refl
a ≟ b = no λ()
a ≟ c = no λ()
b ≟ a = no λ()
b ≟ b = yes refl
b ≟ c = no λ()
c ≟ a = no λ()
c ≟ b = no λ()
c ≟ c = yes refl

open TotalParserCombinators Tok _≟_

------------------------------------------------------------------------
-- An auxiliary definition and some boring lemmas

infixr 8 _^_

_^_ : Tok → ℕ → List Tok
_^_ = flip List.replicate

private

  ^-lemma : ∀ t n → t ^ suc n ≡ t ^ n ++ [ t ]
  ^-lemma t zero    = refl
  ^-lemma t (suc n) = cong (_∷_ t) (^-lemma t n)

  shallow-comm : ∀ i n → i + suc n ≡ suc (i + n)
  shallow-comm i n =
    solve 2 (λ i n → i :+ (con 1 :+ n) := con 1 :+ i :+ n) refl i n

  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-string : ℕ → ℕ → List Tok
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-string n i = (a ^ (i + n) ++ b ^ (i + n)) ++ c ^ n

  rearranging-lemma : ∀ i n →
    aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-string (suc n) i ≡
    ((a ^ (suc i + n) ++ b ^ (suc i + n)) ++ c ^ n) ++ [ c ]
  rearranging-lemma i n with i + suc n | shallow-comm i n
  ... | ._ | refl = begin
    (a ^ (suc i + n) ++ b ^ (suc i + n)) ++ c ^ suc n
      ≡⟨ cong (λ s → (a ^ (suc i + n) ++ b ^ (suc i + n)) ++ s)
              (^-lemma c n) ⟩
    (a ^ (suc i + n) ++ b ^ (suc i + n)) ++ (c ^ n ++ [ c ])
      ≡⟨ sym (ListMonoid.assoc
                (a ^ (suc i + n) ++ b ^ (suc i + n)) _ _) ⟩
    ((a ^ (suc i + n) ++ b ^ (suc i + n)) ++ c ^ n) ++ [ c ]
      ∎

  identity-lemma : ∀ i →
    a ^ i ++ b ^ i ≡ (a ^ (i + 0) ++ b ^ (i + 0)) ++ []
  identity-lemma i = begin
    a ^ i ++ b ^ i
      ≡⟨ cong (λ i → a ^ i ++ b ^ i) (sym (proj₂ NatCS.+-identity i)) ⟩
    a ^ (i + 0) ++ b ^ (i + 0)
      ≡⟨ sym (proj₂ ListMonoid.identity _) ⟩
    (a ^ (i + 0) ++ b ^ (i + 0)) ++ []
      ∎

------------------------------------------------------------------------
-- Recognising exactly i "things"

-- exactly i p defines the language { s₁s₂…s_i | s_j ∈ p, 1 ≤ j ≤ i }.

exactly-index : Bool → ℕ → Bool
exactly-index _ zero    = _
exactly-index _ (suc _) = _

exactly : ∀ {n} (i : ℕ) → P n → P (exactly-index n i)
exactly zero    p = ε
exactly (suc i) p = ♯? p · ♯? (exactly i p)

-- Some lemmas relating _^_, exactly and tok.

exactly-tok-complete : ∀ t i → t ^ i ∈ exactly i (tok t)
exactly-tok-complete t zero    = ε
exactly-tok-complete t (suc i) =
  cast refl lem tok · exactly-tok-complete t i
  where lem = sym (♭?♯? (exactly-index false i))

exactly-tok-sound : ∀ t i {s} → s ∈ exactly i (tok t) → s ≡ t ^ i
exactly-tok-sound t zero    ε         = refl
exactly-tok-sound t (suc i) (t∈ · s∈)
  with cast refl (♭?♯? (exactly-index false i)) t∈
... | tok = cong (_∷_ t) (exactly-tok-sound t i s∈)

------------------------------------------------------------------------
-- aⁿbⁿcⁿ

-- The context-sensitive language { aⁿbⁿcⁿ | n ∈ ℕ } can be recognised
-- using the parser combinators defined in this development.

aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-index : ℕ → Bool
aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-index _ = _

aⁿ⁺ⁱbⁿ⁺ⁱcⁿ : (i : ℕ) → P (aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-index i)
aⁿ⁺ⁱbⁿ⁺ⁱcⁿ i = ⟪ ♯ aⁿ⁺ⁱbⁿ⁺ⁱcⁿ (suc i) ⟫ · ♯? (tok c)
             ∣ ♯? (exactly i (tok a)) · ♯? (exactly i (tok b))

aⁿbⁿcⁿ : P true
aⁿbⁿcⁿ = aⁿ⁺ⁱbⁿ⁺ⁱcⁿ 0

-- Let us prove that aⁿbⁿcⁿ is correctly defined.

aⁿbⁿcⁿ-string : ℕ → List Tok
aⁿbⁿcⁿ-string n = (a ^ n ++ b ^ n) ++ c ^ n

aⁿbⁿcⁿ-complete : ∀ n → aⁿbⁿcⁿ-string n ∈ aⁿbⁿcⁿ
aⁿbⁿcⁿ-complete n = aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-complete n 0
  where
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-complete : ∀ n i → aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-string n i ∈ aⁿ⁺ⁱbⁿ⁺ⁱcⁿ i
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-complete zero i
    with (a ^ (i + 0) ++ b ^ (i + 0)) ++ [] | identity-lemma i
  ... | ._ | refl = ∣ʳ {p₁ = ⟪ _ ⟫ · _} (helper a · helper b)
    where
    helper = λ (t : Tok) →
      cast refl (sym (♭?♯? (exactly-index false i)))
           (exactly-tok-complete t i)
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-complete (suc n) i
    with aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-string (suc n) i | rearranging-lemma i n
  ... | ._ | refl =
    ∣ˡ (aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-complete n (suc i) · cast refl lem tok)
    where lem = sym (♭?♯? (aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-index (suc i)))

aⁿbⁿcⁿ-sound : ∀ {s} → s ∈ aⁿbⁿcⁿ → ∃ λ n → s ≡ aⁿbⁿcⁿ-string n
aⁿbⁿcⁿ-sound = aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-sound 0
  where
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-sound : ∀ {s} i →
                     s ∈ aⁿ⁺ⁱbⁿ⁺ⁱcⁿ i →
                     ∃ λ n → s ≡ aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-string n i
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-sound i (∣ˡ (s∈ · t∈))
    with cast refl (♭?♯? (aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-index (suc i))) t∈
  ... | tok with aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-sound (suc i) s∈
  ... | (n , refl) = (suc n , sym (rearranging-lemma i n))
  aⁿ⁺ⁱbⁿ⁺ⁱcⁿ-sound i (∣ʳ (_·_ {s₁} {s₂} s₁∈ s₂∈)) = 0 , (begin
    s₁ ++ s₂
      ≡⟨ cong₂ _++_ (exactly-tok-sound a i
                      (cast refl (♭?♯? (exactly-index false i)) s₁∈))
                    (exactly-tok-sound b i
                      (cast refl (♭?♯? (exactly-index false i)) s₂∈)) ⟩
    a ^ i ++ b ^ i
      ≡⟨ identity-lemma i ⟩
    (a ^ (i + 0) ++ b ^ (i + 0)) ++ []
      ∎)
