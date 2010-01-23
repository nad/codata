------------------------------------------------------------------------
-- Some examples
------------------------------------------------------------------------

-- The conclusion I draw from the examples below is that, unless you
-- really need to use this framework, it is probably wise to stay away
-- from it. Unless, perhaps, if someone codes up lots of automation
-- for it (note that I did not even finish the definition of the
-- Hamming numbers).

module Contractive.Examples where

open import Coinduction
open import Data.Nat
open import Data.Nat.Properties
open import Data.Stream
import Data.Vec as Vec
open Vec using (_∷_; [])
open import Function
open import Contractive
import Contractive.Stream as S
open import StreamProg using (Ord; lt; eq; gt; merge)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

open COFE (S.cofe 0)

fibF : ContractiveFun (S.cofe 0)
fibF = record
  { F             = F
  ; isContractive = isCon _ _ _
  }
  where
  F = λ xs → 0 ∷ ♯ (1 ∷ ♯ zipWith _+_ xs (tail xs))

  lemma₁ : ∀ _∙_ (xs ys : Stream ℕ) n →
           take n (zipWith _∙_ xs ys) ≡
           Vec.zipWith _∙_ (take n xs) (take n ys)
  lemma₁ _∙_ _        _        zero    = refl
  lemma₁ _∙_ (x ∷ xs) (y ∷ ys) (suc n) =
    cong (_∷_ (x ∙ y)) (lemma₁ _∙_ (♭ xs) (♭ ys) n)

  lemma₂ : ∀ (xs ys : Stream ℕ) n →
           Eq n xs ys → take n xs ≡ take n ys
  lemma₂ _        _         zero    _   = refl
  lemma₂ (x ∷ xs) ( y ∷ ys) (suc n) hyp
    with cong Vec.head hyp | take n (♭ xs) | lemma₂ (♭ xs) (♭ ys) n (cong Vec.tail hyp)
  lemma₂ (x ∷ xs) (.x ∷ ys) (suc n) hyp | refl | .(take n (♭ ys)) | refl = refl

  isCon : ∀ (xs ys : Stream ℕ) n →
          (∀ {m} → m <′ n → Eq m xs ys) →
          Eq n (F xs) (F ys)
  isCon _        _        zero    _   = refl
  isCon (x ∷ xs) (y ∷ ys) (suc n) hyp = cong (λ zs → 0 ∷ 1 ∷ zs) (begin
    take n (zipWith _+_ (x ∷ xs) (♭ xs))               ≡⟨ lemma₁ _+_ (x ∷ xs) (♭ xs) n ⟩
    Vec.zipWith _+_ (take n (x ∷ xs)) (take n (♭ xs))  ≡⟨ cong₂ (Vec.zipWith _+_)
                                                                (lemma₂ _ _ n (hyp ≤′-refl))
                                                                (cong Vec.tail (hyp ≤′-refl)) ⟩
    Vec.zipWith _+_ (take n (y ∷ ys)) (take n (♭ ys))  ≡⟨ sym $ lemma₁ _+_ (y ∷ ys) (♭ ys) n ⟩
    take n (zipWith _+_ (y ∷ ys) (♭ ys))               ∎)

fib : Stream ℕ
fib = ContractiveFun.fixpoint fibF

hammingF : ContractiveFun (S.cofe 0)
hammingF = record
  { F             = F
  ; isContractive = isCon _ _ _
  }
  where
  toOrd : ∀ {m n} → Ordering m n → Ord
  toOrd (less _ _)    = lt
  toOrd (equal _)     = eq
  toOrd (greater _ _) = gt

  cmp : ℕ → ℕ → Ord
  cmp m n = toOrd (compare m n)

  F = λ (xs : _) → 0 ∷ ♯ merge cmp (map (_*_ 2) xs) (map (_*_ 3) xs)

  postulate
    lemma : ∀ n → cmp (2 * suc n) (3 * suc n) ≡ lt

  isCon : ∀ (xs ys : Stream ℕ) n →
          (∀ {m} → m <′ n → Eq m xs ys) →
          Eq n (F xs) (F ys)
  isCon _        _         zero    _   = refl
  isCon (x ∷ xs) (y  ∷ ys) (suc n) hyp with cong Vec.head (hyp (s≤′s z≤′n))
  isCon (0 ∷ xs) (.0 ∷ ys) (suc n) hyp | refl =
    cong (λ zs → 0 ∷ 0 ∷ zs) (begin
      take n (merge cmp (map (_*_ 2) (♭ xs)) (map (_*_ 3) (♭ xs)))  ≡⟨ iCantBeBothered ⟩
      take n (merge cmp (map (_*_ 2) (♭ ys)) (map (_*_ 3) (♭ ys)))  ∎)
    where postulate iCantBeBothered : _
  isCon (suc x ∷ xs) (.(suc x) ∷ ys) (suc n) hyp | refl
    with cmp (2 * suc x) (3 * suc x) | lemma x
  isCon (suc x ∷ xs) (.(suc x) ∷ ys) (suc n) hyp | refl | .lt | refl =
    cong (λ zs → 0 ∷ 2 * suc x ∷ zs) (begin
      take n (merge cmp (map (_*_ 2) (♭ xs))
                        (map (_*_ 3) (suc x ∷ xs)))  ≡⟨ iCantBeBothered ⟩
      take n (merge cmp (map (_*_ 2) (♭ ys))
                        (map (_*_ 3) (suc x ∷ ys)))  ∎)
    where postulate iCantBeBothered : _

hamming : Stream ℕ
hamming = ContractiveFun.fixpoint hammingF
