------------------------------------------------------------------------
-- Instantiation of Contractive for streams
------------------------------------------------------------------------

-- Taken from the paper.

-- The definition of Eq has been changed slightly, as compared to the
-- paper. The paper uses
--   Eq = λ n xs ys → take n xs ≡ take n ys.
-- The reason for the change is that with the definition above
-- coherence does not say anything about the first element in limU s.
-- With the definition in the paper head (s 0), which is the first
-- element in limU s, does not have to be related to head (s n) for
-- any other n, and this makes it impossible to prove isLimitU.
-- (Unless I have missed something.)

module Contractive.Stream {A : Set} where

open import Coinduction
open import Contractive
open import Stream
open import Data.Nat
open import Data.Nat.Properties
import Data.Vec as Vec
open Vec using (_∷_; [])
open import Data.Function
open import Relation.Unary
open import Relation.Binary.PropositionalEquality
open import Induction.Nat

<′-isWellFoundedOrder : IsWellFoundedOrder _<′_
<′-isWellFoundedOrder = record
  { trans         = λ {i} {j} {k} i+1≤j j+1≤k → ≤⇒≤′ (begin
                       suc i  ≤⟨ ≤′⇒≤ (≤′-step i+1≤j) ⟩
                       suc j  ≤⟨ ≤′⇒≤ j+1≤k ⟩
                       k      ∎)
  ; isWellFounded = <-allAcc
  }
  where open ≤-Reasoning

ofe : OFE
ofe = record
  { carrier            = ℕ
  ; domain             = Stream A
  ; _<_                = _<′_
  ; isWellFoundedOrder = <′-isWellFoundedOrder
  ; Eq                 = λ n xs ys → take (suc n) xs ≡ take (suc n) ys
  ; isEquivalence      = λ _ → record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }

open OFE ofe

private

  limU : (ℕ → Stream A) → Stream A
  limU s = head (s 0) ≺ ♯ limU (tail ∘ s ∘ suc)

  η : ∀ {n} {xs : Stream A} → Eq n xs (head xs ≺ ♯ tail xs)
  η {xs = x ≺ xs} = refl

  step : ∀ s →
         IsCoherent {U} (lift s) →
         IsCoherent {U} (lift (tail ∘ s ∘ suc))
  step s coh {m} {n} _ _ m<n = begin
    take (suc m) (tail (s (suc m)))      ≡⟨ lem (s (suc m)) ⟩
    Vec.tail (take (2 + m) (s (1 + m)))  ≡⟨ cong Vec.tail $ coh {1 + m} {1 + n} _ _ (s≤′s m<n) ⟩
    Vec.tail (take (2 + m) (s (1 + n)))  ≡⟨ sym $ lem (s (suc n)) ⟩
    take (suc m) (tail (s (suc n)))      ∎
    where
    open ≡-Reasoning

    lem : ∀ {n} (xs : Stream A) →
          take n (tail xs) ≡ Vec.tail (take (1 + n) xs)
    lem (x ≺ xs) = refl

  isLimitU : ∀ s →
             IsCoherent {U} (lift s) →
             IsLimit {U} (lift s) (limU s)
  isLimitU s coh {zero}  _ = begin
    take 1 (s 0)     ≡⟨ η ⟩
    head (s 0) ∷ []  ∎
    where open ≡-Reasoning
  isLimitU s coh {suc n} _ = begin
    take (2 + n) (s (1 + n))                                 ≡⟨ η ⟩
    head (s (1 + n)) ∷ take (1 + n) ((tail ∘ s ∘ suc) n)     ≡⟨ cong₂ _∷_ lem₁ (isLimitU (tail ∘ s ∘ suc)
                                                                                         (step s coh) {n} _) ⟩
    head (s 0)       ∷ take (1 + n) (limU (tail ∘ s ∘ suc))  ∎
    where
    open ≡-Reasoning

    lem₂ : ∀ {n} (xs ys : Stream A) →
           Eq n xs ys → head xs ≡ head ys
    lem₂ (x ≺ xs) (y ≺ ys) = cong Vec.head

    lem₁ : head (s (1 + n)) ≡ head (s 0)
    lem₁ = lem₂ _ _ $ sym $ coh {0} {suc n} _ _ (s≤′s z≤′n)

  lim↓ : A → ∀ n → (∀ n' → n' <′ n → Stream A) → Stream A
  lim↓ x zero    s = repeat x
  lim↓ x (suc n) s = s n ≤′-refl

  isLimit↓ : ∀ x n (s : Family (↓ n)) →
             IsCoherent s → IsLimit s (lim↓ x n s)
  isLimit↓ x zero    s coh ()
  isLimit↓ x (suc n) s coh ≤′-refl       = refl
  isLimit↓ x (suc n) s coh (≤′-step m<n) =
    coh (≤′-step m<n) ≤′-refl m<n

-- The paper implicitly assumes that A is non-empty.

cofe : A → COFE
cofe x = record
  { ofe      = ofe
  ; limU     = limU
  ; isLimitU = isLimitU _
  ; lim↓     = lim↓ x
  ; isLimit↓ = λ n {s} → isLimit↓ x n s
  }
