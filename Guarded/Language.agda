------------------------------------------------------------------------
-- A more interesting example: A universe for certain languages
------------------------------------------------------------------------

-- Note: This file is unfinished.

module Guarded.Language where

------------------------------------------------------------------------
-- The universe

open import Data.Char

infixl 5 _⊛_
infixl 4 _∣_

codata L : Set where
  ε    : L
  term : Char -> L
  _∣_  : L -> L -> L
  _⊛_  : L -> L -> L

open import Data.Nat

take : ℕ -> L -> L
take zero    _         = ε
take (suc n) ε         = ε
take (suc n) (term c)  = term c
take (suc n) (p₁ ∣ p₂) = take n p₁ ∣ take n p₂
take (suc n) (p₁ ⊛ p₂) = take n p₁ ⊛ take n p₂

------------------------------------------------------------------------
-- Grammar producers

open import Guarded

data LProd (s : Set) : Guardedness -> Set where
  return : forall {g} -> L -> LProd s g
  ε      : forall {g} -> LProd s g
  term   : forall {g} -> Char -> LProd s g
  _∣_    : forall {g} ->
           LProd s guarded -> LProd s guarded ->
           LProd s g
  _⊛_    : forall {g} ->
           LProd s guarded -> LProd s guarded ->
           LProd s g
  rec    : s -> LProd s guarded

smap : forall {s₁ s₂ g} -> (s₁ -> s₂) -> LProd s₁ g -> LProd s₂ g
smap f (return p) = return p
smap f (term c)   = term c
smap f ε          = ε
smap f (p₁ ∣ p₂)  = smap f p₁ ∣ smap f p₂
smap f (p₁ ⊛ p₂)  = smap f p₁ ⊛ smap f p₂
smap f (rec x)    = rec (f x)

private
 module Dummy {s : Set} (step : s -> LProd s unguarded) where

  unguard : LProd s guarded -> LProd s unguarded
  unguard (return p)  = return p
  unguard ε           = ε
  unguard (term c)    = term c
  unguard (p₁ ∣ p₂)   = p₁ ∣ p₂
  unguard (p₁ ⊛ p₂)   = p₁ ⊛ p₂
  unguard (rec x)     = step x

  produce : LProd s unguarded -> L
  produce (return xs) ~ xs
  produce ε           ~ ε
  produce (term c)    ~ term c
  produce (p₁ ∣ p₂)   ~ produce (unguard p₁) ∣ produce (unguard p₂)
  produce (p₁ ⊛ p₂)   ~ produce (unguard p₁) ⊛ produce (unguard p₂)

open Dummy public

LProductive : Productive
LProductive = record
  { T        = L
  ; Producer = LProd
  ; return   = return
  ; rec      = rec
  ; unguard  = unguard
  ; produce  = produce
  ; smap     = smap
  }

------------------------------------------------------------------------
-- A simple library

module SimpleLib (Seed : Set) where

  private
    G = LProd Seed

  addOp : forall {g} -> G g
  addOp = term '+' ∣ term '-'

  mulOp : forall {g} -> G g
  mulOp = term '*' ∣ term '/'

  digit : forall {g} -> G g
  digit = term '0'
        ∣ term '1'
        ∣ term '2'
        ∣ term '3'
        ∣ term '4'
        ∣ term '5'
        ∣ term '6'
        ∣ term '7'
        ∣ term '8'
        ∣ term '9'

  parenthesised : forall {g} -> G guarded -> G g
  parenthesised p = term '(' ⊛ p ⊛ term ')'

------------------------------------------------------------------------
-- A library which includes corecursive definitions

module Library (Seed : Set) (s : Seed) where

  open SimpleLib Seed public

  private
    G = LProd Seed

  -- This definition is incorrect, rec s does not refer to p +.

  _+ : forall {g} -> G guarded -> G g
  p + = p ⊛ (ε ∣ rec s)

  _⋆ : forall {g} -> G guarded -> G g
  p ⋆ = ε ∣ p +

  _sepBy_ : forall {g} -> G guarded -> G guarded -> G g
  p sepBy sep = p ⊛ (sep ⊛ p) ⋆

  number : forall {g} -> G g
  number = digit ⋆

------------------------------------------------------------------------
-- Examples

module Expr₁ where

  open import Data.Unit
  open import Data.Product
  open import Guarded.IndexedBy

  data Nonterminal : Set where
    expr   : Nonterminal
    term   : Nonterminal
    factor : Nonterminal

  module L = Productive (LProductive IndexedBy Nonterminal)

  grammar : forall {g} -> L.Producer ⊤ g
  grammar expr   = L.rec _ term sepBy addOp
    where open Library (⊤ × Nonterminal) (tt , term)
  grammar term   = L.rec _ factor sepBy mulOp
    where open Library (⊤ × Nonterminal) (tt , factor)
  grammar factor = number
                 ∣ parenthesised (L.rec _ expr)
    where open Library (⊤ × Nonterminal) (tt , factor)

  test = \n nt -> take n (L.unfold (\_ -> grammar) tt nt)

module Expr₂ where

  open Productive LProductive using (unfold)

  -- Alternative definition without corecursive library grammars:

  data Nonterminal : Set where
    _⋆      : LProd Nonterminal guarded -> Nonterminal
    number  : Nonterminal
    expr    : Nonterminal
    term    : Nonterminal
    factor  : Nonterminal

  open SimpleLib Nonterminal

  grammar : forall {g} -> Nonterminal -> LProd Nonterminal g
  grammar (p ⋆)  = ε ∣ p ⊛ rec (p ⋆)
  grammar number = digit ⊛ rec (digit ⋆)
  grammar expr   = rec term   ⊛ rec ((addOp ⊛ rec term)   ⋆)
  grammar term   = rec factor ⊛ rec ((mulOp ⊛ rec factor) ⋆)
  grammar factor = rec number
                 ∣ parenthesised (rec expr)

  test = \n nt -> take n (unfold grammar nt)

open import Data.Product

testBoth : ℕ -> L × L
testBoth n = (Expr₁.test n Expr₁.expr , Expr₂.test n Expr₂.expr)
