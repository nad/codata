------------------------------------------------------------------------
-- Formalisation of subtyping for recursive types
------------------------------------------------------------------------

-- Partly based on "Coinductive Axiomatization of Recursive Type
-- Equality and Subtyping" by Michael Brandt and Fritz Henglein.

module RecursiveTypes where

-- Recursive types and potentially infinite trees.

import RecursiveTypes.Syntax

-- Substitutions.

import RecursiveTypes.Substitution

-- The semantics of recursive types, defined in terms of the trees
-- that you get when unfolding them.

import RecursiveTypes.Semantics

-- The definition of subtyping which, in my eyes, is the most obvious.
-- Some people may dislike coinductive definitions, though.

import RecursiveTypes.Subtyping.Coinductive

-- Another definition of subtyping, this time in terms of finite
-- approximations. According to Brandt and Henglein this definition is
-- due to Amadio and Cardelli.

import RecursiveTypes.Subtyping.Inductive

-- The two semantical definitions of subtyping above can easily be
-- proved equivalent.

import RecursiveTypes.Subtyping.Equivalence

-- An axiomatisation of subtyping which is inspired by Brandt and
-- Henglein's. The main difference is that their axiomatisation is
-- inductive, using explicit hypotheses to get a coinductive flavour,
-- whereas mine is mixed inductive/coinductive, using no explicit
-- hypotheses. The axiomatisation is proved equivalent to the
-- coinductive semantic definition of subtyping. The proof is a lot
-- simpler than Brandt and Henglein's, but their proof includes a
-- decision procedure for subtyping.

import RecursiveTypes.Subtyping.Axiomatisation
