------------------------------------------------------------------------
-- Formalisation of subtyping for recursive types
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- This formalisation is explained in "Subtyping, Declaratively—An
-- Exercise in Mixed Induction and Coinduction" (coauthored with
-- Thorsten Altenkirch). The code is partly based on "Coinductive
-- Axiomatization of Recursive Type Equality and Subtyping" by Michael
-- Brandt and Fritz Henglein.

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

import RecursiveTypes.Subtyping.Semantic.Coinductive

-- An example.

import RecursiveTypes.Subtyping.Example

-- Another definition of subtyping, this time in terms of finite
-- approximations. According to Brandt and Henglein this definition is
-- due to Amadio and Cardelli.

import RecursiveTypes.Subtyping.Semantic.Inductive

-- The two semantical definitions of subtyping above can easily be
-- proved equivalent.

import RecursiveTypes.Subtyping.Semantic.Equivalence

-- An axiomatisation of subtyping which is inspired by Brandt and
-- Henglein's. The main difference is that their axiomatisation is
-- inductive, using explicit hypotheses to get a coinductive flavour,
-- whereas mine is mixed inductive/coinductive, using no explicit
-- hypotheses. The axiomatisation is proved equivalent to the
-- coinductive semantic definition of subtyping. The proof is a lot
-- simpler than Brandt and Henglein's, but their proof includes a
-- decision procedure for subtyping.

import RecursiveTypes.Subtyping.Axiomatic.Coinductive

-- Brandt and Henglein's axiomatisation, plus some proofs:
-- • A proof showing that the axiomatisation is sound with respect to
--   the ones above. The soundness proof is different from the one
--   given by Brandt and Henglein: it is cyclic (but productive).
-- • Proofs of decidability and completeness, based on Brandt and
--   Henglein's algorithm.

import RecursiveTypes.Subtyping.Axiomatic.Inductive

-- Some modules containing supporting code for the proof of
-- decidability, including Brandt and Henglein's subterm relation.

import RecursiveTypes.Subterm
import RecursiveTypes.Subterm.RestrictedHypothesis
import RecursiveTypes.Syntax.UnfoldedOrFixpoint

-- An incorrect "subtyping" relation which illustrates the fact that
-- taking the transitive closure of a coinductively defined relation
-- is not in general equivalent to adding an inductive transitivity
-- constructor to it.

import RecursiveTypes.Subtyping.Axiomatic.Incorrect

-- Finally some code which is not directly related to subtyping or
-- recursive types: an example which shows that, in a coinductive
-- setting, it is not always sound to postulate admissible rules
-- (inductively).

import AdmissibleButNotPostulable
