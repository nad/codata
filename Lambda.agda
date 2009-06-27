------------------------------------------------------------------------
-- A definition of a big-step semantics which handles termination and
-- non-termination at the same time, without duplication of rules
------------------------------------------------------------------------

module Lambda where

-- Syntax of an untyped λ-calculus.

import Lambda.Syntax

-- Substitutions.

import Lambda.Substitution

-- A big-step semantics for the language. Conditional coinduction is
-- used to avoid duplication of rules.
--
-- Cousot and Cousot give a similar definition in "Bi-inductive
-- structural semantics", and their definition inspired this one.
-- Their definition has almost the same rules, but these rules are
-- interpreted in the framework of bi-induction rather than the
-- framework of mixed induction and (conditional) coinduction.

import Lambda.OneSemantics

-- Two separate semantics for the language, one for converging terms
-- and the other for diverging terms, as given by Leroy and Grall in
-- "Coinductive big-step operational semantics".
--
-- Leroy and Grall attempted to unify their two semantics into a
-- single one, using only coinduction, but failed to find a definition
-- which was equivalent to the two that they started with.

import Lambda.TwoSemantics

-- The two definitions are equivalent.

import Lambda.Equivalence
