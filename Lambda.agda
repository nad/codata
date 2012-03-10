------------------------------------------------------------------------
-- An investigation of various ways to define the semantics of an
-- untyped λ-calculus and a virtual machine, and a discussion of
-- compiler correctness
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

module Lambda where

-- Syntax of an untyped λ-calculus.

import Lambda.Syntax

------------------------------------------------------------------------
-- Semantics based on substitutions

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

import Lambda.Substitution.OneSemantics

-- Two separate semantics for the language, one for converging terms
-- and the other for diverging terms, as given by Leroy and Grall in
-- "Coinductive big-step operational semantics".
--
-- Leroy and Grall attempted to unify their two semantics into a
-- single one, using only coinduction, but failed to find a definition
-- which was equivalent to the two that they started with. However,
-- they aimed for a definition which did not have more rules than the
-- definition for converging terms; the definition in OneSemantics
-- does not satisfy this criterion.

import Lambda.Substitution.TwoSemantics

-- The two definitions are equivalent.

import Lambda.Substitution.Equivalence

------------------------------------------------------------------------
-- Virtual machine

-- A virtual machine with two semantics (one relational and one
-- functional), a compiler from the λ-calculus defined above into the
-- language of the virtual machine, and a proof showing that the two
-- semantics are equivalent.

import Lambda.VirtualMachine

------------------------------------------------------------------------
-- Semantics based on closures

-- A semantics for the untyped λ-calculus, based on closures and
-- environments, as given by Leroy and Grall in "Coinductive big-step
-- operational semantics" (more or less).
--
-- The module also contains a proof which shows that the compiler in
-- Lambda.VirtualMachine preserves the semantics (assuming that the
-- virtual machine is deterministic). Leroy and Grall prove almost the
-- same thing. In their proof they use a relation indexed by a natural
-- number to work around limitations in Coq's productivity checker.
-- Agda has similar limitations, but I work around them using mixed
-- induction/coinduction, which in my opinion is more elegant. I am
-- not sure if my workaround would work in Coq, though.

import Lambda.Closure.Relational

-- A semantics for the untyped λ-calculus which uses the partiality
-- monad, along with another compiler correctness proof. An advantage
-- of formulating the semantics in this way is that it is very easy to
-- state compiler correctness.

import Lambda.Closure.Functional

-- The module above uses some workarounds in order to convince Agda
-- that the code is productive. The following module contains (more or
-- less) the same code without the workarounds, but is checked with
-- the termination checker turned off.

import Lambda.Closure.Functional.No-workarounds

-- The relational and functional semantics are equivalent.

import Lambda.Closure.Equivalence

-- An alternative definition of the functional semantics. This
-- definition uses continuation-passing style instead of bind.

import Lambda.Closure.Functional.Alternative

-- A definition of a type system (with recursive types) for the
-- λ-calculus given above, and a proof of type soundness for the
-- functional semantics.

import Lambda.Closure.Functional.Type-soundness

-- A very brief treatment of different kinds of term equivalences,
-- including contextual equivalence and applicative bisimilarity.

import Lambda.Closure.Equivalences

-- A functional semantics, a compiler and a compiler correctness proof
-- for a non-deterministic untyped λ-calculus with constants.

import Lambda.Closure.Functional.Non-deterministic

-- A variant of the code above without the workarounds used to
-- convince Agda that the code is productive.

import Lambda.Closure.Functional.Non-deterministic.No-workarounds
