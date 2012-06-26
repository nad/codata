------------------------------------------------------------------------
-- Code related to the paper
-- "Operational Semantics Using the Partiality Monad"
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- Several definitions and proofs in this code are closely related to
-- definitions and proofs in the paper "Coinductive big-step
-- operational semantics" by Leroy and Grall. See my paper for more
-- detailed references to related work, and also for more explanations
-- of how the code works.

module Operational-semantics-using-the-partiality-monad where

------------------------------------------------------------------------
-- Section 2

-- Fin.

import Data.Fin

-- Vec, lookup.

import Data.Vec

-- The partiality monad.

import Category.Monad.Partiality

-- A variant of trivial, as well as proofs showing that the definition
-- of weak bisimilarity in the paper coincides with Capretta's
-- definition and a more standard definition based on weak
-- bisimulations.

import AdmissibleButNotPostulable

------------------------------------------------------------------------
-- Section 3

-- Tm, Env, Value.

import Lambda.Syntax

-- Big-step functional semantics, Ω.

import Lambda.Closure.Functional

-- The module above uses some workarounds in order to convince Agda
-- that the code is productive. The following module contains (more or
-- less) the same code without the workarounds, but is checked with
-- the termination checker turned off.

import Lambda.Closure.Functional.No-workarounds

-- An alternative definition of the functional semantics. This
-- definition uses continuation-passing style instead of bind.

import Lambda.Closure.Functional.Alternative

------------------------------------------------------------------------
-- Section 4

-- Type system, type soundness.

import Lambda.Closure.Functional.Type-soundness

-- Any for Maybe.

import Data.Maybe

-- All for the partiality monad.

import Category.Monad.Partiality.All

------------------------------------------------------------------------
-- Section 5

-- The relational semantics.

import Lambda.Closure.Relational

-- Proofs of equivalence.

import Lambda.Closure.Equivalence

------------------------------------------------------------------------
-- Section 6

-- The virtual machine. Two semantics are given, one relational and
-- one functional, and they are proved to be equivalent.

import Lambda.VirtualMachine

------------------------------------------------------------------------
-- Section 7

-- The compiler.

import Lambda.VirtualMachine

-- Compiler correctness for the functional semantics.

import Lambda.Closure.Functional
import Lambda.Closure.Functional.No-workarounds

-- Compiler correctness for the relational semantics.

import Lambda.Closure.Relational

------------------------------------------------------------------------
-- Section 8

-- The non-deterministic language along with a compiler and a compiler
-- correctness proof, as well as a type soundness proof.

import Lambda.Closure.Functional.Non-deterministic
import Lambda.Closure.Functional.Non-deterministic.No-workarounds

------------------------------------------------------------------------
-- Section 9

-- A very brief treatment of different kinds of term equivalences,
-- including contextual equivalence and applicative bisimilarity.

import Lambda.Closure.Equivalences

-- _⇓.

import Category.Monad.Partiality
