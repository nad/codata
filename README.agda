------------------------------------------------------------------------
-- Code related to the paper Mixing Induction and Coinduction
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- The code has been tested using Agda 2.2.4.

module README where

------------------------------------------------------------------------
-- Section 3: An ad-hoc method for making corecursive definitions
-- guarded

-- Streams. (Mostly reexported from Agda's standard library.)

import Stream

-- A definition of the stream of Fibonacci numbers, as well
-- as a definition of the Hamming numbers.

import StreamProg

-- A somewhat more elaborate/complicated variant of the method which
-- can handle functions like tail.

import IndexedStreamProg

-- A formalisation of parts of Ralf Hinze's paper "Streams and Unique
-- Fixed Points".

import Stream.Programs
import Stream.Equality
import Stream.Pointwise
import Hinze.Lemmas
import Hinze.Section2-4
import Hinze.Section3
import Hinze.Simplified.Section2-4
import Hinze.Simplified.Section3

-- Breadth-first labelling of trees, /almost/ implementing the classic
-- tie-the-recursive-knot algorithm due to Jeremy Gibbons and Geraint
-- Jones (see "Linear-time Breadth-first Tree Algorithms: An Exercise
-- in the Arithmetic of Folds and Zips", or Chris Okasaki's
-- explanation in "Breadth-First Numbering: Lessons from a Small
-- Exercise in Algorithm Design"). Proper sharing is not maintained,
-- though, so this implementation is far from being linear in the size
-- of the tree.

import Tree
import BreadthFirst.Universe
import BreadthFirst.Programs
import BreadthFirst

------------------------------------------------------------------------
-- Section 4: Subtyping for recursive types

-- Formalisation of subtyping for recursive types, partly based on
-- "Coinductive Axiomatization of Recursive Type Equality and
-- Subtyping" by Michael Brandt and Fritz Henglein.

import RecursiveTypes

-- One must exercise caution when using the technique advertised in
-- Section 4. The following module shows that, in a coinductive
-- setting, it is not always sound to postulate admissible rules
-- (inductively).

import AdmissibleButNotPostulable

------------------------------------------------------------------------
-- Section 5: Total parser combinators

-- Parser combinators which only handle recognition.

import TotalParserCombinators

-- Full parser combinators. Initially developed together with Ulf
-- Norell; I added the use of mixed induction and coinduction.

import StructurallyRecursiveDescentParsing.README

------------------------------------------------------------------------
-- Section 6: Big-step semantics for both converging and diverging
-- computations

-- A definition of a big-step semantics which handles termination and
-- non-termination at the same time, without duplication of rules.
-- Partly based on Leroy and Grall's "Coinductive big-step operational
-- semantics" and Cousot and Cousot's "Bi-inductive structural
-- semantics".

import Lambda

-- An example showing how the list and colist types can be "unified".

import DataAndCodata

------------------------------------------------------------------------
-- Section 7: Related work

-- An investigation of nested fixpoints of the form μX.νY.… in Agda.
-- It turns out that they cannot be represented directly.

import MuNu

-- An implementation of "A Unifying Approach to Recursive and
-- Co-recursive Definitions" by Pietro Di Gianantonio and Marino
-- Miculan. Contains one postulate.

import Contractive
import Contractive.Function
import Contractive.Stream
import Contractive.Examples
