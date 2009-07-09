------------------------------------------------------------------------
-- Various developments related to codata and coinduction
--
-- Nils Anders Danielsson
------------------------------------------------------------------------

-- In order to type check/run the code here you need to use recent (at
-- the time of writing) versions of Agda and the Agda standard
-- libraries.

module README where

-- Streams. (Mostly reexported from Agda's "standard" library.)

import Stream

-- A simple example of my "ad-hoc and monolithic method for ensuring
-- that corecursive definitions are productive" (see
-- http://www.cs.nott.ac.uk/~nad/publications/danielsson-aim9-talk.html).

import StreamProg

-- A somewhat more elaborate/complicated example which can handle
-- functions like tail.

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

-- Breadth-first labelling of trees which /almost/ implements the
-- classic tie-the-recursive-knot algorithm due to Jeremy Gibbons and
-- Geraint Jones (see "Linear-time Breadth-first Tree Algorithms: An
-- Exercise in the Arithmetic of Folds and Zips", or Chris Okasaki's
-- explanation in "Breadth-First Numbering: Lessons from a Small
-- Exercise in Algorithm Design"). Proper sharing is not maintained,
-- though, so this implementation is far from being linear in the size
-- of the tree.

import Tree
import BreadthFirst.Universe
import BreadthFirst.Programs
import BreadthFirst

-- Formalisation of subtyping for recursive types, partly based on
-- "Coinductive Axiomatization of Recursive Type Equality and
-- Subtyping" by Michael Brandt and Fritz Henglein.

import RecursiveTypes

-- A definition of a big-step semantics which handles termination and
-- non-termination at the same time, without duplication of rules.
-- Partly based on Leroy and Grall's "Coinductive big-step operational
-- semantics" and Cousot and Cousot's "Bi-inductive structural
-- semantics".

import Lambda

-- An investigation of nested fixpoints of the form μX.νY.… in Agda.
-- It turns out that they cannot be represented directly.

import MuNu

-- An implementation of "A Unifying Approach to Recursive and
-- Co-recursive Definitions" by Pietro Di Gianantonio and Marino
-- Miculan.

import Contractive
import Contractive.Function
import Contractive.Stream
import Contractive.Examples

-- An abandoned encoding of guarded definitions.

import Guarded
import Guarded.Stream
import Guarded.Product
import Guarded.IndexedBy
import Guarded.Language
