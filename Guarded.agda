------------------------------------------------------------------------
-- An encoding of guarded definitions
------------------------------------------------------------------------

-- This idea comes from Hancock and Setzer (Interactive Programs in
-- Dependent Type Theory). Conor McBride pointed me to their approach,
-- and this formulation of it.

-- Note that this approach needs to be modified to handle coinductive
-- families; it also needs to be modified to handle things like map
-- and zip (as part of guarded right-hand sides). These problems are
-- explored in the "Interrupts" repository, where I encountered and
-- partially solved these problems. Furthermore using this approach to
-- define libraries of combinators which can be used in guarded
-- right-hand sides appears to be tricky (see Guarded.Language, which
-- does not solve the problem). For these reasons I have now, possibly
-- temporarily, abandoned this approach to handling productive
-- definitions.

module Guarded where

data Guardedness : Set where
  guarded   : Guardedness
  unguarded : Guardedness

record Productive : Set1 where
  field
    -- The type of values to be produced.
    T : Set

    -- The type of value producers ("right-hand sides"), parameterised
    -- on a given seed type. A Producer may only be used in a context
    -- of matching Guardedness.
    Producer : Set ->          -- Seed type.
               Guardedness ->  -- Guardedness context.
               Set

    -- Returns a value immediately. Can be used in any context.
    return : forall {s g} -> T -> Producer s g

    -- This stands for a corecursive occurrence of the thing being
    -- defined, possibly with a new seed. Note that rec has to be used
    -- in a guarded context.
    rec : forall {s} -> s -> Producer s guarded

    -- This makes it possible to use a definition which has to be
    -- guarded in an unguarded context.
    unguard : forall {s} ->
              (s -> Producer s unguarded) ->
              (Producer s guarded -> Producer s unguarded)

    -- Given a Producer and a step function, produce a value.
    produce : forall {s} ->
              (s -> Producer s unguarded) ->
              (Producer s unguarded -> T)

    -- Map over the seed type.
    smap : forall {s₁ s₂ g} -> (s₁ -> s₂) -> Producer s₁ g -> Producer s₂ g

  -- Given a step function and a seed, produce a value.

  unfold : forall {s} -> (s -> Producer s unguarded) -> (s -> T)
  unfold step s = produce step (step s)

-- Note that unguard and smap can probably be removed from this record.
