------------------------------------------------------------------------
-- The partiality monad
------------------------------------------------------------------------

-- The partiality monad.

sized codata Lift (+ A : Set) : -Size -> Set
{ now   : [i : Size] -> A        -> Lift A ($ i)
; later : [i : Size] -> Lift A i -> Lift A ($ i)
}

-- A non-terminating computation.

cofun never : (A : Set) -> [i : Size] -> |i| -> Lift A i
{ never A ($ i) = later i (never A i)
}

-- The monad's bind operation.

cofun bind : (A, B : Set) -> [i : Size] ->
             Lift A i -> (A -> Lift B i) -> Lift B i
{ bind A B ($ i) (now   .i a) f = f a
; bind A B ($ i) (later .i x) f = later i (bind A B i x f)
}

-- Weak bisimilarity and the greater-than-or-equal-to relation are
-- defined as a single type family, parametrised by the notion of
-- equivalence.

data Kind : Set
{ ge : Kind  -- Weak bisimilarity.
; eq : Kind  -- Greater than or equal to.
}

-- The inductive part of the relations.

data Rel' (A : Set) (+ Rel : Lift A # -> Lift A # -> Set) :
          Kind -> Lift A # -> Lift A # -> Set
{ nowCong'   : (k : Kind) -> (v : A) ->
               Rel' A Rel k (now # v) (now # v)
; laterCong' : (k : Kind) -> (x1, x2 : Lift A #) ->
               Rel x1 x2 ->
               Rel' A Rel k (later # x1) (later # x2)
; laterL'    : (k : Kind) -> (x1, x2 : Lift A #) ->
               Rel' A Rel k x1 x2 ->
               Rel' A Rel k (later # x1) x2
; laterR'    : (x1, x2 : Lift A #) ->
               Rel' A Rel eq x1 x2 ->
               Rel' A Rel eq x1 (later # x2)
}

-- The relations. (The constructor tie "ties the coinductive knot".)

sized codata Rel (A : Set) (k : Kind) (x1, x2 : Lift A #) : Size -> Set
{ tie : [i : Size] -> Rel' A (\x1 x2 -> Rel A k x1 x2 i) k x1 x2 ->
        Rel A k x1 x2 ($ i)
}

pattern nowCong i k v            = tie i (nowCong' k v)
pattern laterCong i k x1 x2 xRel = tie i (laterCong' k x1 x2 xRel)
pattern laterL'' i k x1 x2 xRel  = tie i (laterL' k x1 x2 xRel)
pattern laterR'' i x1 x2 xEq     = tie i (laterR' x1 x2 xEq)

-- Weak bisimilarity.

let Eq ^(A : Set) -(i : Size) : Lift A # -> Lift A # -> Set =
  \x1 x2 -> Rel A eq x1 x2 i

-- Greater than or equal to.

let GEq ^(A : Set) -(i : Size) : Lift A # -> Lift A # -> Set =
  \x1 x2 -> Rel A ge x1 x2 i

-- Less than or equal to.

let LEq ^(A : Set) -(i : Size) : Lift A # -> Lift A # -> Set =
  \x1 x2 -> Rel A ge x2 x1 i

-- The constructors of Rel' can be "lifted" to the level of Rel. (For
-- nowCong and laterCong the pattern synonyms suffice.)

cofun laterL : (A : Set) -> (i : Size) -> (k : Kind) ->
               [x1, x2 : Lift A #] ->
               Rel A k x1 x2 i -> Rel A k (later # x1) x2 i
{ laterL A ($ i) k x1 x2 (tie .i xRel) = laterL'' i k x1 x2 xRel
}

cofun laterR : (A : Set) -> (i : Size) -> [x1, x2 : Lift A #] ->
               Eq A i x1 x2 -> Eq A i x1 (later # x2)
{ laterR A ($ i) x1 x2 (tie .i xEq) = laterR'' i x1 x2 xEq
}

-- The relations are reflexive.

cofun reflRel : [i : Size] -> (k : Kind) -> [A : Set] ->
                (x : Lift A #) -> Rel A k x x i
{ reflRel    i  k A (now   .# v) = nowCong i k v
; reflRel ($ i) k A (later .# x) = laterCong i k x x (reflRel i k A x)
}

-- Weak bisimilarity is symmetric.

mutual {

  cofun symEq' : [i : Size] -> [A : Set] ->
                 [x1, x2 : Lift A #] ->
                 Rel' A (Eq A i) eq x1 x2 ->
                 Eq A ($ i) x2 x1
  { symEq' i A .(now # v) .(now # v) (nowCong' .eq v) =
      nowCong i eq v
  ; symEq' i A .(later # x1) .(later # x2)
      (laterCong' .eq x1 x2 xEq) =
      laterCong i eq x2 x1 (symEq i A x1 x2 xEq)
  ; symEq' i A .(later # x1) .x2 (laterL' .eq x1 x2 xEq) =
      laterR A ($ i) x2 x1 (symEq' i A x1 x2 xEq)
  ; symEq' i A .x1 .(later # x2) (laterR' x1 x2 xEq) =
      laterL A ($ i) eq x2 x1 (symEq' i A x1 x2 xEq)
  }

  cofun symEq : [i : Size] -> [A : Set] ->
                [x1, x2 : Lift A #] ->
                Eq A i x1 x2 -> Eq A i x2 x1
  { symEq ($ i) A x1 x2 (tie .i xEq) = symEq' i A x1 x2 xEq
  }

}

-- The following transitivity-like properties can be proved for the
-- relations above.

mutual {

  cofun transLRel' :
    (i : Size) -> (A : Set) -> (k : Kind) ->
    [x1, x2, x3 : Lift A #] ->
    Rel' A (GEq A #)                   ge x1 x2 ->
    Rel' A (\x1 x2 -> Rel A k x1 x2 i) k  x2 x3 ->
    Rel  A                             k  x1 x3 ($ i)
  { transLRel' i A k .(now # v) .(now # v) x3 (nowCong' .ge v) rel23 =
      tie i rel23
  ; transLRel' i A k .(later # x1) .x2 x3
      (laterL' .ge x1 x2 geq12) rel23 =
      laterL A ($ i) k x1 x3 (transLRel' i A k x1 x2 x3 geq12 rel23)
  ; transLRel' i A .eq x1 .x2 .(later # x3)
      geq12 (laterR' x2 x3 eq23) =
      laterR A ($ i) x1 x3 (transLRel' i A eq x1 x2 x3 geq12 eq23)
  ; transLRel' i A k .(later # x1) .(later # x2) .(later # x3)
      (laterCong' .ge x1 x2 geq12) (laterCong' .k .x2 x3 rel23) =
      laterCong i k x1 x3 (transLRel i A k x1 x2 x3 geq12 rel23)
  ; transLRel' i A k .(later # x1) .(later # x2) .x3
      (laterCong' .ge x1 x2 (tie .# geq12)) (laterL' .k .x2 x3 rel23) =
      laterL A ($ i) k x1 x3 (transLRel' i A k x1 x2 x3 geq12 rel23)
  }

  cofun transLRel :
    (i : Size) -> (A : Set) -> (k : Kind) ->
    [x1, x2, x3 : Lift A #] ->
    GEq A # x1 x2 -> Rel A k x2 x3 i -> Rel A k x1 x3 i
  { transLRel ($ i) A k x1 x2 x3 (tie .# geq12) (tie .i rel23) =
      transLRel' i A k x1 x2 x3 geq12 rel23
  }

}

let transREq (i : Size) (A : Set) [x1, x2, x3 : Lift A #]
             (eq12 : Eq A i x1 x2) (leq23 : LEq A # x2 x3) :
             Eq A i x1 x3 =
  symEq i A x3 x1
    (transLRel i A eq x3 x2 x1 leq23
       (symEq i A x1 x2 eq12))

let transRLEq (i : Size) (A : Set) [x1, x2, x3 : Lift A #]
              (leq12 : LEq A i x1 x2) (leq23 : LEq A # x2 x3) :
              LEq A i x1 x3 =
  transLRel i A ge x3 x2 x1 leq23 leq12
