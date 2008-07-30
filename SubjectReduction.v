(* This exploit is due to Nicolas Oury. *)

CoInductive Stream : Set :=
  | cons : Stream -> Stream.

Definition out (xs : Stream) : Stream :=
  match xs with
  | cons ys => cons ys
  end.

Require Import Logic.

Lemma out_eq (xs : Stream) : xs = out xs .
  intros xs.
  case_eq xs.
  intros s eq.
  reflexivity.
Defined.

CoFixpoint ones : Stream := cons ones.

Definition p : ones = cons ones := out_eq ones.

Eval compute in p.

(* p evaluates to refl_equal (cons (cofix ones  : Stream := cons ones)),
   but the following definition does not type check, so Coq lacks
   subject reduction. *)

Definition p2 : ones = cons ones :=
 refl_equal (cons (cofix ones : Stream := cons ones)).
