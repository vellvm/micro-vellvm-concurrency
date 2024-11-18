From Coq Require Import
     NArith.

From ExtLib Require Import
     Structures.Monads
.

From ITree Require Import
     Basics.CategoryOps
     Core.Subevent
.
Unset Universe Checking.
From CTree Require Import
     CTree
     Interp.Fold
     Interp.FoldStateT.

From Mem Require Import Utils Events.

Import MonadNotation.


Definition handle_sched_round_robin {E C} :
  SchedC ~> Monads.stateT nat (ctree E C) :=
  fun _ e s =>
  match e with
  | Sched l => let next := if Nat.eqb s (fold_left max l O) then O else S s in
    ret (next, s)
  end.

Definition handle_sched_random {E C} :
  SchedC ~> Monads.stateT N (ctree E C) :=
  fun _ e seed =>
  match e with
  | Sched l =>
    let '(seed, rd) := rand seed (N.of_nat (length l)) in
    let next := nth (N.to_nat rd) l O in
    ret (seed, next)
  end.

Section InterpSched.

  Context {E C : Type -> Type}.
  Context {S : Type}.
  Variable handler : SchedC ~> Monads.stateT S (ctree E C).

  Definition C_branch : C ~> Monads.stateT S (ctree E C) :=
    fun _ c m => r <- branch c ;; ret (m, r).

  Definition interp_sched_h :
    SchedC +' C ~>
    Monads.stateT S (ctree E C) :=
    case_ handler C_branch.

  Definition interp_sched :
    ctree E (SchedC +' C) ~> Monads.stateT S (ctree E C) :=
    refine interp_sched_h.

End InterpSched.
