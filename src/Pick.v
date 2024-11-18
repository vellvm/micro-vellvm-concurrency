From Coq Require Import
     NArith
     ZArith
     String.

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


Definition freeze {E C} `{PickC -< C} v : ctree E C value :=
  match v with
  | Some v => Ret v
  | None => branch Pick
  end.

Definition force_def {E C T} `{PickC -< C} `{ExceptC T -< C} v (msg: string) (err: T) : ctree E C value :=
  match v with
  | Some v => Ret v
  | None => cthrow err msg
  end.

Definition handle_pick_random {E C} :
  PickC ~> Monads.stateT N (ctree E C) :=
  fun _ e seed =>
  match e with
  | Pick =>
    let '(seed, rd) := rand seed (N.of_nat 2000) in
    ret (seed, (Z.of_N rd - 1000)%Z)
  end.

Section InterpPick.

  Context {E C : Type -> Type}.
  Context {S : Type}.
  Variable handler : PickC ~> Monads.stateT S (ctree E C).

  Definition C_branch : C ~> Monads.stateT S (ctree E C) :=
    fun _ c m => r <- branch c ;; ret (m, r).

  Definition interp_pick_h :
    PickC +' C ~>
    Monads.stateT S (ctree E C) :=
    case_ handler C_branch.

  Definition interp_pick :
    ctree E (PickC +' C) ~> Monads.stateT S (ctree E C) :=
    refine interp_pick_h.

End InterpPick.
