From Coq Require Import
     Init
     String
     ZArith
.

From ExtLib Require Import
     Structures.Monads
.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.Subevent
     Indexed.Sum
.

Unset Universe Checking.
From CTree Require Import
     CTree
     Fold
     FoldStateT
.

From Mem Require Import Utils Events.

Import MonadNotation.

Open Scope bool_scope.

Definition handle_alloc_simple {E C} :
  AllocE ~> Monads.stateT nat (ctree E C) :=
  fun _ e s =>
    let 'Alloc size := e in Ret (s + size, s).

Section InterpAlloc.

  Context {E F C : Type -> Type}.
  Context `{E -< F}.

  Definition E_trigger : E ~> Monads.stateT nat (ctree F C) :=
    fun _ e => Monads.liftState (trigger e).

  (* FIXME universe inconsistency *)
  Definition interp_alloc_h :
    AllocE +' E ~>
    Monads.stateT nat (ctree F C) :=
  fun _ e s =>
    match e with
    | inl1 e => handle_alloc_simple _ e s
    | inr1 e => E_trigger _ e s
    end.
    (*case_ (handle_alloc_simple) E_trigger.*)

  Definition interp_alloc :
    ctree (AllocE +' E) C ~> Monads.stateT nat (ctree F C) :=
      interp interp_alloc_h.

End InterpAlloc.
