From Coq Require Import
     Init
     List
     String
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
     Eq
     Fold
     FoldStateT
.

From Mem Require Import Utils Events.

Import ListNotations.
Import MonadNotation.

Open Scope bool_scope.

Section Vars.

Context (globals : StringMap.t value).

Definition var_state := StringMap.t value.

Definition read_local (vs : var_state) reg :=
  StringMap.find_or reg nullval vs.

Definition write_local (vs : var_state) reg val :=
  StringMap.add reg val vs.

Definition read_global reg :=
  StringMap.find_or reg nullval globals.

Definition handle_var {E C} :
  VarE ~> Monads.stateT var_state (ctree E C) :=
  fun _ e vs =>
    match e with
    | NewFrame =>
      Ret (StringMap.empty, tt)
    | LocalWrite reg value =>
      Ret (write_local vs reg value, tt)
    | LocalRead v =>
      Ret (vs, read_local vs v)
    | GlobalRead v =>
      Ret (vs, read_global v)
    end.

Section InterpVar.

  Context {E C : Type -> Type}.

  Definition E_trigger : E ~> Monads.stateT var_state (ctree E C) :=
    fun _ e s => x <- trigger e;; Ret (s, x).

  Definition interp_var_h :
    VarE +' E ~>
    Monads.stateT var_state (ctree E C) :=
    fun _ e s =>
      match e with
      | inl1 e => handle_var _ e s
      | inr1 e => E_trigger _ e s
      end.

  Definition interp_var :
      ctree (VarE +' E) C ~> Monads.stateT var_state (ctree E C) :=
    interp_state interp_var_h.

End InterpVar.

End Vars.
