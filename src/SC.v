From Coq Require Import
     Lists.List
     ZArith
     Strings.String.

From ExtLib Require Import
     Data.String
     Structures.Monads
.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.Subevent
     Events.MapDefault
     Events.State
     Indexed.Sum
.
Unset Universe Checking.
From CTree Require Import
     CTree
     Interp.Fold
     Interp.FoldStateT.

From Mem Require Import Utils Events Sched Pick.

Import ListNotations.
Import CTreeNotations.

Open Scope ctree_scope.
Open Scope monad_scope.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Section SCMemory.

Definition memory := NatMap.t value.
Definition SCMem := memory.

Definition empty_mem : SCMem := NatMap.empty.

Definition mem_read sc addr : option value := NatMap.find addr sc.

Definition mem_write sc addr v : SCMem :=
  NatMap.add addr v sc.

Lemma mem_read_write_eq : forall sc addr v,
  mem_read (mem_write sc addr v) addr = Some v.
Proof.
  intros. unfold mem_read, mem_write.
  now apply NatMapFacts.add_eq_o.
Qed.

Lemma mem_read_write_neq : forall sc addr addr' v,
  addr <> addr' ->
  mem_read (mem_write sc addr v) addr' = mem_read sc addr'.
Proof.
  intros. unfold mem_read, mem_write.
  now apply NatMapFacts.add_neq_o.
Qed.

(* no need to take into account memory ordering in SC *)
Definition handle_mem {E C} `{PickC -< C} :
  ThreadAnnotE MemoryE ~> Monads.stateT SCMem (ctree E C) :=
  fun _ e s =>
    let m := s in
    match e with
    | ThreadAnnot _ e =>
      match e with
      | Read _ a =>
        v <- freeze (mem_read s a);;
        Step (Ret (s, v))
      | Write _ a v => Step (Ret (mem_write s a v, tt))
      | ReadWrite _ a f =>
        oldv <- freeze (mem_read s a);;
        Step (Ret (mem_write s a (f oldv), oldv))
      | Fence _ => Step (Ret (s, tt))
      end
    end.

End SCMemory.

Section InterpSC.
  Context {E C : Type -> Type}.

  Definition E_trigger : E ~> Monads.stateT SCMem (ctree E (PickC +' C)) :=
   fun _ e m => r <- trigger e ;; ret (m, r).

  Definition interp_mem_h : ThreadAnnotE MemoryE +' E ~>
    Monads.stateT SCMem (ctree E (PickC +' C)) :=
    case_ handle_mem E_trigger.

  Definition interp_mem : ctree (ThreadAnnotE MemoryE +' E) C ~>
    Monads.stateT SCMem (ctree E (PickC +' C)) :=
    interp interp_mem_h.
End InterpSC.
