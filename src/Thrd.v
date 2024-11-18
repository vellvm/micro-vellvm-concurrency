From Coq Require Import List String ZArith.
From ITree Require Import Core.Subevent.
Unset Universe Checking.
From Mem Require Import Events lang.

Import ListNotations.

Open Scope Z_scope.

(* thrd_create and thrd_join from C11 *)

Section Thrd.

  Context {E B : Type -> Type} {X : Type}
    {HasAlloc : AllocE -< E}
    {HasMemory : MemoryE -< E}
    {HasThread : @ThreadE addr -< E}.

(* thrd_create allocates three memory cells that contain (in order):
  - the status of the thread (0 = not started, 1 = started, 2 = finished, 3 = joined)
  - the return value of the thread
  - the thread argument
*)

  Definition thrd_create f (arg : exp) (tdatareg : string) := [
    (* allocate the thread data structure *)
    (tdatareg, Alloca (OP_Atom 3));
    (* store the thread argument *)
    ("__thrd_create_1", AtomicRMW acq_rel ATOMIC_xchg arg (OP_IBinop Add (EXP_Ident tdatareg) 2));
    (* init thread status to 0 *)
    ("__thrd_create_2", AtomicRMW acq_rel ATOMIC_xchg (OP_Atom 0) (OP_Atom (EXP_Ident tdatareg)));
    (* spawn the thread *)
    ("__thrd_create_3", ThreadCreate f "__thrd_init" "__thrd_cleanup" (OP_Atom (EXP_Ident tdatareg)))
  ].

  Definition thrd_init : definition :=
    ("__thrd_init",
      mkCFG "0" [mk_block "0" [
        (* synchronize with the parent thread *)
        ("0", AtomicRMW acq_rel ATOMIC_xchg (OP_Atom 1%Z) (OP_Atom (EXP_Ident "arg0")));
        (* load the thread argument *)
        ("1", AtomicLoad not_atomic (OP_IBinop Add (EXP_Ident "arg0") 2%Z))
      (* pass the thread argument to the function *)
      ] (Return (OP_Atom (EXP_Ident "1")))] []).

  Definition thrd_cleanup : definition :=
    ("__thrd_cleanup",
      mkCFG "0" [mk_block "0" [
        (* store the return value *)
        ("0", AtomicRMW acq_rel ATOMIC_xchg (OP_Atom (EXP_Ident "arg1")) (OP_IBinop Add (EXP_Ident "arg0") 1));
        (* synchronize with the joining thread *)
        ("1", AtomicRMW acq_rel ATOMIC_xchg (OP_Atom 2) (OP_Atom (EXP_Ident "arg0")))
      ] (Return (OP_Atom 0))] []).

  (* We slightly deviate from C11 semantics here: joining an already joined thread should be UB,
     but we do not support it at the time, so we just loop. *)
  Definition thrd_join label tdata nextBid retvalreg := [
    mk_block label
      (* check whether the thread is finished/joinable and update its status to joined if so *)
      [("__thrd_join_status", AtomicCmpXchg acq_rel (OP_Atom 2) (OP_Atom 3) (OP_Atom tdata))]
      (* loop if it is not the case *)
      (Jmp2 (OP_ICmp Eq (EXP_Ident "__thrd_join_status") 2) label (label ++ "_end"));
    mk_block (label ++ "_end")
      (* load the return value of the thread *)
      [(retvalreg, AtomicLoad acquire (OP_IBinop Add tdata 1))]
      (Jmp1 nextBid)
  ]%string.

  (* lighter version that justs syncs-with at thread creation, and does not support join *)

  Definition simple_thrd_create f (arg : exp) (tdatareg : string) := [
    (* allocate the thread data structure *)
    (tdatareg, Alloca (OP_Atom 1));
    (* store the thread argument *)
    ("__thrd_create_1", AtomicRMW acq_rel ATOMIC_xchg arg (OP_Atom (EXP_Ident tdatareg)));
    (* spawn the thread *)
    ("__thrd_create_2", ThreadCreate f "__simple_thrd_init" "__simple_thrd_cleanup" (OP_Atom (EXP_Ident tdatareg)))
  ].

  Definition simple_thrd_init : definition :=
    ("__simple_thrd_init",
      mkCFG "0" [mk_block "0" [
        (* synchronize with the parent thread and load the thread argument *)
        ("0", AtomicRMW acq_rel ATOMIC_add (OP_Atom 0) (OP_Atom (EXP_Ident "arg0")))
      (* pass the thread argument to the function *)
      ] (Return (OP_Atom (EXP_Ident "0")))] []).

  Definition simple_thrd_cleanup : definition :=
    ("__simple_thrd_cleanup",
      mkCFG "0" [mk_block "0" [
      ] (Return (OP_Atom 0))] []).


End Thrd.