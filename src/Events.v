From Coq Require Import
     Lists.List
     Strings.String
     ZArith.

From ExtLib Require Import
     Core.RelDec
     Data.Nat
     Data.String
     Structures.Monad.

From ITree Require Import
     Events.Exception.

From CTree Require Import
     CTree
     Eq.

Import MonadNotation.

Open Scope monad_scope.

(* Basic types and values. This could be isolated in a module for more genericity. *)

Definition function_id := string.
Definition thread_id := nat.
Definition addr := nat.
Definition ident := string.

Section Value.

  Definition value := Z.

  Definition nullptr := 0%Z.
  Definition nullval := nullptr.

  Definition value_eqb v v' := Z.eqb v v'.

End Value.

(* LLVM orderings and constraints on them *)

Variant ordering : Set :=
| not_atomic (*| unordered*) | monotonic | acquire | release | acq_rel | seq_cst.

Definition is_supported_read_ordering o :=
  match o with
  | release | acq_rel => false
  | _ => true
  end.

Definition is_supported_write_ordering o :=
  match o with
  | acquire | acq_rel => false
  | _ => true
  end.

Definition is_supported_rmw_ordering o :=
  match o with
  | not_atomic => false
  | _ => true
  end.

Definition is_supported_fence_ordering o :=
  match o with
  | not_atomic => false
  | _ => true
  end.

Definition is_acquire o :=
  match o with acquire | acq_rel | seq_cst => true | _ => false end.

Definition is_release o :=
  match o with release | acq_rel | seq_cst => true | _ => false end.

Definition is_sc o :=
  match o with seq_cst => true | _ => false end.

Definition is_not_atomic o :=
  match o with not_atomic => true | _ => false end.


(* Events *)

(* Memory accesses of a thread. *)
Variant MemoryE : Type -> Type :=
| Read (o: ordering) (k: addr) : MemoryE value
| Write (o: ordering) (k: addr) (v: value) : MemoryE unit
| ReadWrite (o: ordering) (k: addr) (f: value -> value) : MemoryE value (* read-modify-write *)
| Fence (o: ordering) : MemoryE unit
.

(* Memory allocation *)
Variant AllocE : Type -> Type :=
| Alloc (size : nat) : AllocE addr
.

(* A Spawn event creates a new thread. *)
Inductive ThreadE {Arg} : Type -> Type :=
| Spawn (f init cleanup : function_id) (arg : Arg) : ThreadE thread_id
| SetAtomic (atomic : bool) : ThreadE unit
.

(* Starting an atomic section *)
Notation Atomic := (SetAtomic true).
(* Yielding control to the scheduler *)
Notation Yield := (SetAtomic false).

(* Interactions with variables *)
Variant VarE : Type -> Type :=
| NewFrame: VarE unit
| LocalWrite (id: ident) (v: value): VarE unit
| LocalRead  (id: ident): VarE value
| GlobalRead (id: ident): VarE value.

(* Event transformer that adds a thread ID annotation *)
Variant ThreadAnnotE E : Type -> Type :=
| ThreadAnnot {X} (tid : thread_id) (e : E X) : ThreadAnnotE E X.

Arguments ThreadAnnot {E X}.

Definition ExceptC T := exceptE (string * T).
Notation cthrow m msg := (br (Throw (msg, m)) (fun x : void => match x with end)).

(* Nondeterministic choice of an undef value *)
Variant PickC : Type -> Type :=
| Pick : PickC value.

(* Scheduling event independent of the memory model. *)
Variant SchedC : Type -> Type :=
| Sched (ready: list thread_id) : SchedC thread_id
.
