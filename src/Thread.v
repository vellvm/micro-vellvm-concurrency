From Coq Require Import
     Lists.List
     String.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad.

From Coinduction Require Import all.
From ITree Require Import
     Core.Subevent
     Indexed.Sum.

Unset Universe Checking.
From CTree Require Import
     CTree
     Eq
     Interp.FoldStateT
     Misc.Head.

From Mem Require Import Utils Events Sched.

Import ListNotations.

Open Scope ctree_scope.
Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Section Thread.

Context {Arg A : Type} {E TE F C : Type -> Type}.
Context `{E -< F} `{ThreadAnnotE TE -< F}.
Context (fns : FnMap.t (list Arg -> ctree (@ThreadE (list Arg) +' TE +' E) C A)).
Context (get_val : A -> Arg).

Section build_thread_ctree.
Import MonadNotation.

(* Build the ctree of a thread by binding the thread init ctree,
   the ctree of the actual task to run, and the thread cleanup ctree. *)
Definition build_thread_ctree (f init cleanup : function_id) (args : list Arg) :
  option (ctree (ThreadE +' TE +' E) C A) :=
  init <- FnMap.find init fns;;
  f <- FnMap.find f fns;;
  cleanup <- FnMap.find cleanup fns;;
  Some (
    farg <- init args;;
    trigger Yield;;
    retval <- f [get_val farg];;
    trigger Yield;;
    cleanup (args ++ [get_val retval])
  ).

End build_thread_ctree.

Import CTreeNotations.

Definition add_thread_ctree nextTid tl f init cleanup a :=
  match build_thread_ctree f init cleanup a with
  | Some t => TMap.add nextTid t tl
  | None => tl
  end.

Definition step_thread_event {X}
    atomic nextTid tid
    (l : TMap.t (ctree (ThreadE +' TE +' E) C A))
    (e : @ThreadE (list Arg) X) (k : X -> ctree (ThreadE +' TE +' E) C A) :
    ctree F (SchedC +' C) (bool * thread_id * TMap.t _) :=
  match e, k with
  | Spawn f init cleanup a, k =>
    Ret (atomic, S nextTid,
      (TMap.add tid (k nextTid) (add_thread_ctree nextTid l f init cleanup a)))
  | SetAtomic atomic, k =>
    Ret (atomic, nextTid, TMap.add tid (k tt) l)
  end.

Definition step_thread
    atomic nextTid tid
    (l : TMap.t (ctree (ThreadE +' TE +' E) C A))
    (t : ctree (ThreadE +' TE +' E) C A) :
    ctree F (SchedC +' C) (bool * thread_id * TMap.t _) :=
  h <- Head.head t;;
  match h with
  | ARet r =>
    Ret (false, nextTid, (TMap.remove tid l))
  | AStep t =>
      Step (
        Ret (atomic, nextTid, TMap.add tid t l))
  | AVis e k =>
    match e with
    | inl1 e =>
      step_thread_event atomic nextTid tid l e k
    | inr1 (inl1 e) =>
      vis (ThreadAnnot tid e) (fun x =>
        Ret (atomic, nextTid, TMap.add tid (k x) l))
    | inr1 (inr1 e) =>
      vis e (fun x =>
        Ret (atomic, nextTid, TMap.add tid (k x) l))
    end
  end.

Notation step_thread_ atomic nextTid tid l t :=
  (match observe t with
  | RetF r =>
    Ret (false, nextTid, (TMap.remove tid l))
  | StuckF => Stuck
  | StepF t =>
      Step (
        Ret (atomic, nextTid, TMap.add tid t l))
  | GuardF t =>
      Guard (step_thread atomic nextTid tid l t)
  | BrF c k =>
      br c (fun x => step_thread atomic nextTid tid l (k x))
  | VisF e k =>
    match e with
    | inl1 e =>
      step_thread_event atomic nextTid tid l e k
    | inr1 (inl1 e) =>
      vis (ThreadAnnot tid e) (fun x =>
        Ret (atomic, nextTid, TMap.add tid (k x) l))
    | inr1 (inr1 e) =>
      vis e (fun x =>
        Ret (atomic, nextTid, TMap.add tid (k x) l))
    end
  end).

Lemma unfold_step_thread : forall
  atomic nextTid tid
  (l : TMap.t (ctree (ThreadE +' TE +' E) C A)) t,
  step_thread atomic nextTid tid l t ≅ step_thread_ atomic nextTid tid l t.
Proof.
  intros. unfold step_thread. rewrite unfold_head.
  destruct (observe t); try now rewrite bind_ret_l.
  - now rewrite bind_stuck.
  - now rewrite bind_guard.
  - now rewrite bind_br.
Qed.

(* Builds a ctree that represents a concurrent computation
   from the ctrees of several threads. *)
Definition interleave
  tidExec nextTid (l : TMap.t (ctree (ThreadE +' TE +' E) C A)) :
  ctree F (SchedC +' C) nat :=
  CTree.iter (fun '(tidExec, nextTid, l) =>
    if TMap.is_empty l then Ret (inr nextTid) else
    '(tidExec, atomic) <- match tidExec with
    | Some tidExec => Ret (tidExec, true)
    | None => br (Sched (TMap.keys l)) (fun tid => Ret (tid, false))
    end;;
    match TMap.find tidExec l with
    | Some t =>
      CTree.bind (step_thread atomic nextTid tidExec l t)
       (fun '(atomic, nextTid, l) =>
         Ret (inl (if atomic then Some tidExec else None, nextTid, l)))
    | None => Ret (inl (None, nextTid, l))
    end) (tidExec, nextTid, l).

Notation interleave_ atomic nextTid l :=
  (if TMap.is_empty l then Ret nextTid else
  tidExec <- branch (Sched (TMap.keys l));;
  match TMap.find tidExec l with
  | Some t =>
      CTree.bind (step_thread atomic nextTid tidExec l t)
       (fun '(atomic, nextTid, l) =>
         Guard (interleave (if atomic then Some tidExec else None) nextTid l))
  | None => Guard (interleave None nextTid l)
  end).

Definition step_interleave
  atomic nextTid tidExec (l : TMap.t (ctree (ThreadE +' TE +' E) C A)) t :
    ctree F (SchedC +' C) nat :=
  '(atomic, nextTid, l) <- step_thread atomic nextTid tidExec l t;;
  Guard (interleave (if atomic then Some tidExec else None) nextTid l).

Theorem interleave_step_interleave : forall tidExec nextTid l,
  interleave tidExec nextTid l ≅
  if TMap.is_empty l then Ret nextTid else
  '(tidExec, atomic) <- match tidExec with
  | Some tidExec => Ret (tidExec, true)
  | None => br (Sched (TMap.keys l)) (fun tid => Ret (tid, false))
  end;;
  match TMap.find tidExec l with
  | Some t =>
    step_interleave atomic nextTid tidExec l t
  | None => Guard (interleave None nextTid l)
  end.
Proof.
  intros. unfold interleave. rewrite unfold_iter.
  destruct (TMap.is_empty l).
  - now rewrite bind_ret_l.
  - rewrite bind_bind. destruct tidExec.
    + rewrite !bind_ret_l.
      destruct (TMap.find k l).
      * rewrite !bind_bind. unfold step_interleave. cbn.
        upto_bind_eq. intros ((? & ?) & ?).
        rewrite bind_ret_l. reflexivity.
      * rewrite bind_ret_l. reflexivity.
    + upto_bind_eq. intros [].
      destruct (TMap.find k l).
      * rewrite bind_bind. unfold step_interleave. cbn.
        upto_bind_eq. intros ((? & ?) & ?).
        rewrite bind_ret_l. reflexivity.
      * rewrite bind_ret_l. reflexivity.
Qed.

(* Builds a ctree that represents a concurrent computation
   from the ctree of a main thread that can spawn more threads. *)
Definition interleave_top
  (main : ctree (ThreadE +' TE +' E) C A) :
  ctree F (SchedC +' C) nat :=
  interleave None 2%nat (TMap.singleton 1%nat main).

Definition handle_thread (tid : thread_id) : @ThreadE Arg ~> Monads.stateT nat (ctree F (SchedC +' C)) :=
  fun _ e s =>
    match e with
    | Spawn f init cleanup a => Ret (S s, s)
    | SetAtomic _ => Ret (s, tt)
    end.

Definition interp_thread_h tid :
  ThreadE +' TE +' E ~> Monads.stateT nat (ctree F (SchedC +' C)) :=
  fun _ e =>
    match e with
    | inl1 e => handle_thread tid _ e
    | inr1 (inl1 e) => Monads.liftState (trigger (ThreadAnnot tid e))
    | inr1 (inr1 e) => Monads.liftState (trigger e)
    end.

(* step_thread could probably be defined in terms of interp_thread and head *)
Definition interp_thread
  tidExec nextTid (t : (ctree (ThreadE +' TE +' E) C A)) :
  ctree F (SchedC +' C) (thread_id * A) :=
  interp_state (interp_thread_h tidExec) t nextTid.

(* Combine two concurrent ctrees into one (parallel operator),
   assuming their thread IDs are disjoint *)
(* this is not actually used and may be removed in the future *)
CoFixpoint merge_threads {E C}
  (t1 t2 : ctree E (SchedC +' C) unit) :
  ctree E (SchedC +' C) unit :=
  match observe t1, observe t2 with
  | RetF _, _ => t2
  | _, RetF _ => t1
  | StuckF, _ | _, StuckF => Stuck
  | VisF e k, _ => Vis e (fun x => merge_threads (k x) t2)
  | _, VisF e k => Vis e (fun x => merge_threads t1 (k x))
  | StepF t1, _ => Step (merge_threads t1 t2)
  | _, StepF t2 => Step (merge_threads t1 t2)
  | GuardF t1, _ => Guard (merge_threads t1 t2)
  | _, GuardF t2 => Guard (merge_threads t1 t2)
  | BrF c1 k1, BrF c2 k2 => br c2 (fun x => merge_threads t1 (k2 x))
  end.

End Thread.
