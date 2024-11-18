From Coq Require Import
     Lia
     Lists.List
     NArith
     ZArith
     Strings.String.

From ExtLib Require Import
     Data.String
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Monad
     Core.Subevent
     Events.State
     Indexed.Sum
.
Unset Universe Checking.
From CTree Require Import
     CTree
     Eq
     Eq.IterFacts
     Interp.Fold
     Interp.FoldStateT
.

From Mem Require Import Utils Events Sched Pick SC.

Import ListNotations.
Import CTreeNotations.

Open Scope string_scope.
Open Scope list_scope.
Open Scope Z_scope.

Section TSOMemory.

Definition memory := NatMap.t value.

Record TSOMem := mk_TSOMem {
  globalMem : memory;
  threadMem : TMap.t memory;
}.

Definition empty_mem := mk_TSOMem NatMap.empty TMap.empty.

Variant TSOFlushC : Type -> Type :=
| TSOFlush (mem: TSOMem) : TSOFlushC (list thread_id).

Definition thread_mem mem tid :=
  TMap.find_or tid NatMap.empty mem.(threadMem).

Definition thread_view mem tid :=
  NatMapFacts.extend mem.(globalMem) (thread_mem mem tid).

Definition mem_read mem tid addr : option value :=
  NatMap.find addr (thread_view mem tid).

Definition mem_write mem tid addr val : TSOMem :=
  let tm := NatMap.add addr val (thread_mem mem tid) in
  mk_TSOMem mem.(globalMem) (NatMap.add tid tm mem.(threadMem)).

Definition mem_flush (mem: TSOMem) (tid: thread_id) : TSOMem :=
    let gm := thread_view mem tid in
    mk_TSOMem gm (TMap.add tid NatMap.empty mem.(threadMem)).

Definition tso_fence o mem tid : TSOMem :=
  if is_release o then mem_flush mem tid else mem.

Lemma thread_mem_flush_eq : forall mem tid,
  thread_mem (mem_flush mem tid) tid = TMap.empty.
Proof.
  intros. unfold thread_mem, mem_flush.
  cbn. apply NatMapFacts.find_or_add_eq_o.
Qed.

Lemma thread_mem_flush_neq : forall mem tid tid',
  tid <> tid' ->
  thread_mem (mem_flush mem tid') tid = thread_mem mem tid.
Proof.
  intros. unfold thread_mem at 1, mem_flush. cbn.
  apply NatMapFacts.find_or_add_neq_o; auto.
Qed.

Lemma thread_mem_write_neq : forall mem tid tid' addr v,
  tid <> tid' ->
  thread_mem (mem_write mem tid' addr v) tid = thread_mem mem tid.
Proof.
  intros. unfold thread_mem at 1.
  cbn. apply NatMapFacts.find_or_add_neq_o; auto.
Qed.

Lemma thread_mem_fence_neq : forall o mem tid tid',
  tid <> tid' ->
  thread_mem (tso_fence o mem tid') tid = thread_mem mem tid.
Proof.
  intros. unfold tso_fence. destruct (is_release o); auto.
  apply thread_mem_flush_neq; auto.
Qed.

Lemma thread_view_flush_eq : forall mem tid,
  thread_view (mem_flush mem tid) tid = thread_view mem tid.
Proof.
  intros. unfold thread_view at 1. rewrite thread_mem_flush_eq.
  cbn. reflexivity.
Qed.

Lemma thread_view_flush_neq : forall mem tid tid',
  tid <> tid' ->
  thread_view (mem_flush mem tid') tid = NatMapFacts.extend (thread_view mem tid') (thread_mem mem tid).
Proof.
  intros. unfold thread_view at 1.
  now rewrite thread_mem_flush_neq.
Qed.

Lemma mem_read_write_eq : forall mem tid addr v,
  mem_read (mem_write mem tid addr v) tid addr = Some v.
Proof.
  intros. unfold mem_read, mem_write, thread_view, thread_mem. cbn.
  rewrite NatMapFacts.find_or_add_eq_o.
  apply NatMapFacts.extend_find_iff. left.
  now rewrite NatMapFacts.add_eq_o.
Qed.

Lemma mem_read_write_neq : forall mem tid tid' addr addr' v,
  tid <> tid' \/ addr <> addr' ->
  mem_read (mem_write mem tid addr v) tid' addr' = mem_read mem tid' addr'.
Proof.
  intros. unfold mem_read, mem_write, thread_view, thread_mem. cbn.
  assert (tid <> tid' \/ (tid = tid' /\ addr <> addr')) by lia. clear H.
  destruct H0 as [| [<- ?]].
  - rewrite NatMapFacts.find_or_add_neq_o. reflexivity. apply H.
  - rewrite NatMapFacts.find_or_add_eq_o.
    rewrite NatMapFacts.add_extend_r.
    rewrite NatMapFacts.add_neq_o; auto.
Qed.

Lemma mem_read_flush_eq : forall mem tid addr,
  mem_read (mem_flush mem tid) tid addr = mem_read mem tid addr.
Proof.
  intros. unfold mem_read. now rewrite thread_view_flush_eq.
Qed.

Lemma mem_read_fence_eq : forall o mem tid addr,
  mem_read (tso_fence o mem tid) tid addr = mem_read mem tid addr.
Proof.
  intros. unfold tso_fence. destruct (is_release o); auto.
  now rewrite mem_read_flush_eq.
Qed.

Lemma mem_flush_empty : forall mem tid,
  thread_mem mem tid = NatMap.empty -> mem_flush mem tid = mem.
Proof.
  intros. unfold mem_flush, thread_view. rewrite H. cbn.
Abort.

Definition handle_mem {E C} `{TSOFlushC -< C} `{PickC -< C} :
  ThreadAnnotE MemoryE ~> Monads.stateT TSOMem (ctree E C) :=
  fun _ e s =>
    '(s, r) <- match e with ThreadAnnot tid e =>
      match e in (MemoryE T) return (ctree E C (TSOMem * T)) with
      | Read _ a =>
        v <- freeze (mem_read s tid a);;
        Step (Ret (s, v))
      | Write o a v =>
        Step (Ret (tso_fence o (mem_write s tid a v) tid, tt))
      | ReadWrite o a f =>
        oldv <- freeze (mem_read s tid a);;
        Step (Ret (tso_fence o (mem_write s tid a (f oldv)) tid, oldv))
      | Fence o =>
        Step (Ret (tso_fence o s tid, tt))
      end
    end;;
    to_flush <- branch (TSOFlush s);;
    let s := fold_left (fun s tid => mem_flush s tid) to_flush s in
    Ret (s, r).

End TSOMemory.

Section InterpTSO.

  Context {E C : Type -> Type}.

  Definition E_trigger : E ~> Monads.stateT TSOMem (ctree E (TSOFlushC +' PickC +' C)) :=
    fun _ e m => r <- trigger e ;; ret (m, r).

  Definition interp_mem_h : ThreadAnnotE MemoryE +' E ~>
    Monads.stateT TSOMem (ctree E (TSOFlushC +' PickC +' C)) :=
    case_ handle_mem E_trigger.

  Definition interp_mem :
    ctree (ThreadAnnotE MemoryE +' E) C ~>
    Monads.stateT TSOMem (ctree E (TSOFlushC +' PickC +' C)) :=
    interp interp_mem_h.

End InterpTSO.

Lemma mem_read_empty_thread_mem :
  forall tso a tid,
  thread_mem tso tid = NatMap.empty ->
  mem_read tso tid a = NatMap.find a tso.(globalMem).
Proof.
  intros. unfold mem_read, thread_view. now rewrite H.
Qed.

Definition Lmem (sc : SC.SCMem) (tso : TSOMem) :=
  (forall a, SC.mem_read sc a = NatMap.find a tso.(globalMem)) /\
  forall tid, thread_mem tso tid = NatMap.empty.

Definition Lmem' : rel (SC.SCMem * unit) (TSOMem * unit) :=
  fun a b => Lmem (fst a) (fst b).

Lemma Lmem_flush : forall sc tso tid, Lmem sc tso -> Lmem sc (mem_flush tso tid).
Proof.
  intros.
  destruct H as (? & ?).
  split; intros.
  - cbn.
    unfold mem_flush, thread_view. rewrite H0. cbn. rewrite H.
    reflexivity.
  - destruct (Nat.eq_dec tid tid0) as [<- | ?].
    + now rewrite thread_mem_flush_eq.
    + rewrite thread_mem_flush_neq; auto.
Qed.

Lemma Lmem_tso_fence : forall sc tso o tid, Lmem sc tso -> Lmem sc (tso_fence o tso tid).
Proof.
  intros.
  unfold tso_fence. destruct (is_release o); auto.
  now apply Lmem_flush.
Qed.

Lemma Lmem_write : forall sc tso o tid addr v, Lmem sc tso ->
  Lmem (SC.mem_write sc addr v) (mem_flush (tso_fence o (mem_write tso tid addr v) tid) tid).
Proof.
  intros. split; cbn; intros.
  - destruct (Nat.eq_dec a addr) as [<- | ?].
    + rewrite SC.mem_read_write_eq.
      cbn.
      setoid_rewrite mem_read_fence_eq.
      now rewrite mem_read_write_eq.
    + rewrite SC.mem_read_write_neq; auto.
      cbn. setoid_rewrite mem_read_fence_eq.
      rewrite mem_read_write_neq; auto.
      rewrite mem_read_empty_thread_mem.
      * apply H.
      * apply H.
  - destruct (Nat.eq_dec tid tid0) as [-> | ?].
    { rewrite thread_mem_flush_eq; auto. }
    rewrite thread_mem_flush_neq; auto.
    rewrite thread_mem_fence_neq; auto.
    rewrite thread_mem_write_neq; auto.
    apply H.
Qed.

Theorem ss_sc_tso {E C} : forall (t : ctree (ThreadAnnotE MemoryE +' E) C unit)
  m m',
  Lmem m m' ->
  (SC.interp_mem _ t m)
    (≲ lift_val_rel Lmem')
    (@interp_mem E C _ t m').
Proof.
  intros.
  eapply ssim_interp_state_h with (Rs := Lmem).
  3: trivial.
  { split. constructor; etrans. intros. constructor. assumption. }
  intros. eapply weq_ssim. eapply update_val_rel_update_val_rel.
  unfold interp_mem_h, handle_mem.
  destruct e as [[_ ? []] | ?]; cbn.
  - (* Read *)
    rewrite (proj1 H0).
    rewrite mem_read_empty_thread_mem; [| apply H0].
    destruct (NatMap.find k st'.(globalMem)) eqn:?; cbn.
    + rewrite !bind_ret_l, bind_step.
      apply step_ssim_step; [| constructor; etrans].
      rewrite bind_ret_l, bind_branch.
      apply ssim_br_r with (x := []).
      apply ssim_ret. constructor. split; auto.
    + rewrite bind_bind, !bind_branch. apply ssim_br_id. intros.
      rewrite bind_step. apply step_ssim_step; [| constructor; etrans].
      rewrite bind_ret_l, bind_branch. apply ssim_br_r with (x := []).
      apply ssim_ret. constructor. split; auto.
  - (* Write *)
    rewrite bind_step. apply step_ssim_step; [| constructor; etrans].
    rewrite bind_ret_l, bind_branch.
    apply ssim_br_r with (x := [tid]).
    apply ssim_ret. constructor. split; auto.
    eapply Lmem_write in H0. apply H0.
  - (* ReadWrite *)
    rewrite bind_bind.
    rewrite mem_read_empty_thread_mem; [| apply H0].
    rewrite (proj1 H0). destruct (NatMap.find k _) eqn:?; cbn.
    + rewrite !bind_ret_l, bind_step.
      apply step_ssim_step; [| constructor; etrans].
      rewrite bind_ret_l, bind_branch.
      apply ssim_br_r with (x := [tid]).
      apply ssim_ret. constructor. split; auto.
      now apply Lmem_write.
    + rewrite !bind_branch. apply ssim_br_id. intros.
      rewrite bind_step. apply step_ssim_step; [| constructor; etrans].
      rewrite bind_ret_l, bind_branch.
      apply ssim_br_r with (x := [tid]).
      apply ssim_ret. constructor. split; auto.
      now apply Lmem_write.
  - (* Fence *)
    rewrite bind_step. apply step_ssim_step; [| constructor; etrans].
    rewrite bind_ret_l, bind_branch.
    apply ssim_br_r with (x := []).
    apply ssim_ret. constructor. split; auto.
    now apply Lmem_tso_fence.
  - cbn. unfold SC.E_trigger, E_trigger. rewrite !bind_trigger. apply ssim_vis_id.
    intros. split; [| now constructor ].
    apply ssim_ret. constructor. auto.
Qed.

Section TSOFlush.

Definition flushable tso :=
  TMap.keys (TMap.filter (fun _ m => negb (TMap.is_empty m)) tso.(threadMem)).

(* Handler that never flushes *)
Definition handle_flush_never {E C} :
  TSOFlushC ~> ctree E C :=
  fun _ e =>
    match e with
    | TSOFlush _ => ret []
    end.

(* Handler that randomly flushes at most one thread *)
Definition handle_flush_random {E C} :
  TSOFlushC ~> Monads.stateT N (ctree E C) :=
  fun _ e seed =>
  match e with
  | TSOFlush s =>
    let n := NatMap.cardinal s.(threadMem) in
    let '(seed, rd) := rand seed (N.of_nat (S n)) in
    let to_flush := if Nat.eqb (N.to_nat rd) n then [] else [N.to_nat rd] in
    ret (seed, to_flush)
  end.

End TSOFlush.

Section InterpFlush.

  Context {E B : Type -> Type}.
  Context {S : Type}.
  Variable handler : TSOFlushC ~> Monads.stateT S (ctree E B).

  Definition B_branch' : B ~> Monads.stateT S (ctree E B) := fun _ x m => c <- branch x;; ret (m, c).

  Definition interp_flush_h : TSOFlushC +' B ~> Monads.stateT S (ctree E B) :=
    case_ handler B_branch'.

  Definition interp_flush : ctree E (TSOFlushC +' B) ~> Monads.stateT S (ctree E B) :=
    refine interp_flush_h.

End InterpFlush.
