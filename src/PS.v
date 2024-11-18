From Coq Require Import
     Classes.RelationPairs
     Init.Logic
     Lia
     Lists.List
     QArith
     QArith.Qminmax
     ZArith
     Strings.String.

From ExtLib Require Import
     Data.String
     Structures.Monad.

From Coinduction Require Import all.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations
     Core.Subevent
     Events.Exception
     Indexed.Sum.
Unset Universe Checking.
From CTree Require Import
     CTree
     Eq
     Fold
     FoldCTree
     FoldStateT
     Misc.Pure.

From Mem Require Import Utils Events Sched Pick SC Message.


Import ListNotations.
Import MonadNotation.

Open Scope string_scope.
Open Scope list_scope.

Definition DebugLogC := void1.
Definition tell {E C} (s: string) : ctree E C unit := Ret tt.

Record ThreadState := mkThread {
  cur_view : NatMap.t date_type;
  acq_view : NatMap.t date_type;
  (* for each address, a view *)
  rel_view : NatMap.t (NatMap.t date_type);
}.

Definition empty_thread := mkThread NatMap.empty NatMap.empty NatMap.empty.

Record PSMem := mk_PSMem {
  threads : TMap.t ThreadState;
  globalMem : msg_set;
  seqView : view_type;
}.

Notation PSExceptC := (ExceptC PSMem).

Definition empty_mem := mk_PSMem TMap.empty empty_msg_set NatMap.empty.

Inductive PSAccess : Type :=
| PSRead
| PSFulfill (v: value)
| PSFulfillUpdate
.

(* the first date is ignored for PSRead *)
Inductive PSMemC : Type -> Type :=
| PSUpdateView (mem: PSMem) (tid: thread_id) (a: addr) (access: PSAccess) : PSMemC (date_type * date_type)
.

Definition thread_state ps tid :=
  TMap.find_or tid empty_thread ps.(threads).

Definition thread_rel_view ps tid :=
  (thread_state ps tid).(rel_view).

Definition thread_view ps tid :=
  (thread_state ps tid).(cur_view).

Definition thread_acq_view ps tid :=
  (thread_state ps tid).(acq_view).

Definition seq_view ps :=
  ps.(seqView).

Definition mem_eq ps ps' :=
  NatMap.Equal1 (QMap.Equal (elt := _)) ps.(globalMem) ps'.(globalMem) /\
  NatMap.Equal ps.(seqView) ps'.(seqView) /\
  forall tid,
    NatMap.Equal1 (NatMap.Equal1 Qeq) (thread_rel_view ps tid) (thread_rel_view ps' tid) /\
    NatMap.Equal1 Qeq (thread_view ps tid) (thread_view ps' tid) /\
    NatMap.Equal1 Qeq (thread_acq_view ps tid) (thread_acq_view ps' tid).

(* check that there is only one possible message to read from, and return its value *)
Definition mem_read_na ps tid a : option value :=
  let msg := last_msg a ps.(globalMem) in
  match msg with
  | Some msg =>
    let tview := thread_view ps tid in
    if Qeq_bool msg.(ts_to) (NatMap.find_or a 0%Q tview)
    then Some msg.(val)
    else None
  | None => None
  end.

(* if an atomic read can read from several different messages including a non-atomic one, it returns undef *)
Definition is_racy olddate date (oldview view : view_type) :=
  (negb (Qeq_bool olddate 0%Q) && NatMap.is_empty oldview) ||
  (negb (Qeq_bool olddate date) && NatMap.is_empty view).

Definition do_mem_read ord ps tid a date : PSMem * view_type * option value :=
  let mem := ps.(globalMem) in
  let tview := thread_view ps tid in
  let acq := thread_acq_view ps tid in
  let rel := thread_rel_view ps tid in
  let seq := seq_view ps in
  (* perform the read *)
  let olddate := NatMap.find_or a 0%Q tview in
  let oldmsg := value_or (find_message a olddate mem) empty_msg in
  let msg := value_or (find_message a date mem) empty_msg in
  let mview := msg.(view) in
  let val := option_map val (find_message a date mem) in
  (* if we can read from several different messages including a non-atomic one, we return undef *)
  let val := if is_racy olddate date oldmsg.(view) mview then None else val in
  (* update the acq view *)
  let acq := NatMap.add a date acq in
  let acq := if is_acquire ord then merge_views acq mview else acq in
  (* update the cur view *)
  let tview := NatMap.add a date tview in
  let tview := if is_acquire ord then merge_views tview mview else tview in
  (* merge the cur and global view if this is an SC read *)
  let tview := if is_sc ord then merge_views tview seq else tview in
  let seq := if is_sc ord then tview else seq in
  let acq := if is_sc ord then merge_views acq seq else acq in
  let thread := mkThread tview acq rel in
  (mk_PSMem (TMap.add tid thread ps.(threads)) mem seq, mview, val).

Definition mem_read ord ps tid a date : PSMem * string + PSMem * view_type * option value :=
  let tview := thread_view ps tid in
  if negb (Qle_bool (TMap.find_or a 0%Q tview) date)
  then inl (ps, "read date in the past") else
  if is_none (find_message a date ps.(globalMem)) && negb (Qeq_bool date 0%Q)
  then inl (ps, "invalid read timestamp") else
  ret (do_mem_read ord ps tid a date).

Definition do_mem_write ord ps tid msg : PSMem :=
  let mem := ps.(globalMem) in
  let tview := thread_view ps tid in
  let acq := thread_acq_view ps tid in
  let rel := thread_rel_view ps tid in
  let rel_a := NatMap.find_or msg.(a) NatMap.empty rel in
  let seq := seq_view ps in
  let prev_view := TMap.find_or msg.(a) 0%Q tview in
  (* update the cur and acq views *)
  let tview := TMap.add msg.(a) msg.(ts_to) tview in
  let acq := TMap.add msg.(a) msg.(ts_to) acq in
  (* merge the cur and global view if this is an SC write *)
  let tview := if is_sc ord then merge_views tview seq else tview in
  let seq := if is_sc ord then tview else seq in
  let acq := if is_sc ord then merge_views acq seq else acq in
  (* copy the cur view to the rel view if this is a release write *)
  let rel_a := if is_release ord then tview else rel_a in
  (* create the message view, based on the given view (useful for RMW release sequences) and the release view *)
  let mview := merge_views rel_a msg.(view) in
  let mview := NatMap.add msg.(a) msg.(ts_to) rel_a in
  let mview := if is_not_atomic ord then NatMap.empty else mview in
  (* add the message to memory *)
  let msg := mkMsg msg.(a) msg.(val) msg.(ts_from) msg.(ts_to) mview in
  let mem := add_message msg mem in
  let thread := mkThread tview acq rel in
  mk_PSMem (TMap.add tid thread ps.(threads)) mem seq.

Definition mem_write ord ps tid msg : PSMem * string + PSMem :=
  let mem := ps.(globalMem) in
  let tview := thread_view ps tid in
  let prev_view := TMap.find_or msg.(a) 0%Q tview in
  if negb (Qle_bool prev_view msg.(ts_from))
  then inl (ps, ("write date " ++ Q2string msg.(ts_to) ++ " in the past, view = " ++ Q2string prev_view)%string) else
  (* check for timestamp collision *)
  let next := find_msg_gt msg.(a) msg.(ts_from) mem in
  let next := value_or (option_map ts_from next) msg.(ts_to) in
  if negb (Qle_bool msg.(ts_to) next)
  then inl (ps, "message overlapping") else
  ret (do_mem_write ord ps tid msg).

Definition mem_fence ord ps tid : PSMem :=
  let tview := thread_view ps tid in
  let acq := thread_acq_view ps tid in
  let rel := thread_rel_view ps tid in
  let seq := seq_view ps in
  (* acq *)
  let tview := if is_acquire ord
    then merge_views tview acq
    else tview in
  (* SC *)
  let acq := if is_sc ord then merge_views acq seq else acq in (* ? *)
  let tview := if is_sc ord then merge_views tview seq else tview in
  let seq := if is_sc ord then tview else seq in
  (* rel *)
  let rel := if is_release ord then NatMap.map (fun _ => tview) ps.(globalMem) else rel in
  let thread := mkThread tview acq rel in
  mk_PSMem (TMap.add tid thread ps.(threads)) ps.(globalMem) seq.

Definition lift_either {E C X} `{PSExceptC -< C} (v : (PSMem * string) + X) :
  ctree E C X :=
  match v with
  | inl (ps, s) => cthrow ps s
  | inr v => Ret v
  end.

Definition handle_mem {E C} `{PSMemC -< C} `{SchedC -< C} `{PickC -< C} `{PSExceptC -< C} `{DebugLogC -< C} :
  ThreadAnnotE MemoryE ~> Monads.stateT PSMem (ctree E C) :=
  fun _ e s =>
    let mem := s.(globalMem) in
    match e with ThreadAnnot tid e =>
      match e with
      | Read o a =>
        if is_not_atomic o then
          v <- freeze (mem_read_na s tid a);;
          Step (ret (s, v))
        else
          '(_, date) <- branch (PSUpdateView s tid a PSRead);;
          r <- lift_either (mem_read o s tid a date);;
          v <- freeze (snd r);;
          Step (ret (fst (fst r), v))
      | Write o a v =>
        '(ts_from, ts_to) <- branch (PSUpdateView s tid a (PSFulfill v));;
        s <- lift_either (mem_write o s tid (mkMsg a v ts_from ts_to NatMap.empty));;
        Step (ret (s, tt))
      | ReadWrite o a f =>
        '(ts_from, ts_to) <- branch (PSUpdateView s tid a PSFulfillUpdate);;
        r <- lift_either (mem_read o s tid a ts_from);;
        let s := fst (fst r) in
        let mview := snd (fst r) in
        let val := snd r in
        val <- freeze val;;
        s <- lift_either (mem_write o s tid (mkMsg a (f val) ts_from ts_to mview));;
        Step (ret (s, val))
      | Fence o =>
        Step (ret (mem_fence o s tid, tt))
      end
    end.

Section InterpPS.

  Context {E F C D : Type -> Type}.
  Context `{E -< F} `{C -< D}.
  Context `{PSMemC -< D}.
  Context `{SchedC -< D}.
  Context `{PSExceptC -< D}.
  Context `{DebugLogC -< D}.
  Context `{PickC -< D}.

  Definition E_trigger : E ~> Monads.stateT PSMem (ctree F D) :=
    fun R e m => r <- trigger e ;; ret (m, r).

  Definition interp_mem_h : (ThreadAnnotE MemoryE +' E) ~>
    Monads.stateT PSMem (ctree F D) :=
    case_ handle_mem E_trigger.

  Definition C_branch : C ~> Monads.stateT PSMem (ctree F D) := fun _ x m => c <- branch x;; ret (m, c).

  Definition interp_mem := interp_state (C := C) interp_mem_h.
End InterpPS.

Definition latest (ps: PSMem) (a: addr) (acc: PSAccess) :=
  let date := (value_or (last_msg a ps.(globalMem)) empty_msg).(ts_to) in
  match acc with
  | PSRead => (date, date)
  | _ => (date, date + 1)%Q
  end.

Arguments latest : simpl never.

Definition handle_view_sc {E C} :
  PSMemC ~> ctree E C :=
  fun _ e =>
  match e with
  | PSUpdateView mem tid a kind =>
    ret (latest mem a kind)
  end.

(* compute the list of empty date ranges between messages *)
Definition free_dates (m : QMap.t (date_type * value * view_type)) :=
  let l := QMap.bindings m in
  combine (0%Q::List.map fst l) (List.map (fun p => fst (fst (snd p))) l).

(* compute the possible timestamp pairs for the specified access *)
Definition possible_timestamps (tid : thread_id) (a : addr) (acc : PSAccess) (mem : PSMem) :=
  let m := NatMap.find_or a QMap.empty mem.(globalMem) in
  let view := NatMap.find_or a 0%Q (thread_view mem tid) in
  let r := free_dates m in
  let l := List.fold_left (fun l '(prev, next) => l ++
    match acc with
    | PSRead => [(prev, prev)]
    | PSFulfill _ =>
      if Qeq_bool prev next then [] else
      [(prev, (prev + next) / 2); (prev, next); ((2 * prev + next) / 3, (prev + 2 * next) / 3); ((prev + next) / 2, next)]%Q
    | PSFulfillUpdate =>
      if Qeq_bool prev next then [] else
      [(prev, (prev + next) / 2); (prev, next)]%Q
    end) r [] in
  let last := value_or (option_map fst (QMapFacts.O.max_elt m)) 0%Q in
  let l := l ++ match acc with
  | PSRead => [(last, last)]
  | PSFulfill _ => [(last, last + 1); (last + 1, last + 2)]%Q
  | PSFulfillUpdate => [(last, last + 1)]%Q
  end in
  List.filter (fun '(ts, _) => Qle_bool view ts) l.

Definition handle_view_random {E C} :
  PSMemC ~> Monads.stateT N (ctree E C) :=
  fun _ e seed =>
  match e with
  | PSUpdateView mem tid a kind =>
    let l := possible_timestamps tid a kind mem in
    let '(seed, rd) := rand seed (N.of_nat (List.length l)) in
    ret (seed, List.nth (N.to_nat rd) l (0, 0)%Q)
  end.

Section InterpView.

  Context {E B : Type -> Type}.
  Context {S : Type}.
  Variable handler : PSMemC ~> Monads.stateT S (ctree E B).

  Definition B_branch' : B ~> Monads.stateT S (ctree E B) := fun _ x m => c <- branch x;; ret (m, c).

  Definition interp_view_h : PSMemC +' B ~> Monads.stateT S (ctree E B) :=
    case_ handler B_branch'.

  Definition interp_view : ctree E (PSMemC +' B) ~> Monads.stateT S (ctree E B) :=
    refine interp_view_h.

End InterpView.


Lemma thread_state_mem_read_neq :
  forall o mem tid tid' a date mem' v val,
  tid <> tid' ->
  mem_read o mem tid a date = inr (mem', v, val) ->
  thread_state mem' tid' = thread_state mem tid'.
Proof.
  intros.
  unfold mem_read in H0.
  destruct (negb _) eqn:?; [discriminate |].
  destruct (andb _ _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb. apply Qle_bool_iff in Heqb.
  cbn in H0. inv H0.
  unfold thread_state. cbn.
  rewrite NatMapFacts.find_or_add_neq_o; auto.
Qed.

Lemma thread_state_mem_fence_neq :
  forall ord ra tid tid',
  tid <> tid' ->
  thread_state (mem_fence ord ra tid) tid' = thread_state ra tid'.
Proof.
  intros. unfold thread_state, mem_fence. cbn.
  rewrite NatMapFacts.find_or_add_neq_o; auto.
Qed.

Definition wf_message m :=
  (0 <= m.(ts_from))%Q /\
  (m.(ts_from) < m.(ts_to))%Q /\
  le_view NatMap.empty m.(view).

Definition wf_thread t :=
  (forall a,
    le_view NatMap.empty (NatMap.find_or a NatMap.empty t.(rel_view)) /\
    le_view (NatMap.find_or a NatMap.empty t.(rel_view)) t.(cur_view)) /\
    le_view t.(cur_view) t.(acq_view).

Definition wf_messages m :=
  (forall ts msg,
    QMap.find ts m = Some msg ->
    wf_message (rebuildMsg 0%nat ts msg)) /\
  (forall ts ts' msg msg',
    ts < ts' ->
    QMap.find ts m = Some msg ->
    QMap.find ts' m = Some msg' ->
    ts <= fst (fst msg'))%Q.

Definition wf_mem_ m :=
  forall a, wf_messages (TMap.find_or a QMap.empty m).

Definition wf_mem m :=
  (forall tid, wf_thread (thread_state m tid)) /\
  wf_mem_ m.(globalMem).

Lemma wf_mem_sorted :
  forall a ts ts' msg msg' mem,
  wf_mem_ mem ->
  (ts < ts')%Q ->
  find_message a ts mem = Some msg ->
  find_message a ts' mem = Some msg' ->
  (msg.(ts_to) <= msg'.(ts_from))%Q.
Proof.
  intros.
  apply find_message_spec in H1 as (<- & <- & ?), H2 as (? & <- & ?).
  eapply H in H3; eauto.
Qed.

Definition msg_in_ msg (msgs : msg_set) :=
  option_rel (Qeq * eq * view_eq)%signature
    (QMap.find msg.(ts_to) (NatMap.find_or msg.(a) QMap.empty msgs)) (Some (destructMsg msg)).

Definition msg_in msg mem := msg_in_ msg mem.(globalMem).

Lemma msg_in_find_message :
  forall msg msgs, msg_in_ msg msgs <->
  option_rel Message.eq (find_message msg.(a) msg.(ts_to) msgs) (Some msg).
Proof.
  unfold msg_in_, find_message. intros. destruct (QMap.find _ _) eqn:?; cbn.
  2: reflexivity.
  split; intro.
  - red. destruct msg, p as ((? & ?) & ?), H as ((? & ?) & ?). cbn in *. auto.
  - red in H. unfold RelProd. destruct msg, p as ((? & ?) & ?). cbn in H |- *. tauto.
Qed.

Lemma wf_message_in :
  forall msg mem,
  wf_mem mem ->
  msg_in msg mem ->
  wf_message msg.
Proof.
  intros. destruct H as [_ ?]. specialize (H msg.(a)).
  apply msg_in_find_message in H0.
  destruct H as [? _].
  destruct (find_message _ _ _) eqn:?.
  - cbn in H0. apply find_message_spec in Heqo as (? & ? & ?).
    apply H in H3. red.
    split. rewrite <- H0. apply H3.
    split. rewrite <- H0 at 1. apply H3.
    rewrite <- H0. apply H3.
  - destruct H0.
Qed.

Lemma find_message_msg_in :
  forall a to msg msgs,
  wf_mem_ msgs ->
  find_message a to msgs = Some msg ->
  msg_in_ msg msgs.
Proof.
  intros. apply msg_in_find_message.
  apply find_message_spec in H0 as ?.
  destruct H1 as (-> & -> & _).
  now rewrite H0.
Qed.

Lemma wf_mem_fence :
  forall o mem tid, wf_mem mem -> wf_mem (mem_fence o mem tid).
Proof.
  intros.
  split; [| apply H]. intros.
  destruct H as [? _].
  destruct (Nat.eq_dec tid tid0).
  2: { rewrite thread_state_mem_fence_neq; auto. } subst.
  unfold mem_fence, thread_state. cbn.
  rewrite NatMapFacts.find_or_add_eq_o. cbn.
  split; [intros; split |]; cbn.
  - destruct (is_release o) eqn:?. 2: apply H.
    unfold NatMap.find_or. rewrite NatMapFacts.map_find.
    destruct (NatMap.find a _) eqn:?; [| reflexivity].
    destruct o; cbn; try discriminate.
    + etransitivity; apply H.
    + apply le_view_merge_views_r. left.
      etransitivity. 2: apply H. apply H.
    + apply le_view_merge_views_r. left.
      apply le_view_merge_views_r. left.
      etransitivity; apply H.
  - destruct o; cbn; try apply H.
    + apply le_view_merge_views_r. left. apply H.
    + unfold NatMap.find_or. rewrite NatMapFacts.map_find.
      destruct (NatMap.find a _) eqn:?; [reflexivity |].
      cbn. etransitivity; apply H.
    + unfold NatMap.find_or. rewrite NatMapFacts.map_find.
      destruct (NatMap.find a _) eqn:?; [reflexivity |].
      cbn. apply le_view_merge_views_r. left.
      etransitivity; apply H.
    + unfold NatMap.find_or. rewrite NatMapFacts.map_find.
      destruct (NatMap.find a _) eqn:?; [reflexivity |].
      cbn. apply le_view_merge_views_r. left.
      apply le_view_merge_views_r. left.
      etransitivity; apply H.
  - destruct o; cbn; try apply H.
    + apply le_view_merge_views_l; auto. apply H.
    + apply le_view_merge_views_l; auto. apply H.
    + apply le_view_merge_views_l.
      * apply le_view_merge_views_r. left.
        apply le_view_merge_views_l; auto. apply H.
      * apply le_view_merge_views_r. now right.
   Unshelve. all: apply O.
Qed.

Lemma wf_do_mem_read :
  forall o mem tid a date,
  wf_mem mem ->
  (NatMap.find_or a 0 (thread_view mem tid) <= date)%Q ->
  wf_mem (fst (fst (do_mem_read o mem tid a date))).
Proof.
  intros. red.
  split; [| apply H]. intros.
  destruct H as [? _].
  destruct (Nat.eq_dec tid tid0).
  2: { unfold thread_state. cbn. rewrite NatMapFacts.find_or_add_neq_o; auto. apply H. } subst.
  unfold thread_state. cbn.
  rewrite NatMapFacts.find_or_add_eq_o.
  split; [intros; split |]; cbn.
  - apply H.
  - destruct (is_acquire o) eqn:?.
    2: {
      destruct (is_sc o) eqn:?; [destruct o; discriminate |].
      rewrite <- add_le_view; auto. apply H.
    }
    destruct o; cbn; try discriminate.
    + apply le_view_merge_views_r. left.
      rewrite <- add_le_view; auto. apply H.
    + apply le_view_merge_views_r. left.
      rewrite <- add_le_view; auto. apply H.
    + apply le_view_merge_views_r. left.
      apply le_view_merge_views_r. left.
      rewrite <- add_le_view; auto. apply H.
  - destruct (is_acquire o) eqn:?.
    2: {
      destruct (is_sc o) eqn:?; [destruct o; discriminate |].
      apply le_view_add. apply Qle_refl. apply H.
    }
    destruct (is_sc o) eqn:?.
    + apply le_view_merge_views_l.
      2: {
        apply le_view_merge_views_r. right.
        apply le_view_merge_views_r. now right.
      }
      apply le_view_merge_views_r. left.
      apply le_view_merge_views_l; apply le_view_merge_views_r; [left | now right].
      apply le_view_add. apply Qle_refl. apply H.
    + apply le_view_merge_views_l; apply le_view_merge_views_r; [left | now right].
      apply le_view_add. apply Qle_refl. apply H.
Qed.

Lemma wf_mem_read :
  forall o mem tid a date mem' v val,
  wf_mem mem ->
  mem_read o mem tid a date = inr (mem', v, val) ->
  wf_mem mem'.
Proof.
  intros.
  unfold mem_read in H0.
  destruct (negb _) eqn:?; [discriminate |].
  destruct (andb _ _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb. apply Qle_bool_iff in Heqb.
  cbn in H0. inv H0.
  apply wf_do_mem_read; auto.
Qed.

Lemma wf_add_message :
  forall mem newmsg,
  wf_mem mem ->
  wf_message newmsg ->
  (newmsg.(ts_to) <= value_or (option_map ts_from (find_msg_gt newmsg.(a) newmsg.(ts_from) mem.(globalMem))) newmsg.(ts_to))%Q ->
  forall to msg,
    find_message newmsg.(a) to mem.(globalMem) = Some msg ->
    (to <= newmsg.(ts_from) \/ newmsg.(ts_to) <= msg.(ts_from))%Q.
Proof.
  intros.
  destruct (Qlt_le_dec newmsg.(ts_from) to); [right | now left].
  destruct (find_msg_gt _ _ _) as [msg_gt |] eqn:?.
  2: {
    eapply find_msg_gt_None_find_message in Heqo. 2: apply q.
    now rewrite H2 in Heqo.
  }
  apply find_msg_gt_find_message in Heqo as ?. destruct H3 as (? & ? & ?).
  destruct (Qlt_le_dec to (ts_to msg_gt)).
  - apply H5 in q; auto. now rewrite H2 in q.
  - cbn in H1. etransitivity. apply H1.
    apply Qle_lt_or_eq in q0 as [].
    + eapply wf_mem_sorted in H2. 4: apply H3. 3: apply H6. 2: apply H.
      etransitivity. 2: apply H2.
      apply find_message_msg_in in H3. 2: apply H. apply wf_message_in in H3; auto.
      apply Qlt_le_weak. apply H3.
    + apply Qle_lteq. right.
      assert (option_rel Message.eq (Some msg) (Some msg_gt)).
      { now rewrite <- H2, <- H3, H6. }
      cbn in H7. now rewrite H7.
Qed.

Lemma wf_do_mem_write :
  forall o mem tid msg,
  wf_mem mem ->
  (NatMap.find_or msg.(a) 0 (thread_view mem tid) <= ts_from msg)%Q ->
  wf_message msg ->
  (msg.(ts_to) <= value_or (option_map ts_from (find_msg_gt msg.(a) msg.(ts_from) mem.(globalMem))) msg.(ts_to))%Q ->
  wf_mem (do_mem_write o mem tid msg).
Proof.
  intros * WF **. split.
  - intros.
    destruct WF as [WF _].
    destruct (Nat.eq_dec tid tid0).
    2: { unfold thread_state. cbn. rewrite NatMapFacts.find_or_add_neq_o; auto. apply WF. } subst.
    unfold thread_state. cbn.
    rewrite NatMapFacts.find_or_add_eq_o.
    split; [intros; split |]; cbn.
    + apply WF.
    + destruct (is_sc o) eqn:?.
      * apply le_view_merge_views_r. left.
        rewrite <- add_le_view; [apply WF |].
        apply Qle_trans with (y := msg.(ts_from)).
        apply H.
        apply Qlt_le_weak. apply H0.
      * rewrite <- add_le_view; [apply WF |].
        apply Qle_trans with (y := msg.(ts_from)).
        apply H.
        apply Qlt_le_weak. apply H0.
    + destruct (is_sc o) eqn:?.
      * apply le_view_merge_views_l; apply le_view_merge_views_r.
        --left. apply le_view_add. apply Qle_refl. apply WF.
        --right. apply le_view_merge_views_r. now right.
      * apply le_view_add. apply Qle_refl. apply WF.
  - split; intros.
    + cbn in H2. unfold add_message in H2. cbn in H2.
      destruct (Nat.eq_dec a (Message.a msg)) as [-> |].
      2: { rewrite NatMapFacts.find_or_add_neq_o in H2; auto. eapply WF. apply H2. }
      rewrite NatMapFacts.find_or_add_eq_o in H2; auto.
      destruct (Qeq_dec (ts_to msg) ts).
      2: { rewrite QMapFacts.add_neq_o in H2; auto. eapply WF. apply H2. }
      rewrite QMapFacts.add_eq_o in H2; auto. inv H2.
      cbn. repeat split; try apply H0; cbn.
      { rewrite <- q. apply H0. }
      destruct (is_not_atomic o); auto.
      apply le_view_add_r.
      { unfold NatMap.find_or. rewrite NatMap.empty_spec. cbn.
        etransitivity. apply (proj1 H0). apply Qlt_le_weak. apply H0. }
      destruct (is_release o). 2: apply WF.
      destruct (is_sc o).
      * apply le_view_merge_views_r. left.
        apply le_view_add_r. unfold NatMap.find_or. rewrite NatMap.empty_spec. cbn.
        etransitivity. apply (proj1 H0). apply Qlt_le_weak. apply H0.
        etransitivity; apply WF.
      * apply le_view_add_r. unfold NatMap.find_or. rewrite NatMap.empty_spec. cbn.
        etransitivity. apply (proj1 H0). apply Qlt_le_weak. apply H0.
        etransitivity; apply WF.
    + cbn in H3, H4. unfold add_message in H3, H4. cbn in H3, H4.
      destruct (Nat.eq_dec a (Message.a msg)) as [-> |].
      2: { rewrite NatMapFacts.find_or_add_neq_o in H3, H4; auto. eapply WF; eauto. }
      rewrite NatMapFacts.find_or_add_eq_o in H3, H4; auto.
      unfold destructMsg in H3, H4. cbn -[QMap.find] in H3, H4.
      destruct (Qeq_dec (ts_to msg) ts), (Qeq_dec (ts_to msg) ts').
      1: { rewrite <- q, <- q0 in H2. now apply Qlt_irrefl in H2. }
      3: { rewrite QMapFacts.add_neq_o in H3, H4; auto. eapply WF; eauto. }
      * rewrite QMapFacts.add_eq_o in H3; auto. inv H3.
        rewrite QMapFacts.add_neq_o in H4; auto.
        rewrite <- q in H2 |- *. clear ts q.
        apply find_find_message in H4.
        eapply wf_add_message in H1; eauto.
        destruct msg' as ((? & ?) & ?).
        destruct H1; auto.
        exfalso. eapply Qlt_irrefl. etransitivity. apply H2.
        eapply Qle_lt_trans. apply H1. apply H0.
      * rewrite QMapFacts.add_eq_o in H4; auto. inv H4. cbn.
        rewrite QMapFacts.add_neq_o in H3; auto.
        rewrite <- q in H2. clear ts' q.
        apply WF in H3 as ?.
        apply find_find_message in H3.
        eapply wf_add_message in H1; eauto.
        destruct H1; auto.
        destruct H4 as (_ & ? & _). destruct msg0 as ((? & ?) & ?). cbn in *.
        exfalso. eapply Qlt_irrefl. etransitivity. apply H4.
        eapply Qlt_le_trans. apply H2. apply H1.
  Unshelve. all: apply O.
Qed.

Lemma wf_mem_write :
  forall o mem tid msg mem',
  wf_mem mem ->
  wf_message msg ->
  mem_write o mem tid msg = inr mem' ->
  wf_mem mem'.
Proof.
  intros.
  unfold mem_write in H1. destruct (negb _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb. rewrite Qle_bool_iff in Heqb.
  destruct (negb _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb0. apply Qle_bool_iff in Heqb0. cbn in Heqb0.
  cbn in H1. inv H1.
  apply wf_do_mem_write; auto.
Qed.

Lemma last_msg_spec :
  forall addr msg mem, msg_in msg mem ->
  msg.(a) = addr ->
  (msg.(ts_to) <= (value_or (last_msg addr mem.(globalMem)) empty_msg).(ts_to))%Q.
Proof.
  intros. subst.
  unfold last_msg. do 2 red in H.
  destruct (QMapFacts.O.max_elt _) eqn:?; cbn.
  - destruct p as (? & (? & ?) & ?). cbn. apply QMapFacts.O.max_elt_Above in Heqo.
    unfold QMapFacts.O.Above in Heqo. specialize (Heqo msg.(ts_to)).
    destruct (Qeq_dec (ts_to msg) k).
    + rewrite q. apply Qle_refl.
    + apply Qle_lteq. left. apply Heqo. apply QMapFacts.remove_in_iff. split.
      { intro. apply n. now apply Qeq_sym. }
      apply QMapFacts.in_find. intro. now rewrite H0 in H.
  - apply QMapFacts.O.max_elt_Empty in Heqo. apply QMapFacts.is_empty_iff in Heqo.
    rewrite QMap.is_empty_spec in Heqo. now rewrite Heqo in H.
Qed.

Definition max_view mem := max_view_ mem.(globalMem).

Lemma max_view_mem_fence :
  forall ps o tid, max_view (mem_fence o ps tid) = max_view ps.
Proof.
  reflexivity.
Qed.

Lemma max_view_last_msg : forall msgs addr,
  NatMap.find_or addr 0%Q (max_view_ msgs) = (value_or (last_msg addr msgs) empty_msg).(ts_to).
Proof.
  intros. unfold max_view_, last_msg.
  rewrite NatMapFacts.map_find_or' with (d := QMap.empty).
  2: reflexivity.
  cbn. destruct (QMapFacts.O.max_elt _) eqn:?.
  - now destruct p as (? & ((? & ?) & ?)).
  - reflexivity.
Qed.

Lemma last_msg_max_view : forall msgs a,
  last_msg a msgs = find_message a (NatMap.find_or a 0%Q (max_view_ msgs)) msgs.
Proof.
  intros. unfold last_msg, max_view_.
  cbn. rewrite NatMapFacts.map_find_or' with (d := QMap.empty).
  2: reflexivity.
  destruct (QMapFacts.O.max_elt _) eqn:?.
  - destruct p. cbn.
    apply QMapFacts.O.max_elt_MapsTo in Heqo. apply QMapFacts.find_mapsto_iff in Heqo.
    unfold find_message. now rewrite Heqo.
  - cbn. apply QMapFacts.O.max_elt_Empty in Heqo. apply QMapFacts.is_empty_iff in Heqo.
    rewrite QMap.is_empty_spec in Heqo.
    unfold find_message. now rewrite Heqo.
Qed.

(* Relation between SC and PS states *)

Definition Lmem (sc : SC.SCMem) (ps : PSMem) :=
  wf_mem ps /\
  (forall a, option_map val (last_msg a ps.(globalMem)) = SC.mem_read sc a) /\
  (le_view (seq_view ps) (max_view ps))%Q /\
  (forall msg, msg_in msg ps -> le_view (msg.(view)) (max_view ps)) /\
  (forall tid, le_view (thread_acq_view ps tid) (max_view ps)).

Definition Lmem' : rel (SC.SCMem * unit) (PSMem * unit) :=
  fun a b => Lmem (fst a) (fst b).

Lemma Lmem_fence : forall o sc ps tid,
  Lmem sc ps ->
  Lmem sc (mem_fence o ps tid).
Proof.
  intros * (WF & Hval & Hseq & Hview & Hacq). red. cbn.
  setoid_rewrite Hval.
  split; [now apply wf_mem_fence |].
  split; [reflexivity |].
  rewrite max_view_mem_fence.
  split; [| split].
  - intros. destruct (is_sc o) eqn:?.
    2: { apply Hseq. }
    destruct o; try discriminate. cbn.
    apply le_view_merge_views_l.
    rewrite merge_views_leq. apply Hacq. apply WF.
    apply Hseq.
  - intros. apply Hview. apply H.
  - intros. cbn. destruct (Nat.eq_dec tid tid0).
    2: {
      unfold thread_acq_view. cbn. rewrite thread_state_mem_fence_neq; auto.
      apply Hacq.
    }
    subst. unfold thread_view, thread_state, mem_fence.
    unfold thread_acq_view, thread_state. cbn.
    rewrite NatMapFacts.find_or_add_eq_o; auto. cbn.
    destruct (is_sc o) eqn:?.
    2: { apply Hacq. }
    apply le_view_merge_views_l.
    + apply Hacq.
    + apply Hseq.
Qed.

Lemma find_message_in : forall addr ts mem msg,
  find_message addr ts mem.(globalMem) = Some msg ->
  msg_in msg mem /\ msg.(a) = addr.
Proof.
  intros. unfold msg_in, msg_in_. unfold find_message in H. cbn in H.
  destruct (QMap.find ts _) eqn:?.
  - destruct p as ((? & ?) & ?).
    inv H. cbn -[RelProd]. rewrite Heqo. split; reflexivity.
  - discriminate.
Qed.

Lemma find_msg_gt_in : forall addr ts mem msg,
  find_msg_gt addr ts mem.(globalMem) = Some msg ->
  msg_in msg mem /\ msg.(a) = addr.
Proof.
  intros.
  apply find_msg_gt_find_message in H as [].
  now apply find_message_in in H.
Qed.

Lemma Lmem_max_view_pos : forall sc mem,
  Lmem sc mem ->
  le_view NatMap.empty (max_view_ mem.(globalMem)).
Proof.
  intros * (WF & ?). etransitivity. 2: apply H. etransitivity. 2: apply WF.
  etransitivity. 2: apply WF. apply WF.
  Unshelve. all: exact O.
Qed.

Lemma Lmem_read :
  forall o sc mem tid a mem' v val,
  Lmem sc mem ->
  mem_read o mem tid a (NatMap.find_or a 0%Q (max_view mem)) = inr (mem', v, val) ->
  Lmem sc (fst (fst (do_mem_read o mem tid a (NatMap.find_or a 0%Q (max_view mem))))).
Proof.
  intros * (WF & Hval & Hseq & Hview & Hacq) ?.
  assert (Hview' : forall a ts, le_view
    (view (value_or (find_message a ts (globalMem mem)) empty_msg))
    (max_view mem)).
  {
    intros. destruct (find_message _ _ _) eqn:?.
    - apply Hview. now apply find_message_in in Heqo0.
    - cbn. now eapply Lmem_max_view_pos.
  }
  unfold mem_read in H. destruct (negb _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb. apply Qle_bool_iff in Heqb.
  destruct (andb _ _) eqn:?; [discriminate |].
  apply andb_false_iff in Heqb0.
  rewrite negb_false_iff, Qeq_bool_iff in Heqb0.
  inv H.
  split. { eapply wf_do_mem_read; auto. }
  split. {
    intros. cbn. now rewrite Hval.
  }
  split. {
    intros. unfold max_view at 2. cbn.
    destruct (is_sc o) eqn:?.
    2: { apply Hseq. }
    destruct o; try discriminate.
    apply le_view_merge_views_l; [apply le_view_merge_views_l |].
    - apply le_view_add_l. apply Qle_refl.
      etransitivity. apply WF. apply Hacq.
    - apply Hview'.
    - apply Hseq.
  }
  split. {
    cbn. intros. apply Hview. apply H.
  }
  intros. unfold max_view at 2. cbn. destruct (Nat.eq_dec tid tid0).
  2: {
    unfold thread_acq_view, thread_state. cbn.
    rewrite NatMapFacts.find_or_add_neq_o; auto.
    apply Hacq.
  }
  subst. unfold thread_acq_view, thread_state. cbn.
  rewrite NatMapFacts.find_or_add_eq_o. cbn.
  destruct (is_sc o) eqn:?.
  2: {
    destruct (is_acquire o) eqn:?.
    - apply le_view_merge_views_l.
      + apply le_view_add_l. reflexivity. apply Hacq.
      + apply Hview'.
    - apply le_view_add_l. reflexivity. apply Hacq.
  }
  destruct o; try discriminate.
  repeat apply le_view_merge_views_l.
  - apply le_view_add_l. apply Qle_refl. apply Hacq.
  - apply Hview'.
  - apply le_view_add_l.
    apply Qle_refl. etransitivity. apply WF. apply Hacq.
  - apply Hview'.
  - apply Hseq.
Qed.

Lemma max_view_add_message : forall msgs msg,
  (NatMap.find_or msg.(a) 0%Q (max_view_ msgs) < msg.(ts_to))%Q ->
  NatMap.Equal1 Qeq (max_view_ (add_message msg msgs))
    (NatMap.add msg.(a) msg.(ts_to) (max_view_ msgs)).
Proof.
  intros ** ?.
  unfold max_view_ at 1. subst.
  unfold add_message. rewrite <- NatMapFacts.map_add.
  destruct (Nat.eq_dec y (msg.(a))).
  - rewrite !NatMapFacts.add_eq_o; auto. cbn -[QMapFacts.O.max_elt].
    destruct (QMap.is_empty (NatMap.find_or (a msg) QMap.empty msgs)) eqn:?.
    { rewrite QMapFacts.max_elt_add_empty; auto. }
    pose (m := QMapFacts.O.max_elt (NatMap.find_or (a msg) QMap.empty msgs)).
    rewrite QMapFacts.max_elt_add_gt with (k := fst (value_or m (0%Q, empty_message))) (v := snd (value_or m (0%Q, empty_message))).
    1: reflexivity.
    + destruct (QMapFacts.O.max_elt _) eqn:?. now destruct p.
      apply QMapFacts.O.max_elt_Empty in Heqo.
      apply QMapFacts.is_empty_iff in Heqo.
      now rewrite Heqo in Heqb.
    + subst m.
      unfold max_view_ in H.
      rewrite NatMapFacts.map_find_or' with (d := QMap.empty) in H.
      2: reflexivity.
      apply H.
  - rewrite !NatMapFacts.add_neq_o; auto.
Qed.

Lemma last_msg_add_message : forall msgs msg addr,
  msg.(a) = addr ->
  (NatMap.find_or msg.(a) 0%Q (max_view_ msgs) < msg.(ts_to))%Q ->
  option_rel Message.eq (last_msg addr (add_message msg msgs)) (Some msg).
Proof.
  intros * <- ?. rewrite last_msg_max_view. rewrite max_view_add_message; auto.
  subst. rewrite NatMapFacts.find_or_add_eq_o.
  rewrite find_message_add_message_eq; auto.
Qed.

Lemma last_msg_add_message_neq : forall msgs msg addr,
  wf_message msg ->
  msg.(a) <> addr \/ (msg.(ts_to) < NatMap.find_or msg.(a) 0 (max_view_ msgs))%Q ->
  option_rel Message.eq (last_msg addr (add_message msg msgs)) (last_msg addr msgs).
Proof.
  intros * WF **.
  destruct (Nat.eq_dec msg.(a) addr).
  - unfold last_msg, add_message. cbn.
    subst.
    rewrite NatMapFacts.find_or_add_eq_o; auto.
    destruct H; [easy |].
    destruct (QMapFacts.O.max_elt (NatMap.find_or _ _ _)) eqn:?.
    + destruct p as (? & (? & ?) & ?). eapply QMapFacts.max_elt_add_lt in Heqo.
      destruct (QMapFacts.O.max_elt (QMap.add _ _ _)) eqn:?.
      2: destruct Heqo.
      destruct p as (? & (? & ?) & ?).
      inv Heqo. cbn in H0, H1. inv H1. rewrite Heqo0. cbn. red; auto.
      rewrite max_view_last_msg in H. unfold last_msg in H. rewrite Heqo in H.
      cbn in H. apply H.
    + destruct (QMapFacts.O.max_elt (QMap.add _ _ _)) eqn:?.
      2: reflexivity.
      destruct p as (? & (? & ?) & ?).
      apply QMapFacts.O.max_elt_Empty in Heqo as ?. apply QMapFacts.is_empty_iff in H0.
      eapply QMapFacts.max_elt_add_empty in H0.
      rewrite Heqo0 in H0. cbn in H0. inv H0. inv H2.
      cbn in H1.
      rewrite max_view_last_msg in H. unfold last_msg in H. rewrite Heqo in H.
      cbn in H. apply Qlt_not_le in H. apply H.
      etransitivity. apply (proj1 WF). apply Qlt_le_weak. apply WF.
  - unfold last_msg, add_message. cbn.
    rewrite NatMapFacts.find_or_add_neq_o; auto.
Qed.

Lemma msg_in_add_message : forall msgs msg msg',
  msg_in_ msg (add_message msg' msgs) ->
  Message.eq msg msg' \/ msg_in_ msg msgs.
Proof.
  intros. rewrite msg_in_find_message in H |- *.
  destruct (Nat.eq_dec msg.(a) msg'.(a)).
  2: { right. rewrite find_message_add_message_neq in H; auto. }
  destruct (Qeq_dec (ts_to msg) (ts_to msg')).
  - left. symmetry in H. rewrite find_message_add_message_eq in H; auto.
  - right. rewrite find_message_add_message_neq in H; auto.
Qed.

Lemma Lmem_write : forall o sc mem tid mem' addr v,
  Lmem sc mem ->
  mem_write o mem tid (mkMsg addr v (fst (latest mem addr (PSFulfill v))) (snd (latest mem addr (PSFulfill v))) NatMap.empty) = inr mem' ->
  Lmem (SC.mem_write sc addr v) mem'.
Proof.
  intros * HLmem ?.
  pose proof (Hempty := Lmem_max_view_pos _ _ HLmem).
  destruct HLmem as (WF & Hval & Hseq & Hview & Hacq).
  unfold mem_write in H.
  destruct (negb _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb. rewrite Qle_bool_iff in Heqb.
  destruct (negb _) eqn:?; [discriminate |].
  apply negb_false_iff in Heqb0. apply Qle_bool_iff in Heqb0.
  cbn in H. inv H.
  split. {
    apply wf_do_mem_write; auto.
    repeat split; cbn; auto.
    - rewrite <- max_view_last_msg. apply Hempty.
    - red. cbn. lia.
  }
  split. {
    intros. cbn.
    destruct (Nat.eq_dec a addr).
    2: {
      setoid_rewrite last_msg_add_message_neq; auto. now rewrite SC.mem_read_write_neq.
      cbn. red. cbn. repeat split.
      - rewrite <- max_view_last_msg. apply Hempty.
      - red. cbn. lia.
      - destruct (is_not_atomic o) eqn:?. 1: reflexivity.
        apply le_view_add_r_gen.
        + rewrite Hempty, <- max_view_last_msg. red. cbn. lia.
        + intros.
          destruct (is_release o) eqn:?.
          2: { apply WF. }
          destruct (is_sc o) eqn:?.
          * rewrite find_or_merge_views.
            apply Q.max_le_iff. left.
            rewrite NatMapFacts.find_or_add_neq_o; auto.
            etransitivity. 2: apply WF. apply WF.
          * rewrite NatMapFacts.find_or_add_neq_o; auto.
            etransitivity. 2: apply WF. apply WF.
    }
    subst. rewrite last_msg_add_message; auto.
    { cbn. now rewrite SC.mem_read_write_eq. }
    cbn. rewrite max_view_last_msg. red. cbn. lia.
  }
  split. {
    intros. cbn.
    unfold max_view. cbn. rewrite max_view_add_message; cbn.
    2: { rewrite max_view_last_msg. red. cbn. lia. }
    destruct (is_sc o) eqn:?.
    - apply le_view_merge_views_l.
      apply le_view_add. { apply Qle_refl. }
      + etransitivity. apply WF. apply Hacq.
      + rewrite <- add_le_view. { apply Hseq. }
        rewrite max_view_last_msg. red. cbn. lia.
    - rewrite <- add_le_view. { apply Hseq. }
      rewrite <- max_view_last_msg. red. cbn. lia.
  }
  split. {
    unfold msg_in, max_view. cbn. intros.
    apply msg_in_add_message in H.
    rewrite max_view_add_message; cbn.
    2: { rewrite max_view_last_msg. red. cbn. lia. }
    apply le_view_add_r_gen.
    - destruct H.
      + rewrite H. cbn.
        destruct (is_not_atomic o) eqn:?. 1: {
          rewrite <- max_view_last_msg. etransitivity.
          apply Hempty. red. cbn. lia.
        }
        rewrite NatMapFacts.find_or_add_eq_o; auto.
      + rewrite <- max_view_last_msg. rewrite Hview; auto. unfold max_view. red. cbn. lia.
    - intros. destruct H.
      2: { rewrite Hview; auto. }
      rewrite H. cbn.
      destruct (is_not_atomic o) eqn:?. 1: { apply Hempty. }
      rewrite NatMapFacts.find_or_add_neq_o; auto.
      rewrite <- max_view_last_msg.
      destruct (is_release o) eqn:?. 1: destruct (is_sc o) eqn:?.
      + rewrite find_or_merge_views. apply Q.max_lub.
        * rewrite NatMapFacts.find_or_add_neq_o; auto.
          etransitivity. apply WF. apply Hacq.
        * apply Hseq.
      + rewrite NatMapFacts.find_or_add_neq_o; auto.
        etransitivity. apply WF. apply Hacq.
      + etransitivity. apply WF. etransitivity. apply WF. apply Hacq.
  }
  intros. destruct (Nat.eq_dec tid tid0).
  2: {
    unfold thread_acq_view, thread_state. cbn.
    rewrite NatMapFacts.find_or_add_neq_o; auto.
    unfold max_view. cbn. rewrite max_view_add_message; cbn.
    - rewrite <- add_le_view. apply Hacq. rewrite max_view_last_msg. red. cbn. lia.
    - rewrite max_view_last_msg. red. cbn. lia.
  }
  subst. cbn. unfold thread_acq_view, thread_state, max_view. cbn.
  rewrite NatMapFacts.find_or_add_eq_o. cbn.
  rewrite max_view_add_message.
  2: { cbn. rewrite max_view_last_msg. red. cbn. lia. }
  cbn. destruct (is_sc o) eqn:?.
  - repeat apply le_view_merge_views_l.
    + apply le_view_add. apply Qle_refl.
      apply Hacq.
    + apply le_view_add. apply Qle_refl.
      etransitivity. apply WF. apply Hacq.
    + rewrite <- add_le_view. apply Hseq.
      rewrite max_view_last_msg. red. cbn. lia.
  - apply le_view_add. apply Qle_refl. apply Hacq.
  Unshelve. all: apply O.
Qed.

Lemma mem_read_latest :
  forall date sc mem a ord tid,
  Lmem sc mem ->
  date = snd (latest mem a PSRead) ->
  mem_read ord mem tid a date = inr (do_mem_read ord mem tid a date).
Proof.
  intros.
  unfold mem_read. destruct (negb _) eqn:?.
  - apply negb_true_iff in Heqb.
    apply not_true_iff_false in Heqb.
    rewrite Qle_bool_iff in Heqb. subst.
    unfold latest in Heqb. exfalso. apply Heqb. cbn.
    rewrite <- max_view_last_msg.
    etransitivity. apply H. apply H.
  - subst. unfold latest at 1. cbn.
    rewrite <- max_view_last_msg, <- last_msg_max_view.
    destruct (last_msg _ _) eqn:?; cbn. 1: reflexivity.
    unfold latest at 1. cbn. rewrite Heqo. cbn. reflexivity.
Qed.

Lemma mem_write_latest :
  forall sc mem v ord tid msg,
  Lmem sc mem ->
  msg.(ts_from) = fst (latest mem msg.(a) (PSFulfill v)) ->
  msg.(ts_to) = snd (latest mem msg.(a) (PSFulfill v)) ->
  mem_write ord mem tid msg = inr (do_mem_write ord mem tid msg).
Proof.
  intros.
  unfold mem_write.
  destruct (negb _) eqn:?.
  - apply negb_true_iff in Heqb.
    apply not_true_iff_false in Heqb.
    rewrite Qle_bool_iff in Heqb.
    rewrite H0 in Heqb. unfold latest in Heqb. cbn in Heqb.
    exfalso. apply Heqb. rewrite <- max_view_last_msg.
    etransitivity. apply H. apply H.
  - apply negb_false_iff in Heqb. apply Qle_bool_iff in Heqb.
    destruct (negb (Qle_bool msg.(ts_to) _)) eqn:?; try reflexivity.
    apply negb_true_iff in Heqb0.
    apply not_true_iff_false in Heqb0.
    rewrite Qle_bool_iff in Heqb0.
    rewrite H0, H1 in Heqb0. unfold latest in Heqb0. cbn in Heqb0.
    exfalso. apply Heqb0. clear Heqb0.
    destruct (find_msg_gt _ _ _) eqn:?. 2: reflexivity.
    cbn. apply find_msg_gt_in in Heqo as ?.
    apply find_msg_gt_find_message in Heqo as ?. destruct H3 as (_ & ? & _).
    exfalso. pose proof (last_msg_spec msg.(a) m mem (proj1 H2) (proj2 H2)).
    apply Qlt_not_le in H3. now apply H3 in H4.
Qed.

Lemma Lmem_read_na {E C D} `{PickC -< C} `{PickC -< D} : forall sc ps tid a,
  Lmem sc ps ->
  (freeze (SC.mem_read sc a) : ctree E C value) ≲ (freeze (mem_read_na ps tid a) : ctree E D value).
Proof.
  intros. rewrite <- (proj1 (proj2 H1)). unfold mem_read_na.
  destruct (last_msg a (globalMem ps)) eqn:?; cbn.
  - destruct (Qeq_bool _ _) eqn:?; cbn.
    + now apply ssim_ret.
    + apply ssim_br_r with (x := val m). now apply ssim_ret.
  - apply ssim_br_id. intros. now apply ssim_ret.
Qed.

Theorem ss_sc_ps {E C} : forall (t : ctree (ThreadAnnotE MemoryE +' E) C unit)
  sc mem,
  Lmem sc mem ->
  (SC.interp_mem _ t sc)
    (≲ lift_val_rel Lmem')
    (@interp_mem E E C (PSMemC +' SchedC +' PickC +' PSExceptC +' DebugLogC +' C) _ _ _ _ _ _ _ _ t mem).
Proof.
  intros.
  eapply ssim_interp_state_h with (Rs := Lmem).
  3: trivial.
  { split. constructor; etrans. intros. constructor. assumption. }
  intros. eapply weq_ssim. eapply update_val_rel_update_val_rel.
  destruct e; [destruct t0 |].
  - destruct e.
    + (* Read *)
      cbn.
      destruct (is_not_atomic o) eqn:?. {
       eapply ssim_clo_bind_gen with (R0 := eq). 2: apply Lmem_read_na; auto.
        apply is_update_val_rel_update_val_rel_eq.
        intros ?? <-. apply step_ssim_step; [| constructor; etrans]. apply ssim_ret. now constructor.
      }
      rewrite bind_branch. apply ssim_br_r with (x := latest st' k PSRead).
      destruct (latest st' k PSRead) eqn:?. unfold latest in Heqp. inv Heqp.
      erewrite mem_read_latest. 2: eassumption. 2: reflexivity.
      cbn. rewrite bind_ret_l. cbn -[do_mem_read].
      eapply Lmem_read in H0. 2: {
        erewrite mem_read_latest. reflexivity. apply H0.
        unfold latest. rewrite <- max_view_last_msg. reflexivity.
      }
      rewrite <- max_view_last_msg.
      eapply ssim_clo_bind_gen with (R0 := eq).
      apply is_update_val_rel_update_val_rel_eq.
      { cbn. rewrite <- last_msg_max_view. rewrite (proj1 (proj2 H0)).
        unfold freeze. destruct (SC.mem_read st k).
        - destruct (is_racy _). eapply ssim_br_r. now apply ssim_ret.
          now apply ssim_ret.
        - destruct (is_racy _); apply ssim_br_id; intros; now apply ssim_ret.
      }
      intros ?? <-. apply step_ssim_step; [| constructor; etrans].
      apply ssim_ret. constructor. split; auto.
      apply H0.
    + (* Write *)
      cbn. rewrite bind_branch. apply ssim_br_r with (x := latest st' k (PSFulfill v)).
      destruct (latest st' k (PSFulfill v)) eqn:?. unfold latest in Heqp. inv Heqp.
      erewrite mem_write_latest. 2: eassumption. 2,3: reflexivity.
      cbn. rewrite bind_ret_l.
      apply step_ssim_step; [| constructor; etrans].
      apply ssim_ret. constructor. split; auto.
      eapply Lmem_write. 1: apply H0.
      erewrite mem_write_latest; try reflexivity. apply H0.
    + (* ReadWrite *)
      cbn.
      rewrite bind_branch. apply ssim_br_r with (x := latest st' k PSFulfillUpdate).
      destruct (latest _ _ _) eqn:?. unfold latest in Heqp. inv Heqp.
      erewrite mem_read_latest. 2: eassumption. 2: reflexivity.
      cbn. rewrite bind_ret_l. cbn -[do_mem_read].
      eapply Lmem_read in H0. 2: {
        erewrite mem_read_latest. reflexivity. apply H0.
        unfold latest. rewrite <- max_view_last_msg. reflexivity.
      }
      rewrite <- max_view_last_msg. cbn -[do_mem_read].
      eapply ssim_clo_bind_gen with (R0 := eq).
      apply is_update_val_rel_update_val_rel_eq.
      { cbn. rewrite <- last_msg_max_view. rewrite (proj1 (proj2 H0)).
        rewrite <- (proj1 (proj2 H0)). unfold max_view. cbn.
        destruct (last_msg k (globalMem st')) eqn:?; cbn.
        { destruct (is_racy _); cbn.
          eapply ssim_br_r. now apply ssim_ret. now apply ssim_ret. }
        rewrite max_view_last_msg, Heqo0. cbn. rewrite Tauto.if_same.
        unfold branch. apply ssim_br_id. intros. now apply ssim_ret.
      }
      intros ?? <-. erewrite mem_write_latest. 2: eassumption.
      2: { unfold latest. cbn. now rewrite max_view_last_msg. }
      2: { unfold latest. cbn. now rewrite max_view_last_msg. }
      cbn -[do_mem_read]. rewrite bind_ret_l.
      apply step_ssim_step; [| constructor; etrans].
      apply ssim_ret. constructor. split; auto.
      eapply Lmem_write. apply H0.
      erewrite mem_write_latest; try reflexivity. 2: apply H0.
      unfold latest. cbn -[do_mem_read]. rewrite <- max_view_last_msg. reflexivity.
    + (* Fence *)
      apply step_ssim_step; [| constructor; etrans].
      apply ssim_ret. constructor. split; auto.
      now apply Lmem_fence.
  - cbn. unfold SC.E_trigger, E_trigger. rewrite !bind_trigger. apply ssim_vis_id.
    intros. split; [| now constructor ].
    apply ssim_ret. constructor. auto.
  Unshelve. all: apply nullval.
Qed.
