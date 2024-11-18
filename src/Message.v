From Coq Require Import
     Classes.RelationPairs
     Init.Logic
     Lists.List
     QArith
     QArith.Qminmax
     QArith.QOrderedType
     Strings.String.

From MMaps Require Import MMaps.

From ExtLib Require Import
     Data.String
     Monads.

From ITree Require Import
     Basics.HeterogeneousRelations.

From Mem Require Import Utils Events.

Import ListNotations.
Import MonadNotation.

Open Scope nat_scope.
Open Scope monad_scope.
Open Scope string_scope.
Open Scope list_scope.

Module QMap.
  Module Import M := MMaps.OrdList.Make Q_as_OT.
  Include ExtMMap Q_as_OT M.
End QMap.

Module QMapFacts := ExtMMapFacts Q_as_OT QMap.

Definition date_type := Q.

Definition Q2string q := (nat2string10 (Z.to_nat (Qnum q)) ++ "/" ++ nat2string10 (Pos.to_nat (Qden q)))%string.

(* views *)

Definition view_type := NatMap.t date_type.

Definition view_eq := NatMap.Equal1 Qeq.

Definition le_view v1 v2 :=
  (forall a, NatMap.find_or a 0 v1 <= NatMap.find_or a 0 v2)%Q.

Definition option_Qmax o1 o2 :=
  Some (Qmax (value_or o1 0%Q) (value_or o2 0%Q)).

Definition merge_views :=
  NatMapFacts.map2 option_Qmax.

Definition fold_views v := NatMap.fold (fun _ view1 view2 => merge_views view1 view2) v NatMap.empty.

#[global] Instance Reflexive_le_view : Reflexive le_view.
Proof.
  do 2 red. intros. apply Qle_refl.
Qed.

#[global] Instance Transitive_le_view : Transitive le_view.
Proof.
  unfold le_view. cbn. intros.
  eapply Qle_trans. apply H. apply H0.
Qed.

#[global] Instance le_view_find : forall a,
  Proper (le_view ==> Qle) (NatMap.find_or a 0%Q).
Proof.
  cbn. intros. apply H.
Qed.

Lemma find_or_merge_views :
  forall a v1 v2,
  NatMap.find_or a 0%Q (merge_views v1 v2) =
  Qmax (NatMap.find_or a 0%Q v1) (NatMap.find_or a 0%Q v2).
Proof.
  intros. unfold merge_views.
  destruct (Sumbool.sumbool_or _ _ _ _ (NatMapFacts.In_dec v1 a) (NatMapFacts.In_dec v2 a)).
  - unfold NatMap.find_or at 1. eapply NatMapFacts.map2_1 in o. now rewrite o.
  - destruct a0. apply NatMapFacts.not_in_find in H, H0. unfold NatMap.find_or. rewrite H, H0.
    apply value_or_eq. intros. apply NatMapFacts.in_find_some in H1.
    apply NatMapFacts.map2_2 in H1. apply NatMapFacts.not_in_find in H, H0. tauto.
Qed.

Lemma merge_views_leq :
  forall v1 v2,
  le_view v1 v2 ->
  NatMap.Equal1d Qeq 0%Q (merge_views v1 v2) v2.
Proof.
  intros ** ?. rewrite find_or_merge_views.
  rewrite Q.max_r; auto.
Qed.

Lemma le_view_merge_views_l :
  forall v v1 v2,
  le_view v1 v ->
  le_view v2 v ->
  le_view (merge_views v1 v2) v.
Proof.
  intros ??????. rewrite find_or_merge_views.
  apply Q.max_lub_iff. split; auto.
Qed.

Lemma le_view_merge_views_r :
  forall v v1 v2,
  le_view v v1 \/ le_view v v2 ->
  le_view v (merge_views v1 v2).
Proof.
  intros ?????. rewrite find_or_merge_views.
  apply Q.max_le_iff. destruct H; [left | right]; apply H.
Qed.

Lemma le_view_add_l :
  forall v v' a ts,
  (ts <= NatMap.find_or a 0%Q v')%Q ->
  le_view v v' ->
  le_view (NatMap.add a ts v) v'.
Proof.
  intros ** ?.
  destruct (Nat.eq_dec a a0).
  - subst. rewrite NatMapFacts.find_or_add_eq_o. apply H.
  - rewrite NatMapFacts.find_or_add_neq_o; auto.
Qed.

Lemma le_view_add_r_gen :
  forall v v' a ts,
  (NatMap.find_or a 0%Q v <= ts)%Q ->
  (forall a', a' <> a -> NatMap.find_or a' 0 v <= NatMap.find_or a' 0 v')%Q ->
  le_view v (NatMap.add a ts v').
Proof.
  intros ** a'. destruct (Nat.eq_dec a' a).
  - subst. rewrite NatMapFacts.find_or_add_eq_o; auto.
  - rewrite NatMapFacts.find_or_add_neq_o; auto.
Qed.

Lemma le_view_add_r :
  forall v v' a ts,
  (NatMap.find_or a 0%Q v <= ts)%Q ->
  le_view v v' ->
  le_view v (NatMap.add a ts v').
Proof.
  intros. apply le_view_add_r_gen; auto.
Qed.

Lemma add_le_view :
  forall v a ts,
  (NatMap.find_or a 0%Q v <= ts)%Q ->
  le_view v (NatMap.add a ts v).
Proof.
  intros ** ?.
  destruct (Nat.eq_dec a a0).
  - subst. rewrite NatMapFacts.find_or_add_eq_o. apply H.
  - rewrite NatMapFacts.find_or_add_neq_o; auto. apply Qle_refl.
Qed.

Lemma le_view_add :
  forall v v' a ts ts',
  (ts <= ts')%Q ->
  le_view v v' ->
  le_view (NatMap.add a ts v) (NatMap.add a ts' v').
Proof.
  intros ** ?. destruct (Nat.eq_dec a a0).
  - subst. now rewrite !NatMapFacts.find_or_add_eq_o.
  - rewrite !NatMapFacts.find_or_add_neq_o; auto.
Qed.

(* the second key is ts_to *)
Definition msg_set := NatMap.t (QMap.t (date_type * value * view_type)).
Definition empty_msg_set : msg_set := NatMap.empty.
Definition is_empty_msg_set (m: msg_set) := NatMap.fold (fun _ s b => b && QMap.is_empty s) m true.

Definition msg_set_eq := NatMap.Equal1 (QMap.Equal1 (Qeq * (eq (A := value)) * view_eq))%signature.

Record Message := mkMsg {
  a : addr;
  val : value;
  ts_from : date_type;
  ts_to : date_type;
  view : NatMap.t date_type;
}.

Definition empty_msg := mkMsg O nullval 0%Q 0%Q NatMap.empty.

Definition empty_message : date_type * value * view_type :=
  (0%Q, nullval, NatMap.empty).

#[local] Definition eq m m' :=
  m.(a) = m'.(a) /\ m.(val) = m'.(val) /\
  Qeq m.(ts_from) m'.(ts_from) /\ Qeq m.(ts_to) m'.(ts_to) /\
  view_eq m.(view) m'.(view).

#[global] Instance Reflexive_eq : Reflexive eq.
Proof.
  cbn. red. auto.
Qed.

#[global] Instance Transitive_eq : Transitive eq.
Proof.
  cbn. unfold eq. intros ??? (? & ? & ? & ? & ?) (? & ? & ? & ? & ?).
  split; [| split; [| split; [| split]]]; etransitivity; eassumption.
Qed.

#[global] Instance Symmetric_eq : Symmetric eq.
Proof.
  cbn. unfold eq. intros ?? (? & ? & ? & ? & ?).
  split; auto. split; auto. split. now symmetry.
  split; now symmetry.
Qed.

#[local] Definition eqb (m m' : Message) : bool :=
  Nat.eqb m.(a) m'.(a) && value_eqb m.(val) m'.(val) &&
  Q_as_OT.eqb m.(ts_from) m'.(ts_from) && Q_as_OT.eqb m.(ts_to) m'.(ts_to) &&
  NatMap.equal Q_as_OT.eqb m.(view) m'.(view).

Definition rebuildMsg addr date val :=
  let '(from, val, view) := val in
  mkMsg addr val from date view.

#[global] Instance rebuildMsg_eq : Proper (Logic.eq ==> Qeq ==> (Qeq * Logic.eq * view_eq)%signature ==> Message.eq) rebuildMsg.
Proof.
  cbn. intros. subst. destruct x1 as ((? & ?) & ?), y1 as ((? & ?) & ?). red. cbn in *.
  tauto.
Qed.

Definition destructMsg msg := (msg.(ts_from), msg.(val), msg.(view)).

#[global] Instance msg_val_eq : Proper (Message.eq ==> Logic.eq) val.
Proof.
  cbn. intros. apply H.
Qed.

#[global] Instance msg_ts_from_Qeq : Proper (Message.eq ==> Qeq) ts_from.
Proof.
  cbn. intros. apply H.
Qed.

#[global] Instance msg_ts_to_Qeq : Proper (Message.eq ==> Qeq) ts_to.
Proof.
  cbn. intros. apply H.
Qed.

#[global] Instance msg_view_eq : Proper (Message.eq ==> view_eq) view.
Proof.
  cbn. intros. apply H.
Qed.

#[global] Instance Equal1d_le_view : Proper (NatMap.Equal1d Qeq 0%Q ==> NatMap.Equal1d Qeq 0%Q ==> flip impl) le_view.
Proof.
  cbn. unfold le_view. intros.
  now rewrite H, H0.
Qed.

Definition add_message (msg: Message) (s: msg_set) : msg_set :=
  let msgs := NatMap.find_or msg.(a) QMap.empty s in
  NatMap.add msg.(a) (QMap.add msg.(ts_to) (destructMsg msg) msgs) s
.

Definition find_message (a : addr) (date : date_type) (s: msg_set) : option Message :=
  val <- QMap.find date (NatMap.find_or a QMap.empty s);;
  ret (rebuildMsg a date val)
.

Arguments find_message : simpl never.

#[global] Instance find_message_eq : Proper (Logic.eq ==> Qeq ==> msg_set_eq ==> option_rel Message.eq) find_message.
Proof.
  unfold find_message. cbn. intros. subst. red in H1.
  specialize (H1 y). unfold NatMap.find_or.
  destruct (NatMap.find y x1) eqn:?, (NatMap.find y y1) eqn:?; setoid_rewrite Heqo; setoid_rewrite Heqo0; try now destruct H1.
  pose proof @QMapFacts.find_m. rewrite H0. clear H.
  specialize (H1 y0).
  destruct (QMap.find y0 t) eqn:?, (QMap.find y0 t0) eqn:?; setoid_rewrite Heqo1; setoid_rewrite Heqo2; try now destruct H1.
  cbn. red in H1. rewrite H0, H1. reflexivity.
Qed.

Lemma find_find_message : forall a to msg msgs,
  QMap.find to (NatMap.find_or a QMap.empty msgs) = Some msg ->
  find_message a to msgs = Some (rebuildMsg a to msg).
Proof.
  intros. unfold find_message. now rewrite H.
Qed.

Lemma find_message_spec : forall addr to msg msgs,
  find_message addr to msgs = Some msg ->
  msg.(a) = addr /\ msg.(ts_to) = to /\
  QMap.find to (NatMap.find_or addr QMap.empty msgs) = Some (destructMsg msg).
Proof.
  intros. unfold find_message in H.
  destruct (QMap.find _ _) eqn:?; [| discriminate].
  inversion H. subst. clear H. destruct p as ((? & ?) & ?). auto.
Qed.

Lemma find_message_add_message_eq : forall msgs msg addr ts,
  addr = msg.(a) ->
  (ts == msg.(ts_to))%Q ->
  option_rel Message.eq (find_message addr ts (add_message msg msgs)) (Some msg).
Proof.
  intros. unfold find_message, add_message.
  cbn. subst. rewrite NatMapFacts.find_or_add_eq_o; auto.
  rewrite QMapFacts.add_eq_o.
  - now destruct msg.
  - now rewrite H0.
Qed.

Lemma find_message_add_message_neq : forall msgs msg addr ts,
  addr <> msg.(a) \/ ~ (ts == msg.(ts_to))%Q ->
  find_message addr ts (add_message msg msgs) = find_message addr ts msgs.
Proof.
  intros. unfold find_message, add_message.
  cbn. destruct (Nat.eq_dec addr msg.(a)).
  - subst. rewrite NatMapFacts.find_or_add_eq_o; auto.
    destruct H; try easy.
    rewrite QMapFacts.add_neq_o; auto.
    intro. now symmetry in H0.
  - rewrite NatMapFacts.find_or_add_neq_o; auto.
Qed.

Definition find_message_or (a : addr) (date : date_type) (s: msg_set) (d: value) (view : view_type) : Message :=
  match find_message a date s with
  | Some m => m
  | None => mkMsg a d date date view
  end.

Arguments find_message_or : simpl never.

#[global] Instance find_message_or_eq : Proper (Logic.eq ==> Qeq ==> msg_set_eq ==> Logic.eq ==> view_eq ==> Message.eq) find_message_or.
Proof.
  cbn. intros. subst. unfold find_message_or.
  pose proof (@find_message_eq y y eq_refl x0 y0 H0 x1 y1 H1).
  now destruct (find_message y x0 x1) eqn:?, (find_message y y0 y1) eqn:?.
Qed.

Definition remove_message (a: addr) (date: date_type) (s: msg_set) : option (msg_set * Message) :=
  let msgs := NatMap.find_or a QMap.empty s in
  v <- QMap.find date msgs;;
  ret (NatMap.add a (QMap.remove date msgs) s, rebuildMsg a date v).

Definition remove_message_or (a: addr) (date: date_type) (s: msg_set) (d: value) (view : view_type) : msg_set * Message :=
  match remove_message a date s with
  | Some m => m
  | None => (s, mkMsg a d date date view)
  end.

Definition is_singleton_msg_set (s: msg_set) (msg: Message) :=
  match remove_message msg.(a) msg.(ts_to) s with
  | Some (s, msg') => Message.eqb msg msg' && is_empty_msg_set s
  | None => false
  end.

(* find the last message with an end date lower or equal to the given date *)
Fixpoint find_le {A} (date: date_type) (l: list (date_type * A)) : option (date_type * A) :=
  match l with
  | [] => None
  | (k, v) :: l =>
      match Qcompare date k with
      | Lt => None
      | Gt | Eq =>
        match find_le date l with Some m => Some m | None => Some (k, v) end
      end
  end.

#[global] Instance find_le_eq {A} {R : relation A} : Proper (Qeq ==> eqlistA (Qeq * R) ==> option_rel (Qeq * R)) find_le.
Proof.
  cbn. intros k k' Hk l l' Hl.
  induction Hl; cbn; auto.
  destruct x, x', H. cbn in H, H0.
  rewrite H, Hk. destruct (Qcompare k' q0) eqn:?; auto.
  - now destruct (find_le k l) eqn:?, (find_le k' l') eqn:?.
  - now destruct (find_le k l) eqn:?, (find_le k' l') eqn:?.
Qed.

Definition find_msg_le (a: addr) (date: date_type) (s: msg_set) : option Message :=
  msgs <- NatMap.find a s;;
  '(to, (from, val, view)) <- find_le date (QMap.bindings msgs);;
  ret (mkMsg a val from to view).

Arguments find_msg_le : simpl never.

#[global] Instance Reflexive_Qeq : Reflexive Qeq.
Proof.
 cbn. intros. apply Qeq_refl.
Qed.

#[global] Instance Reflexive_Qle : Reflexive Qle.
Proof.
  cbn. intros. apply Qle_refl.
Qed.

#[global] Instance Transitive_Qeq : Transitive Qeq.
Proof.
 cbn. intros. eapply Qeq_trans; eassumption.
Qed.

#[global] Instance Transitive_Qle : Transitive Qle.
Proof.
  cbn. apply Qle_trans.
Qed.

#[global] Instance find_msg_le_eq : Proper (Logic.eq ==> Qeq ==> msg_set_eq ==> option_rel Message.eq) find_msg_le.
Proof.
  cbn. intros. subst. red in H1.
  specialize (H1 y). unfold find_msg_le.
  destruct (NatMap.find y x1) eqn:?, (NatMap.find y y1) eqn:?; setoid_rewrite Heqo; setoid_rewrite Heqo0; try now destruct H1.
  cbn -[RelProd] in H1 |- *.
  assert (option_rel (Qeq * (Qeq * Logic.eq * view_eq))%signature (find_le x0 (QMap.bindings t)) (find_le y0 (QMap.bindings t0))).
  epose proof (@find_le_eq _ _ x0 y0 H0 (QMap.bindings t) (QMap.bindings t0) ltac:(now apply QMapFacts.bindings_m1)). rewrite H. reflexivity.
  destruct (find_le x0 _) as [(? & (? & ?) & ?)|] eqn:?, (find_le y0 _) as [(? & (? & ?) & ?)|] eqn:?; cbn; auto.
  destruct H as (? & (? & ?) & ?). red. auto.
Qed.

Lemma Qeq_bool_compare :
  forall q q', Qeq_bool q q' = true <-> Qcompare q q' = Eq.
Proof.
  intros. rewrite QMapFacts.O.F.compare_eq_iff.
  now rewrite Qeq_bool_iff.
Qed.

Lemma findA_InA {A} :
  forall l k (x : A),
  findA (Qeq_bool k) l = Some x ->
  InA (Qeq @@1)%signature (k, x) l.
Proof.
  intros. induction l.
  - discriminate.
  - destruct a0. cbn in *.
    destruct (Qeq_bool k q) eqn:?.
    + inversion H. subst. clear H.
      left. red. apply Qeq_bool_iff in Heqb. apply Heqb.
    + right. apply IHl, H.
Qed.

Lemma findA_not_InA {A} :
  forall l k (x : A),
  findA (Qeq_bool k) l = None <->
  ~ InA (Qeq @@1)%signature (k, x) l.
Proof.
  intros. induction l.
  { now split. }
  destruct a0. cbn in *.
  split; intro.
  - destruct (Qeq_bool k q) eqn:?; cbn.
    + discriminate.
    + intro. inversion H0; subst; clear H0.
      * apply Qeq_bool_neq in Heqb. now apply Heqb in H2.
      * apply IHl in H. now apply H in H2.
  - destruct (Qeq_bool k q) eqn:?.
    + exfalso. apply H. left.
      now apply Qeq_bool_eq in Heqb.
    + apply IHl. intro. apply H.
      now apply InA_cons_tl.
Qed.

Lemma find_le_findA {A} :
  forall l k k' (x : A),
  Sorted (Qlt @@1)%signature l ->
  find_le k l = Some (k', x) ->
  findA (Qeq_bool k') l = Some x /\ (k' <= k)%Q.
Proof.
  intros. revert x H0. induction H; intros; [discriminate |].
  destruct a0. cbn in H1 |- *.
  destruct (Qcompare k q) eqn:?.
  - apply QMapFacts.O.F.compare_eq_iff in Heqc.
    destruct (find_le k l) eqn:?.
    + inversion H1. subst. clear H1.
      specialize (IHSorted _ eq_refl).
      destruct H0. { discriminate. }
      destruct b. red in H0. cbn in H0, Heqo.
      rewrite <- Heqc in H0.
      rewrite Qlt_alt in H0. rewrite H0 in Heqo. discriminate.
    + inversion H1. subst. clear H1.
      rewrite Qeq_bool_refl. split; auto.
      rewrite Heqc. apply Qle_refl.
  - discriminate.
  - destruct (find_le k l) eqn:?.
    + inversion H1. subst. clear H1.
      specialize (IHSorted _ eq_refl) as [].
      split; auto.
      destruct (Qeq_bool k' q) eqn:?; auto.
      rewrite Qeq_bool_iff in Heqb. rewrite Heqb in H2.
      apply findA_InA in H1.
      rewrite InfA_alt in H0; auto. 3: typeclasses eauto.
      apply H0 in H1. 2, 3: typeclasses eauto.
      cbn in H1. apply Qlt_not_eq in H1. symmetry in Heqb. now apply H1 in Heqb.
    + inversion H1. subst. clear H1.
      rewrite Qeq_bool_refl. split; auto.
      apply Qgt_alt in Heqc. apply Qle_lteq. left. apply Heqc.
Qed.

Lemma findA_find_le {A} :
  forall l k (x : A),
  Sorted (Qlt @@1)%signature l ->
  findA (Qeq_bool k) l = Some x -> option_rel (Qeq * Logic.eq)%signature (find_le k l) (Some (k, x)).
Proof.
  intros. revert x H0. induction H; intros; [discriminate |].
  destruct a0. cbn in H1 |- *.
  destruct (Qcompare k q) eqn:?.
  - apply QMapFacts.O.F.compare_eq_iff in Heqc.
    apply Qeq_bool_iff in Heqc. rewrite Heqc in H1.
    inversion H1. subst. clear H1.
    destruct (find_le k l) eqn:?.
    + destruct p. eapply find_le_findA in Heqo as []; auto.
      apply findA_InA in H1.
      rewrite InfA_alt in H0. apply H0 in H1.
      2, 3, 4, 5: auto; typeclasses eauto.
      apply Qeq_bool_iff in Heqc. rewrite Heqc in H2.
      apply Qle_not_lt in H2. now apply H2 in H1.
    + split; auto. now rewrite Qeq_bool_iff in Heqc.
  -
Abort.

(* find the first message with an end date greater than the given date *)
Fixpoint find_gt {A} (date: date_type) (l: list (date_type * A)) : option (date_type * A) :=
  match l with
  | [] => None
  | (k, v) :: l =>
      match Qcompare date k with
      | Lt => Some (k, v)
      | Gt | Eq => find_gt date l
      end
  end.

Lemma find_gt_findA {A} :
  forall l k k' (x : A),
  Sorted (Qlt @@1)%signature l ->
  find_gt k l = Some (k', x) ->
  findA (Qeq_bool k') l = Some x /\ (k < k')%Q /\
    (forall k'', k < k'' -> k'' < k' -> findA (Qeq_bool k'') l = None)%Q.
Proof.
  intros. revert x H0. induction H; intros; [discriminate |].
  destruct a0. cbn in H1 |- *.
  destruct (Qcompare k q) eqn:?.
  - apply QMapFacts.O.F.compare_eq_iff in Heqc.
    apply IHSorted in H1 as (? & ? & ?).
    destruct (Qeq_bool k' q) eqn:?; auto.
    + apply Qeq_bool_eq in Heqb.
      rewrite Heqb, Heqc in H2. now apply Qlt_irrefl in H2.
    + repeat split; auto.
      intros. destruct (Qeq_bool k'' q) eqn:?; auto.
      apply Qeq_bool_eq in Heqb0. rewrite Heqc, Heqb0 in H4.
      now apply Qlt_irrefl in H4.
  - inversion H1. subst. clear H1.
    apply Qlt_alt in Heqc.
    rewrite Qeq_bool_refl. repeat split; auto.
    intros. destruct (Qeq_bool k'' k') eqn:?.
    + apply Qeq_bool_eq in Heqb. rewrite Heqb in H2.
      now apply Qlt_irrefl in H2.
    + eapply findA_not_InA with (x := x). intro.
      eapply QMapFacts.O.O.Sort_Inf_In in H0; eauto.
      eapply Qlt_irrefl. etransitivity. apply H2. apply H0.
  - apply QMapFacts.O.F.compare_gt_iff in Heqc.
    apply IHSorted in H1 as (? & ? & ?).
    destruct (Qeq_bool k' q) eqn:?; auto.
    + apply Qeq_bool_eq in Heqb.
      rewrite Heqb, Heqc in H2. now apply Qlt_irrefl in H2.
    + repeat split; auto. intros.
      destruct (Qeq_bool k'' q) eqn:?.
      * apply Qeq_bool_eq in Heqb0. rewrite Heqb0 in H4.
        exfalso. eapply Qlt_irrefl. etransitivity. apply Heqc. apply H4.
      * now apply H3.
Qed.

Lemma find_gt_None_findA {A} :
  forall (l : list (Q * A)) k k',
  Sorted (Qlt @@1)%signature l ->
  (k < k')%Q ->
  find_gt k l = None ->
  findA (Qeq_bool k') l = None.
Proof.
  intros. induction H; intros; [reflexivity |].
  destruct a0. cbn in H1 |- *.
  destruct (Qcompare k q) eqn:?.
  - apply QMapFacts.O.F.compare_eq_iff in Heqc.
    apply IHSorted in H1.
    destruct (Qeq_bool k' q) eqn:?; auto.
    apply Qeq_bool_eq in Heqb.
    rewrite Heqb, Heqc in H0. now apply Qlt_irrefl in H0.
  - inversion H1.
  - apply QMapFacts.O.F.compare_gt_iff in Heqc.
    apply IHSorted in H1.
    destruct (Qeq_bool k' q) eqn:?; auto.
    apply Qeq_bool_eq in Heqb.
    rewrite Heqb in H0.
    exfalso. eapply Qlt_irrefl. etransitivity; eassumption.
Qed.

Definition find_msg_gt (a: addr) (date: date_type) (s: msg_set) : option Message :=
  '(to, (from, val, view)) <- find_gt date (QMap.bindings (NatMap.find_or a QMap.empty s));;
  ret (mkMsg a val from to view).

Arguments find_msg_gt : simpl never.

Lemma Qeq_bool_eq_dec : forall x y,
  (if Q_as_OT.eq_dec x y then true else false) = Qeq_bool x y.
Proof.
  intros. destruct (Q_as_OT.eq_dec x y).
  - rewrite q. now rewrite Qeq_bool_refl.
  - destruct (Qeq_bool x y) eqn:?; auto.
    apply Qeq_bool_iff in Heqb. now apply n in Heqb.
Qed.

Lemma findA_proper {A B} : Proper ((Logic.eq ==> Logic.eq) ==> Logic.eq ==> Logic.eq) (@findA A B).
Proof.
  cbn. intros f g ? l l' <-. subst.
  induction l.
  - reflexivity.
  - destruct a0. cbn.
    erewrite <- H. 2: reflexivity.
    destruct (f a0) eqn:?; auto.
Qed.

Lemma find_msg_gt_find_message :
  forall a ts msg m,
  find_msg_gt a ts m = Some msg ->
  find_message a msg.(ts_to) m = Some msg /\ (ts < msg.(ts_to))%Q /\
  (forall ts', ts < ts' -> ts' < msg.(ts_to) -> find_message a ts' m = None)%Q.
Proof.
  intros. unfold find_msg_gt in H. cbn in H.
  destruct (find_gt _ _) eqn:?.
  - destruct p as (? & (? & ?) & ?). inversion H. subst. clear H. apply find_gt_findA in Heqo.
    2: apply QMap.bindings_spec2.
    cbn. destruct Heqo as (? & ? & ?). repeat split; auto.
    + unfold find_message. rewrite QMapFacts.bindings_o.
      erewrite findA_proper. 2: { cbn. intros. subst. apply Qeq_bool_eq_dec. }
      2: reflexivity. cbn. setoid_rewrite H. reflexivity.
    + intros. unfold find_message. rewrite QMapFacts.bindings_o.
      erewrite findA_proper. 2: { cbn. intros. subst. apply Qeq_bool_eq_dec. }
      2: reflexivity. cbn. now setoid_rewrite H1.
  - discriminate.
Qed.

Lemma find_msg_gt_None_find_message :
  forall addr ts ts' msgs,
  (ts < ts')%Q ->
  find_msg_gt addr ts msgs = None ->
  find_message addr ts' msgs = None.
Proof.
  intros. unfold find_msg_gt in H0. cbn in H0.
  destruct (find_gt _ _) eqn:?.
  - destruct p as (? & (? & ?) & ?). discriminate.
  - eapply find_gt_None_findA in Heqo.
    2: apply QMap.bindings_spec2. 2: apply H.
    unfold find_message. rewrite QMapFacts.bindings_o.
    erewrite findA_proper. 2: { cbn. intros. subst. apply Qeq_bool_eq_dec. }
    2: reflexivity. cbn. setoid_rewrite Heqo. reflexivity.
Qed.

Fixpoint find_lt {A} (date: date_type) (l: list (date_type * A)) : option (date_type * A) :=
  match l with
  | [] => None
  | (k, v) :: l =>
      match Q_as_OT.compare date k with
      | Lt | Eq => None
      | Gt =>
        match find_lt date l with Some m => Some m | None => Some (k, v) end
      end
  end.

Definition find_msg_lt (a: addr) (date: date_type) (s: msg_set) : option Message :=
  msgs <- NatMap.find a s;;
  '(to, (from, val, view)) <- find_lt date (QMap.bindings msgs);;
  ret (mkMsg a val from to view).

Arguments find_msg_lt : simpl never.

Definition max_view_ msgs : view_type :=
  NatMap.map (fun m => fst (value_or (QMapFacts.O.max_elt m) (0%Q, empty_message))) msgs.

Definition last_msg (a: addr) (s: msg_set) : option Message :=
  let msgs := NatMap.find_or a QMap.empty s in
  '(date, val) <- QMapFacts.O.max_elt msgs;;
  ret (rebuildMsg a date val).

Arguments last_msg : simpl never.
