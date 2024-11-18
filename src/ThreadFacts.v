From Coq Require Import
     Arith
     Classes.RelationPairs
     Lists.List
     Lia.

From ExtLib Require Import
     Data.Nat
     Data.String
     Structures.Monad.

From Coinduction Require Import all.
From ITree Require Import
     Basics.HeterogeneousRelations
     Core.Subevent
     Indexed.Sum.

From CTree Require Import
     CTree
     Eq
     Eq.SBisimAlt
     Misc.Pure.

Unset Universe Checking.

From Mem Require Import Utils Events Thread Sched.

Import ListNotations.


Section ThreadFactsEq.

Context {Arg A : Type} {E TE F C : Type -> Type}
  `{HasE : E -< F} `{HasTE : ThreadAnnotE TE -< F}.

#[global] Instance add_thread_eq :
  Proper (FnMap.Equal (elt := _) ==> eq ==> eq ==>
    TMap.Equal (elt := _) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal (elt := _))
    (@add_thread_ctree Arg A E TE C).
Proof.
  cbn. intros. subst. unfold add_thread_ctree.
  destruct (build_thread_ctree _ _ _ _ _ _) eqn:?.
  - unfold build_thread_ctree in Heqo. cbn in Heqo.
    repeat (destruct (FnMap.find _ _) eqn:? in Heqo); inv Heqo.
    rewrite H in Heqo0, Heqo1, Heqo2.
    unfold build_thread_ctree.
    rewrite Heqo0, Heqo1, Heqo2.
    cbn. pose proof @NatMapFacts.add_m. now rewrite H2.
  - unfold build_thread_ctree in Heqo. cbn in Heqo.
    repeat (destruct (FnMap.find _ _) eqn:? in Heqo); inv Heqo.
    + rewrite H in Heqo0, Heqo1, Heqo2.
      unfold build_thread_ctree.
      rewrite Heqo0, Heqo1, Heqo2.
      cbn. assumption.
    + rewrite H in Heqo0, Heqo1.
      unfold build_thread_ctree.
      rewrite Heqo0, Heqo1.
      cbn. assumption.
    + rewrite H in Heqo0.
      unfold build_thread_ctree.
      rewrite Heqo0.
      cbn. assumption.
Qed.

#[global] Instance step_thread_eq :
  Proper (FnMap.Equal (elt := _) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal (elt := _) ==> eq ==>
    equ (eq * eq * (TMap.Equal (elt := _))))
    (@step_thread Arg A E TE F C _ _).
Proof.
  cbn -[RelProd]. intros fns fns' Hfns get_val ? <- atomic ? <- nextTid ? <- tidExec ? <- tl tl' Htl t ? <-.
  revert nextTid tidExec tl tl' Htl t. coinduction R CH. intros.
  rewrite !unfold_step_thread. destruct (observe t) eqn:?.
  - constructor. split; auto.
    now apply NatMapFacts.remove_m.
  - reflexivity.
  - constructor. step. constructor. repeat split; auto. cbn.
    now apply NatMapFacts.add_m.
  - constructor. now apply CH.
  - destruct e; [destruct t0 |].
    + unfold step_thread_event.
      constructor. split; auto. unfold snd.
      pose proof @NatMapFacts.add_m. rewrite Hfns, Htl.
      reflexivity.
    + constructor. intros. split; auto.
      now apply NatMapFacts.add_m.
    + destruct s.
      * constructor. intros.
        step. constructor. split; auto.
        now apply NatMapFacts.add_m.
      * constructor. intros.
        step. constructor. split; auto.
        now apply NatMapFacts.add_m.
  - constructor. intros. now apply CH.
Qed.

#[global] Instance interleave_eq  :
  Proper (FnMap.Equal (elt := _) ==> eq ==> eq ==> eq ==> TMap.Equal (elt := _) ==> equ eq)
    (@interleave Arg A E TE F C _ _).
Proof.
  cbn. coinduction R CH. intros fns fns' Hfns get_val ? <- atomic ? <- nextTid ? <- tl tl' Htl.
  setoid_rewrite interleave_step_interleave.
  destruct (TMap.is_empty tl) eqn:?.
  { rewrite Htl in Heqb. rewrite Heqb. reflexivity. }
  rewrite Htl in Heqb. rewrite Heqb.
  rewrite <- (NatMapFacts.in_keys tl tl').
  2: reflexivity. 2: { apply NatMapFacts.Equal_Eqdom in Htl. apply Htl. }
  upto_bind_eq. intros [t b].
  rewrite <- Htl.
  destruct (TMap.find t tl) eqn:?.
  - unfold step_interleave.
    upto_bind. now apply step_thread_eq. red.
    intros ((? & ?) & ?) ((? & ?) & ?) ?.
    cbn in H. destruct H as ((<- & <-) & ?).
    constructor. now apply CH.
  - constructor. now apply CH.
Qed.

End ThreadFactsEq.

Definition Rstep_equ {E B X} : relation (bool * nat * _) :=
  (eq * eq * TMap.Equal1 (@equ E B X X eq))%signature.

Definition Rstep_sb {E B X} : relation (bool * nat * _) :=
  (eq * eq * TMap.Equal1 (@sbisim E E B B X X eq))%signature.

Definition Rstep_ss {E B X} : relation (bool * nat * _) :=
  (eq * eq * TMap.Equal1 (@ssim E E B B X X eq))%signature.

#[global] Instance Symmetric_Rstep_sb {E B X} :
  Symmetric (@Rstep_sb E B X).
Proof.
  typeclasses eauto.
Qed.

#[global] Instance Transitive_Rstep_sb {E B X} :
  Transitive (@Rstep_sb E B X).
Proof.
  typeclasses eauto.
Qed.

Section ThreadFacts.

Context {E TE F B : Type -> Type} {Arg X : Type}
  `{HasE: E -< F} `{HasTE : ThreadAnnotE TE -< F}.

Section Lemmas.

Context (fns : FnMap.t (list Arg -> ctree (@ThreadE (list Arg) +' TE +' E) B X))
  (get_val : X -> Arg) (atomic : bool) (nextTId : nat) 
  (tidExec : TMap.key) (pl : TMap.t (ctree (@ThreadE (list Arg) +' TE +' E) B X)).

Lemma step_thread_brD_inv {Y} : forall p
  (c : (SchedC +' B) Y) k x,
  step_thread (F := F) fns get_val atomic nextTId tidExec pl p ≅ Br c k ->
  exists c0 k0, p ≅ Br c0 k0 /\
    c = subevent _ c0 /\
    k x ≅ step_thread (Arg := Arg) fns get_val atomic nextTId tidExec pl (k0 x).
Proof.
  intros. rewrite unfold_step_thread in H. destruct (observe p) eqn:?; inv_equ.
  - destruct e; [destruct t | destruct s]; inv_equ.
  - exists c0, k0.
    now rewrite ctree_eta, Heqc0, EQ.
Qed.

Lemma step_thread_guard_inv : forall p t,
  step_thread (F := F) fns get_val atomic nextTId tidExec pl p ≅ Guard t ->
  exists t0, p ≅ Guard t0 /\
    t ≅ step_thread (Arg := Arg) fns get_val atomic nextTId tidExec pl t0.
Proof.
  intros. rewrite unfold_step_thread in H. destruct (observe p) eqn:?; inv_equ.
  - exists t0. now rewrite ctree_eta, Heqc.
  - destruct e; [destruct t0 | destruct s]; inv_equ.
Qed.

Lemma trans_step_thread_obs {Y} : forall
  (p : ctree (ThreadE +' TE +' E) B X) t' (e : E Y) x,
  trans (obs (subevent _ e) x) p t' ->
  exists t'',
    trans (obs (subevent _ e) x)
      (step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p)
      (Ret (atomic, nextTId, (TMap.add tidExec t'' pl))) /\
    t'' ≅ t'.
Proof.
  intros. do 3 red in H.
  remember (observe p) as op. remember (observe t') as ot'. remember (obs _ _).
  revert p Heqop. induction H; intros.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. eapply trans_br. 2: reflexivity. etrans.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. eapply trans_guard. etrans.
  - inv Heql.
  - inv Heql. invert. exists (k x).
    rewrite unfold_step_thread, <- Heqop. cbn.
    split. now constructor.
    now rewrite (ctree_eta t'), <- Heqot', <- ctree_eta.
  - inv Heql.
Qed.

Lemma trans_step_thread_obs_annot {Y} : forall
  (p : ctree (ThreadE +' TE +' E) B X) t' (e : TE Y) x,
  trans (obs (subevent _ e) x) p t' ->
  exists t'',
    trans (obs (subevent _ (ThreadAnnot tidExec e)) x)
      (step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p)
      (Ret (atomic, nextTId, (TMap.add tidExec t'' pl))) /\
    t'' ≅ t'.
Proof.
  intros. do 3 red in H.
  remember (observe p) as op. remember (observe t') as ot'. remember (obs _ _).
  revert p Heqop. induction H; intros.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. eapply trans_br. 2: reflexivity. etrans.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. eapply trans_guard. etrans.
  - inv Heql.
  - inv Heql. invert. exists (k x).
    rewrite unfold_step_thread, <- Heqop. cbn.
    split. now constructor.
    now rewrite (ctree_eta t'), <- Heqot', <- ctree_eta.
  - inv Heql.
Qed.

Lemma trans_step_thread_spawn : forall
  (p : ctree (ThreadE +' TE +' E) B X) t' f init cleanup (a : list Arg),
  trans (obs (subevent _ (Spawn f init cleanup a)) nextTId) p t' ->
  exists t'', trans (val (atomic, S nextTId,
    (TMap.add tidExec t''
      (add_thread_ctree fns get_val nextTId pl f init cleanup a))))
      (step_thread (F := F) fns get_val atomic nextTId tidExec pl p) Stuck /\
    t'' ≅ t'.
Proof.
  intros. do 3 red in H.
  remember (observe p) as op. remember (observe t') as ot'. remember (obs _ _).
  revert p Heqop. induction H; intros.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. etrans.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. etrans.
  - inv Heql.
  - inv Heql. invert. exists (k nextTId).
    rewrite unfold_step_thread, <- Heqop. cbn. split.
    2: { now rewrite (ctree_eta t'), <- Heqot', <- ctree_eta. }
    etrans.
  - inv Heql.
Qed.

Lemma trans_step_thread_setAtomic : forall
  (p : ctree (ThreadE +' TE +' E) B X) t' a,
  trans (obs (subevent _ (SetAtomic a)) tt) p t' ->
  exists t'', trans (val (a, nextTId, (TMap.add tidExec t'' pl)))
    (step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p) Stuck /\
    t'' ≅ t'.
Proof.
  intros. do 3 red in H. remember (observe p) as op. remember (observe t') as ot'. remember (obs _ _).
  revert p Heqop. induction H; intros.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. etrans.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. etrans.
  - inv Heql.
  - inv Heql. invert. exists (k tt).
    rewrite unfold_step_thread, <- Heqop. cbn. split; etrans.
    now rewrite (ctree_eta t'), <- Heqot', <- ctree_eta.
  - inv Heql.
Qed.

Lemma trans_step_thread_tau : forall
  (p : ctree (ThreadE +' TE +' E) B X) t',
  trans τ p t' ->
  exists t'', trans τ
    (step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p)
    (Ret (atomic, nextTId, (TMap.add tidExec t'' pl))) /\
    t'' ≅ t'.
Proof.
  intros. do 3 red in H. remember (observe p) as op. remember (observe t') as ot'. remember τ.
  revert p Heqop. induction H; intros.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. etrans.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl). destruct IHtrans_ as (t'' & TR & EQ).
    exists t''. split; auto. rewrite unfold_step_thread, <- Heqop. etrans.
  - exists t.
    rewrite unfold_step_thread, <- Heqop. cbn. split. econstructor. reflexivity.
    now rewrite (ctree_eta t'), <- Heqot', <- ctree_eta.
  - inv Heql.
  - inv Heql.
Qed.

Lemma trans_step_thread_val : forall
  (p : ctree (ThreadE +' TE +' E) B X) t' (v : X),
  trans (val v) p t' ->
  trans (val (false, nextTId, TMap.remove tidExec pl))
    (step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p)
    Stuck.
Proof.
  intros. do 3 red in H.
  remember (observe p) as op. remember (observe t') as ot'. remember (val v).
  revert p Heqop. induction H; intros.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl).
    rewrite unfold_step_thread, <- Heqop. etrans.
  - specialize (IHtrans_ Heqot' Heql _ eq_refl).
    rewrite unfold_step_thread, <- Heqop. etrans.
  - inv Heql.
  - inv Heql.
  - apply val_eq_inv in Heql as ->. rewrite unfold_step_thread, <- Heqop. constructor.
Qed.

Lemma step_thread_vis_inv {Y} : forall p (e : F Y) k,
  step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p ≅ Vis e k ->
  (exists e0 k0, e = subevent (H := HasE) _ e0 /\ p ≅ vis e0 k0 /\
    (forall x, k x ≅ Ret (atomic, nextTId, (TMap.add tidExec (k0 x) pl)))) \/
  (exists e0 k0, e = subevent (H := HasTE) _ (ThreadAnnot tidExec e0) /\ p ≅ vis e0 k0 /\
    (forall x, k x ≅ Ret (atomic, nextTId, (TMap.add tidExec (k0 x) pl)))).
Proof.
  intros.
  rewrite unfold_step_thread in H.
  destruct (observe p) eqn:?; try now inv_equ.
  destruct e0.
  - destruct t; inv_equ.
  - destruct s; inv_equ.
    + right. exists t, k0. split; auto. rewrite ctree_eta, Heqc. split; auto.
      intros. now rewrite EQ.
    + left. exists e0, k0. split; auto. rewrite ctree_eta, Heqc. split; auto.
      intros. now rewrite EQ.
Qed.

Lemma step_thread_step_inv : forall p t,
  step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p ≅ Step t ->
  exists t0, p ≅ Step t0 /\
    (t ≅ Ret (atomic, nextTId, (TMap.add tidExec t0 pl))).
Proof.
  intros.
  rewrite unfold_step_thread in H.
  destruct (observe p) eqn:?.
  - inv_equ.
  - inv_equ.
  - inv_equ.
    exists t0. split.
    + now rewrite ctree_eta, Heqc.
    + now rewrite H.
  - inv_equ.
  - destruct e as [? | []]; inv_equ. destruct t0; inv_equ.
  - inv_equ.
Qed.

Lemma step_thread_ret_inv : forall p atomic1 nextTId1 pl1,
  step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl p ≅ Ret (atomic1, nextTId1, pl1) ->
  (exists v0, p ≅ Ret v0 /\ atomic1 = false /\ nextTId1 = nextTId /\ pl1 = TMap.remove tidExec pl) \/
  (exists f init cleanup arg k, p ≅ vis (Spawn f init cleanup arg) k /\ atomic1 = atomic /\ nextTId1 = S nextTId /\
    pl1 = (TMap.add tidExec (k nextTId) (add_thread_ctree fns get_val nextTId pl f init cleanup arg))) \/
  (exists k, p ≅ vis (SetAtomic atomic1) k /\ nextTId1 = nextTId /\
    pl1 = TMap.add tidExec (k tt) pl).
Proof.
  intros.
  rewrite unfold_step_thread in H.
  destruct (observe p) eqn:?; try now inv_equ.
  - inv_equ. inversion H. subst.
    left. exists r. now rewrite ctree_eta, Heqc.
  - unfold step_thread_event in H. destruct e as [| []]; inv_equ.
    destruct t; inv_equ; inv H.
    + right. left.
      exists f, init, cleanup, arg, k. rewrite ctree_eta, Heqc.
      repeat split; auto.
    + right. right.
      exists k. now rewrite ctree_eta, Heqc.
Qed.

End Lemmas.

#[global] Instance add_thread_equ :
  Proper (FnMap.Equal1 (eq ==> equ eq) ==> eq ==> eq ==>
    TMap.Equal1 (equ eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (equ eq))
    (@add_thread_ctree Arg X E TE B).
Proof.
  do 9 red. intros. subst. unfold add_thread_ctree, build_thread_ctree. cbn.
  assert (option_rel (eq ==> equ eq)%signature (FnMap.find y4 x) (FnMap.find y4 y)) by now rewrite H.
  destruct (FnMap.find y4 x) eqn:?, (FnMap.find y4 y) eqn:?; try inv H0.
  2: now rewrite H2.
  assert (option_rel (eq ==> equ eq)%signature (FnMap.find y3 x) (FnMap.find y3 y)) by now rewrite H.
  destruct (FnMap.find y3 x) eqn:?, (FnMap.find y3 y) eqn:?; try inv H1.
  2: now rewrite H2.
  assert (option_rel (eq ==> equ eq)%signature (FnMap.find y5 x) (FnMap.find y5 y)) by now rewrite H.
  destruct (FnMap.find y5 x) eqn:?, (FnMap.find y5 y) eqn:?; try inv H3.
  2: now rewrite H2.
  cbn -[respectful] in H0, H1, H3.
  apply NatMapFacts.add_m1; auto.
  rewrite H0. do 2 (upto_bind_eq; intros).
  rewrite H1. do 2 (upto_bind_eq; intros).
  now rewrite H3.
Qed.

#[global] Instance step_thread_equ :
  Proper (FnMap.Equal1 (eq ==> equ eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (@equ (ThreadE +' TE +' E) B X X eq) ==> equ eq ==>
    equ (@Rstep_equ (ThreadE +' TE +' E) B X))
    (step_thread (Arg := Arg) (F := F)).
Proof.
  intros fns fns' Hfns atomic ? <- get_val ? <- nextTId ? <- tidExec ? <-. cbn.
  unfold equ at 3. coinduction R CH. (* FIXME fix __coinduction_equ unfolding *)
  intros pl pl' ? p p' EQ.
  rewrite (ctree_eta p), (ctree_eta p') in EQ.
  rewrite !unfold_step_thread.
  destruct (observe p) eqn:?, (observe p') eqn:?; inv_equ.
  - constructor. cbn.
    split; auto. apply NatMapFacts.remove_m1; auto.
  - constructor.
  - constructor. cbn.
    step. constructor.
    split; auto. apply NatMapFacts.add_m1; auto.
  - constructor. cbn. apply CH; auto.
  - destruct e0 as [| []].
    + unfold step_thread_event. destruct t.
      * constructor.
        split; auto.
        apply NatMapFacts.add_m1; auto. apply EQ0. apply add_thread_equ; auto.
      * constructor. cbn.
        split; auto.
        apply NatMapFacts.add_m1; auto. apply EQ0.
    + constructor. intros.
      step. constructor. cbn.
      split; auto.
      apply NatMapFacts.add_m1; auto. apply EQ0.
    + constructor. intros.
      step. constructor. cbn.
      split; auto.
      apply NatMapFacts.add_m1; auto. apply EQ0.
  - constructor. intros. now apply CH.
Qed.

#[global] Instance interleave_equ :
  Proper (FnMap.Equal1 (eq ==> equ eq) ==> eq ==> eq ==> eq ==> TMap.Equal1 (equ eq) ==>
    equ eq)
    (@interleave Arg X E TE F B _ _).
Proof.
  intros fns fns' Hfns get_val ? <- tidExec ? <- nextTId ? <-. red.
  revert tidExec nextTId. coinduction R CH. intros ?? pl pl' EQ.
  setoid_rewrite interleave_step_interleave.
  pose proof @NatMapFacts.is_empty_m. rewrite <- EQ. clear H.
  destruct (TMap.is_empty pl) eqn:?; [reflexivity |].
  rewrite <- (NatMapFacts.in_keys pl pl'); [| auto |].
  2: { eapply NatMapFacts.Equal1_Eqdom. apply EQ. }
  upto_bind_eq. destruct x as [tidExec1 atomic].
  pose proof (EQ tidExec1).
  destruct (TMap.find tidExec1 pl) eqn:?, (TMap.find tidExec1 pl') eqn:?; try solve [ destruct H ].
  - cbn in H.
    unfold step_interleave.
    upto_bind. { eapply step_thread_equ; eauto. }
    intros ((? & ?) & ?) ((? & ?) & ?) ?.
    cbn in H0. destruct H0 as ((<- & <-) & ?).
    constructor. now apply CH.
  - constructor. apply CH; auto.
Qed.

#[global] Instance step_interleave_equ :
  Proper (FnMap.Equal1 (eq ==> equ eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (equ eq) ==> equ eq ==> equ eq)
    (@step_interleave Arg X E TE F B _ _).
Proof.
  do 3 red. intros fns fns' ? get_val ? <- atomic ? <- nextTId ? <- tid ? <- pl pl' SIM p p' SIM'.
  unfold step_interleave.
  upto_bind. apply step_thread_equ; auto.
  intros. destruct x1 as ((? & ?) & ?), x2 as ((? & ?) & ?).
  cbn in H0. destruct H0 as ((-> & ->) & ?).
  step. constructor. now apply interleave_equ.
Qed.

(* ssim *)

#[global] Instance add_thread_ssim :
  Proper (FnMap.Equal1 (eq ==> ssim eq) ==> eq ==> eq ==>
    TMap.Equal1 (ssim eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (ssim eq))
    (@add_thread_ctree Arg X E TE B).
Proof.
  do 9 red. intros. subst. unfold add_thread_ctree, build_thread_ctree. cbn.
  assert (option_rel (eq ==> ssim eq)%signature (FnMap.find y4 x) (FnMap.find y4 y)) by now rewrite H.
  destruct (FnMap.find y4 x) eqn:?, (FnMap.find y4 y) eqn:?; try inv H0.
  2: now rewrite H2.
  assert (option_rel (eq ==> ssim eq)%signature (FnMap.find y3 x) (FnMap.find y3 y)) by now rewrite H.
  destruct (FnMap.find y3 x) eqn:?, (FnMap.find y3 y) eqn:?; try inv H1.
  2: now rewrite H2.
  assert (option_rel (eq ==> ssim eq)%signature (FnMap.find y5 x) (FnMap.find y5 y)) by now rewrite H.
  destruct (FnMap.find y5 x) eqn:?, (FnMap.find y5 y) eqn:?; try inv H3.
  2: now rewrite H2.
  cbn -[respectful] in H0, H1, H3.
  apply NatMapFacts.add_m1; auto.
  rewrite H0. apply ssim_clo_bind_eq; auto. intros.
  apply ssim_clo_bind_eq; auto. intros _.
  rewrite H1. apply ssim_clo_bind_eq; auto. intros.
  apply ssim_clo_bind_eq; auto.
Qed.

#[global] Instance step_thread_ssim :
  Proper (FnMap.Equal1 (eq ==> ssim eq) ==> eq ==> eq ==> eq ==> eq ==>
      TMap.Equal1 (@ssim (ThreadE +' TE +' E) _ B B X X eq) ==>
      ssim eq ==>
      ssim (lift_val_rel (@Rstep_ss (@ThreadE (list Arg) +' TE +' E) B X)))
    (step_thread (Arg := Arg) (F := F)).
Proof.
  cbn -[Rstep_ss respectful]. do 8 red. coinduction CR CH.
  intros fns fns' Hfns get_val ? <- atomic ? <- nextTId ? <- tidExec ? <- pl pl' ? p p' SIM ?? TR.
  do 3 red in TR.
  remember (observe (step_thread _ _ _ _ _ _ _)) as os. remember (observe t') as ot'.
  eassert (EQ : go os ≅ _). { rewrite Heqos, <- ctree_eta. reflexivity. } clear Heqos.
  step in SIM. revert p p' EQ SIM.
  induction TR; intros.
  - symmetry in EQ. apply step_thread_brD_inv with (x := x) in EQ as (?c & ?k & EQp & EQk).
    subs. apply ss_br_l_inv with (x := x) in SIM.
    apply IHTR in SIM; auto. now rewrite <- ctree_eta.
  - symmetry in EQ. apply step_thread_guard_inv in EQ as (?t & EQp & EQt).
    subs. apply ss_guard_l_inv in SIM.
    apply IHTR in SIM; auto. now rewrite <- ctree_eta.
  - symmetry in EQ. apply step_thread_step_inv in EQ as (t0 & EQp & EQt).
    subs. apply ss_step_l_inv in SIM as (l' & u' & TR & SIM & <-).
    eapply trans_step_thread_tau in TR as (u'' & TR & EQ).
    eexists _, _. split; [apply TR |]. split; [| constructor; etrans].
    rewrite (ctree_eta t'), <- Heqot', <- ctree_eta, H0.
    step. apply step_ss_ret. left. constructor. cbn.
    split; auto.
    apply NatMapFacts.add_m1; auto.
    rewrite EQ. apply SIM.
  - symmetry in EQ.
    apply step_thread_vis_inv in EQ as [(e0 & k0 & -> & EQp & EQk) | (e0 & k0 & -> & EQp & EQk)].
    + subs. apply ss_vis_l_inv with (x := x) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_obs in TR as (u'' & TR & EQ).
      eexists _, _. split; [apply TR |]. split; [| constructor; etrans].
      rewrite (ctree_eta t'), <- Heqot', <- ctree_eta, <- H0, EQk.
      step. apply step_ss_ret. constructor. cbn.
      split; auto.
      apply NatMapFacts.add_m1; auto.
      rewrite EQ. apply SIM.
    + subs. apply ss_vis_l_inv with (x := x) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_obs_annot in TR as (u'' & TR & EQ).
      eexists _, _. split; [apply TR |]. split; [| constructor; etrans].
      rewrite (ctree_eta t'), <- Heqot', <- ctree_eta, <- H0, EQk.
      step. apply step_ss_ret. constructor. cbn.
      split; auto.
      apply NatMapFacts.add_m1; auto.
      rewrite EQ. apply SIM.
  - symmetry in EQ. destruct r as ((? & ?) & ?).
    apply step_thread_ret_inv in EQ as ?.
    destruct H0 as [(v & EQp & -> & -> & ->) | [(f & init & cleanup & arg & k0 & EQp & -> & -> & ->) | (k0 & EQp & -> & ->)]].
    + rewrite EQp in SIM. apply ss_ret_l_inv in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_val in TR.
      eexists _, _. split; [apply TR |]. cbn. split.
      {
        (* FIXME for some reason rewrite does not work *)
        eapply equ_clos_sst_goal.
        rewrite (ctree_eta t'), <- Heqot'. reflexivity. reflexivity.
        step. apply is_stuck_sb; apply Stuck_is_stuck. }
      constructor. cbn. split; auto.
      apply NatMapFacts.remove_m1; auto.
    + rewrite EQp in SIM.
      apply ss_vis_l_inv with (x := nextTId) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_spawn in TR as (u'' & TR & EQu'').
      eexists _, _. split; [apply TR |]. split.
      { rewrite (ctree_eta t'), <- Heqot'. step. apply is_stuck_sb; apply Stuck_is_stuck. }
      constructor. split; auto.
      apply NatMapFacts.add_m1; auto. now rewrite EQu''.
      apply add_thread_ssim; auto.
    + rewrite EQp in SIM.
      apply ss_vis_l_inv with (x := tt) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_setAtomic in TR as (u'' & TR & EQu'').
      eexists _, _. split; [apply TR |]. split.
      { rewrite (ctree_eta t'), <- Heqot'. step. apply is_stuck_sb; apply Stuck_is_stuck. }
      constructor. cbn. split; auto.
      apply NatMapFacts.add_m1; auto.
      rewrite EQu''. apply SIM.
Qed.

#[global] Instance interleave_ssim :
  Proper (FnMap.Equal1 (eq ==> ssim eq) ==> eq ==> eq ==> eq ==> TMap.Equal1 (ssim eq) ==> ssim eq)
    (@interleave Arg X E TE F B _ _).
Proof.
  intros fns fns' Hfns get_val ? <- tidExec ? <- nextTId ? <- tl tl' SIM.
  unfold interleave.
  eapply IterFacts.ssim_iter with
    (Ra := (eq * eq * TMap.Equal1 (ssim eq))%signature) (Rb := eq) (L := eq).
  { apply update_val_rel_correct. }
  { intros. split; auto. intros. now apply val_eq_inv in H. }
  2: { auto. }
  clear tidExec nextTId tl tl' SIM.
  intros ((tidExec & nextTId) & tl) ([] & tl') ?. cbn in H. destruct H as ((<- & <-) & SIM).
  pose proof @NatMapFacts.is_empty_m. rewrite SIM. clear H.
  destruct (TMap.is_empty tl') eqn:?. { step. apply step_ss_ret. constructor. cbn. reflexivity. }
  eapply ssim_clo_bind_gen with (L0 := eq). { apply is_update_val_rel_update_val_rel_eq. }
  {
    rewrite <- (NatMapFacts.in_keys tl tl').
    2: reflexivity. 2: now eapply NatMapFacts.Equal1_Eqdom.
    reflexivity.
  }
  intros [tidExec1 atomic1].
  pose proof (SIM tidExec1).
  intros [] [=]. rewrite <- H1, <- H2. clear k b H1 H2.
  destruct (TMap.find tidExec1 tl) eqn:?, (TMap.find tidExec1 tl') eqn:?; try solve [ destruct H ].
  - cbn in H. eapply ssim_clo_bind_gen with (R0 := Rstep_ss).
    2: { eapply step_thread_ssim; eauto. }
    { red. rewrite update_val_rel_update_val_rel. reflexivity. }
    intros ((? & ?) & ?) ((? & ?) & ?) ?.
    cbn in H0. destruct H0 as ((<- & <-) & ?).
    intros. step. apply step_ss_ret. constructor. cbn. auto.
  - intros. step. apply step_ss_ret. constructor. cbn. auto.
Qed.

#[global] Instance step_interleave_ssim :
  Proper (FnMap.Equal1 (eq ==> ssim eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (ssim eq) ==> ssim eq ==> ssim eq)
    (@step_interleave Arg X E TE F B _ _).
Proof.
  intros ??? ??? ??? ??? ??? pl pl' SIM p p' SIM'.
  unfold step_interleave.
  eapply ssim_clo_bind. apply step_thread_ssim; auto.
  intros ((? & ?) & ?) ((? & ?) & ?) ?.
  cbn in H4. destruct H4 as ((-> & ->) & ?).
  destruct b0.
  rewrite !sb_guard. apply interleave_ssim; auto.
  now rewrite !sb_guard, H, H0, H4.
Qed.

(* sbisim *)

#[global] Instance add_thread_sbisim :
  Proper (FnMap.Equal1 (eq ==> sbisim eq) ==> eq ==> eq ==>
    TMap.Equal1 (sbisim eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (sbisim eq))
    (@add_thread_ctree Arg X E TE B).
Proof.
  do 9 red. intros. subst. unfold add_thread_ctree, build_thread_ctree. cbn.
  assert (option_rel (eq ==> sbisim eq)%signature (FnMap.find y4 x) (FnMap.find y4 y)) by now rewrite H.
  destruct (FnMap.find y4 x) eqn:?, (FnMap.find y4 y) eqn:?; try inv H0.
  2: now rewrite H2.
  assert (option_rel (eq ==> sbisim eq)%signature (FnMap.find y3 x) (FnMap.find y3 y)) by now rewrite H.
  destruct (FnMap.find y3 x) eqn:?, (FnMap.find y3 y) eqn:?; try inv H1.
  2: now rewrite H2.
  assert (option_rel (eq ==> sbisim eq)%signature (FnMap.find y5 x) (FnMap.find y5 y)) by now rewrite H.
  destruct (FnMap.find y5 x) eqn:?, (FnMap.find y5 y) eqn:?; try inv H3.
  2: now rewrite H2.
  cbn -[respectful] in H0, H1, H3.
  apply NatMapFacts.add_m1; auto.
  rewrite H0. do 2 (upto_bind_eq; intros).
  rewrite H1. do 2 (upto_bind_eq; intros).
  now rewrite H3.
Qed.

#[global] Instance step_thread_sbisim :
  Proper (FnMap.Equal1 (eq ==> sbisim eq) ==> eq ==> eq ==> eq ==> eq ==>
      TMap.Equal1 (@sbisim (ThreadE +' TE +' E) _ B B X X eq) ==>
      sbisim eq ==>
      sbisim (lift_val_rel (@Rstep_sb (@ThreadE (list Arg) +' TE +' E) B X)))
    (step_thread (Arg := Arg) (F := F)).
Proof.
  cbn -[Rstep_sb respectful]. do 8 red. coinduction CR CH. symmetric using idtac.
  {
    intros. apply H; auto.
    - now symmetry.
    - now symmetry.
    - now symmetry.
  }
  intros fns fns' Hfns get_val ? <- atomic ? <- nextTId ? <- tidExec ? <- pl pl' ? p p' SIM ?? TR.
do 3 red in TR.
  remember (observe (step_thread _ _ _ _ _ _ _)) as os. remember (observe t') as ot'.
  eassert (EQ : go os ≅ _). { rewrite Heqos, <- ctree_eta. reflexivity. } clear Heqos.
  step in SIM. destruct SIM as [SIM _].
  revert p p' EQ SIM.
  induction TR; intros.
  - symmetry in EQ. apply step_thread_brD_inv with (x := x) in EQ as (?c & ?k & EQp & EQk).
    subs. apply ss_br_l_inv with (x := x) in SIM.
    apply IHTR in SIM; auto. now rewrite <- ctree_eta.
  - symmetry in EQ. apply step_thread_guard_inv in EQ as (?t & EQp & EQt).
    subs. apply ss_guard_l_inv in SIM.
    apply IHTR in SIM; auto. now rewrite <- ctree_eta.
  - symmetry in EQ. apply step_thread_step_inv in EQ as (t0 & EQp & EQt).
    subs. apply ss_step_l_inv in SIM as (l' & u' & TR & SIM & <-).
    eapply trans_step_thread_tau in TR as (u'' & TR & EQ).
    eexists _, _. split; [apply TR |]. split; [| constructor; etrans].
    rewrite (ctree_eta t'), <- Heqot', <- ctree_eta, H0.
    step. apply step_sb_ret. left. constructor. cbn.
    split; auto.
    apply NatMapFacts.add_m1; auto.
    rewrite EQ. apply SIM.
  - symmetry in EQ.
    apply step_thread_vis_inv in EQ as [(e0 & k0 & -> & EQp & EQk) | (e0 & k0 & -> & EQp & EQk)].
    + subs. apply ss_vis_l_inv with (x := x) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_obs in TR as (u'' & TR & EQ).
      eexists _, _. split; [apply TR |]. split; [| constructor; etrans].
      rewrite (ctree_eta t'), <- Heqot', <- ctree_eta, <- H0, EQk.
      step. apply step_sb_ret. constructor. cbn.
      split; auto.
      apply NatMapFacts.add_m1; auto.
      rewrite EQ. apply SIM.
    + subs. apply ss_vis_l_inv with (x := x) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_obs_annot in TR as (u'' & TR & EQ).
      eexists _, _. split; [apply TR |]. split; [| constructor; etrans].
      rewrite (ctree_eta t'), <- Heqot', <- ctree_eta, <- H0, EQk.
      step. apply step_sb_ret. constructor. cbn.
      split; auto.
      apply NatMapFacts.add_m1; auto.
      rewrite EQ. apply SIM.
  - symmetry in EQ. destruct r as ((? & ?) & ?).
    apply step_thread_ret_inv in EQ as ?.
    destruct H0 as [(v & EQp & -> & -> & ->) | [(f & init & cleanup & arg & k0 & EQp & -> & -> & ->) | (k0 & EQp & -> & ->)]].
    + rewrite EQp in SIM. apply ss_ret_l_inv in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_val in TR.
      eexists _, _. split; [apply TR |]. cbn. split.
      {
        (* FIXME for some reason rewrite does not work *)
        eapply equ_clos_sb_goal.
        rewrite (ctree_eta t'), <- Heqot'. reflexivity. reflexivity.
        step. apply is_stuck_sb; apply Stuck_is_stuck.
      }
      constructor. cbn. split; auto.
      apply NatMapFacts.remove_m1; auto.
    + rewrite EQp in SIM.
      apply ss_vis_l_inv with (x := nextTId) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_spawn in TR as (u'' & TR & EQu'').
      eexists _, _. split; [apply TR |]. split.
      { rewrite (ctree_eta t'), <- Heqot'. step. apply is_stuck_sb; apply Stuck_is_stuck. }
      constructor. split; auto.
      apply NatMapFacts.add_m1; auto. now rewrite EQu''.
      apply add_thread_sbisim; auto.
    + rewrite EQp in SIM.
      apply ss_vis_l_inv with (x := tt) in SIM as (l' & u' & TR & SIM & <-).
      eapply trans_step_thread_setAtomic in TR as (u'' & TR & EQu'').
      eexists _, _. split; [apply TR |]. split.
      { rewrite (ctree_eta t'), <- Heqot'. step. apply is_stuck_sb; apply Stuck_is_stuck. }
      constructor. cbn. split; auto.
      apply NatMapFacts.add_m1; auto.
      rewrite EQu''. apply SIM.
Qed.

Lemma option_rel_flip : forall {X} (R : relation X) x y,
  option_rel R x y <-> option_rel (flip R) y x.
Proof.
  intros. split; intro; now destruct x, y.
Qed.

#[global] Instance interleave_sbisim :
  Proper (FnMap.Equal1 (eq ==> sbisim eq) ==> eq ==> eq ==> eq ==> TMap.Equal1 (sbisim eq) ==> sbisim eq)
    (@interleave Arg X E TE F B _ _).
Proof.
  intros fns fns' Hfns get_val ? <- tidExec ? <- nextTId ? <- tl tl' SIM.
  unfold interleave.
  eapply IterFacts.sbisim_iter with
    (Ra := (eq * eq * TMap.Equal1 (sbisim eq))%signature) (Rb := eq) (L := eq).
  { apply update_val_rel_correct. }
  { intros. split; auto. intros. now apply val_eq_inv in H. }
  2: { auto. }
  clear tidExec nextTId tl tl' SIM.
  intros ((tidExec & nextTId) & tl) ([] & tl') ?. cbn in H. destruct H as ((<- & <-) & SIM).
  pose proof @NatMapFacts.is_empty_m. rewrite <- SIM. clear H.
  destruct (TMap.is_empty tl) eqn:?. { step. apply step_sb_ret. constructor. cbn. reflexivity. }
  eapply sbisim_clo_bind_gen with (L0 := eq). { apply is_update_val_rel_update_val_rel_eq. }
  {
    rewrite <- (NatMapFacts.in_keys tl tl').
    2: reflexivity. 2: now eapply NatMapFacts.Equal1_Eqdom.
    reflexivity.
  }
  intros [tidExec1 atomic1].
  pose proof (SIM tidExec1).
  intros [] [=]. rewrite <- H1, <- H2. clear k b H1 H2.
  destruct (TMap.find tidExec1 tl) eqn:?, (TMap.find tidExec1 tl') eqn:?; try solve [ destruct H ].
  - cbn in H. eapply sbisim_clo_bind_gen with (R0 := Rstep_sb).
    2: { eapply step_thread_sbisim; eauto. }
    { red. rewrite update_val_rel_update_val_rel. reflexivity. }
    intros ((? & ?) & ?) ((? & ?) & ?) ?.
    cbn in H0. destruct H0 as ((<- & <-) & ?).
    intros. step. apply step_sb_ret. constructor. cbn. auto.
  - intros. step. apply step_sb_ret. constructor. cbn. auto.
Qed.

#[global] Instance step_interleave_sbisim :
  Proper (FnMap.Equal1 (eq ==> sbisim eq) ==> eq ==> eq ==> eq ==> eq ==>
    TMap.Equal1 (sbisim eq) ==> sbisim eq ==> sbisim eq)
    (@step_interleave Arg X E TE F B _ _).
Proof.
  intros ??? ??? ??? ??? ??? pl pl' SIM p p' SIM'.
  unfold step_interleave.
  eapply sbisim_clo_bind. apply step_thread_sbisim; auto.
  intros ((? & ?) & ?) ((? & ?) & ?) ?.
  cbn in H4. destruct H4 as ((-> & ->) & ?).
  destruct b0.
  rewrite !sb_guard. apply interleave_sbisim; auto.
  now rewrite !sb_guard, H, H0, H4.
Qed.

Lemma step_thread_stuck : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X))
  tidExec,
  step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl Stuck ≅ Stuck.
Proof.
  intros. rewrite unfold_step_thread. reflexivity.
Qed.

Lemma step_thread_br {Y} : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X))
  tidExec (c : B Y) k,
  step_thread (F := F) fns get_val atomic nextTId tidExec pl (Br c k) ≅
    br c (fun x => step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl (k x)).
Proof.
  intros. rewrite unfold_step_thread. reflexivity.
Qed.

Lemma step_interleave_step : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X))
  tidExec t,
  step_interleave (F := F) fns get_val atomic nextTId tidExec pl (Step t) ≅
    Step (Guard (interleave (Arg := Arg) (F := F) fns get_val
      (if atomic then Some tidExec else None)
      nextTId (TMap.add tidExec t pl))).
Proof.
  intros. unfold step_interleave. rewrite unfold_step_thread. cbn.
  rewrite bind_step. step. constructor. intros.
  rewrite bind_ret_l. reflexivity.
Qed.

(*
Lemma step_interleave_brS {Y} : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X))
  tidExec (c : B Y) k,
  step_interleave (F := F) fns get_val atomic nextTId tidExec pl (BrS c k) ≅
    brS c (fun x => Guard (interleave (Arg := Arg) (F := F) fns get_val
      (if atomic then Some tidExec else None)
      nextTId (TMap.add tidExec (k x) pl))).
Proof.
  intros. unfold step_interleave. rewrite unfold_step_thread. cbn.
  rewrite bind_br. step. constructor. intros.
  rewrite bind_ret_l. reflexivity.
Qed.
*)

Lemma step_interleave_vis {Y} : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X))
  tidExec (e : E Y) k,
  step_interleave (F := F) fns get_val atomic nextTId tidExec pl (vis e k) ≅
    vis e (fun x => Guard
      (interleave (Arg := Arg) (F := F) fns get_val
        (if atomic then Some tidExec else None)
        nextTId (TMap.add tidExec (k x) pl))).
Proof.
  intros. unfold step_interleave. rewrite unfold_step_thread. cbn.
  rewrite bind_vis. step. constructor. intros.
  rewrite bind_ret_l. reflexivity.
Qed.

Lemma step_interleave_setAtomic : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X)) tidExec atomic1 k,
  step_interleave (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl (vis (SetAtomic atomic1) k) ≅
    Guard (interleave (F := F) fns get_val
      (if atomic1 then Some tidExec else None)
      nextTId (TMap.add tidExec (k tt) pl)).
Proof.
  intros. unfold step_interleave. rewrite unfold_step_thread. cbn.
  rewrite bind_ret_l. reflexivity.
Qed.

Lemma step_interleave_spawn : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X)) tidExec fn init cleanup arg k,
  step_interleave (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl (vis (Spawn fn init cleanup arg) k) ≅
    Guard (interleave (F := F) fns get_val
      (if atomic then Some tidExec else None) (S nextTId)
      (TMap.add tidExec (k nextTId)
        (add_thread_ctree fns get_val nextTId pl fn init cleanup arg))).
Proof.
  intros. unfold step_interleave. rewrite unfold_step_thread. cbn.
  rewrite bind_ret_l. reflexivity.
Qed.

Lemma step_thread_bind_pure : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X)) tidExec t k,
  pure_finite t ->
  step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl (CTree.bind t k)
  (~ lift_val_rel (@Rstep_sb (@ThreadE (list Arg) +' TE +' E) B X))
  CTree.bind (interp_thread (A := X) tidExec nextTId t)
    (fun '(nextTId, x) => step_thread (F := F) fns get_val atomic nextTId tidExec pl (k x)).
Proof.
  intros. unfold interp_thread.
  induction H.
  - rewrite EQ at 2. subs. rewrite FoldStateT.interp_state_ret.
    rewrite bind_ret_l with (x := (nextTId, v)).
    apply step_thread_sbisim; auto.
    now rewrite bind_ret_l.
  - rewrite EQ at 2. subs. rewrite FoldStateT.interp_state_stuck. rewrite !bind_stuck.
    rewrite step_thread_stuck. step. apply is_stuck_sb; apply Stuck_is_stuck.
  - rewrite EQ at 2. subs. rewrite FoldStateT.interp_state_br. cbn -[Rstep_sb].
    rewrite bind_bind, bind_branch.
    rewrite unfold_step_thread. cbn -[Rstep_sb].
    step. apply step_sb_br_id. intro.
    rewrite bind_guard. symmetry. apply step_sb_guard_l; auto. symmetry.
    rewrite ((gfp_fp (sb _) _ _)). apply H.
  - rewrite EQ at 2. subs. rewrite FoldStateT.interp_state_guard. cbn -[Rstep_sb].
    rewrite !bind_guard.
    rewrite unfold_step_thread. cbn -[Rstep_sb].
    apply sbisim_guard. apply IHpure_finite_.
Qed.

Lemma step_interleave_bind_pure : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X)) tidExec t k,
  pure_finite t ->
  step_interleave (F := F) fns get_val atomic nextTId tidExec pl (CTree.bind t k) ~
  CTree.bind (interp_thread (A := X) tidExec nextTId t)
    (fun x => let '(nextTId, x) := x in
      step_interleave (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl (k x)).
Proof.
  intros. unfold step_interleave.
  pose proof (bind_bind (E := F) (Z := nat)
    (interp_thread tidExec nextTId t)
    (fun '(nextTId0, x) => step_thread fns get_val atomic nextTId0 tidExec pl (k x))).
  cbn in H0.
  (* FIXME this is ugly *)
  eassert (
    forall l, CTree.bind (E := F) (interp_thread tidExec nextTId t)
      (fun x : thread_id * X =>
        CTree.bind
          (let '(nextTId0, x0) := x in step_thread fns get_val atomic nextTId0 tidExec pl (k x0)) l) ≅
    CTree.bind (interp_thread tidExec nextTId t)
      (fun '(nextTId0, x0) =>
       CTree.bind (step_thread fns get_val atomic nextTId0 tidExec pl (k x0))
         l)).
  { intros. upto_bind. reflexivity. intros [] ? <-. reflexivity. }
  setoid_rewrite <- H1. rewrite <- H0.
  eapply sbisim_clo_bind. apply step_thread_bind_pure; auto.
  intros ((? & ?) & ?) ((? & ?) & ?) ?. cbn in H2. destruct H2 as ((<- & <-) & ?).
  rewrite !sb_guard. now apply interleave_sbisim.
Qed.

Lemma step_thread_is_stuck : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X)) tidExec t,
  is_stuck t ->
  is_stuck (step_thread (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl t).
Proof.
  intros. intros ???.
  do 3 red in H0. remember (observe (step_thread _ _ _ _ _ _ _)) as os.
  genobs u ou.
  assert (step_thread fns get_val atomic nextTId tidExec pl t ≅ go os).
  { now rewrite Heqos, <- ctree_eta. } clear Heqos.
  revert t H H1. induction H0; intros.
  - apply step_thread_brD_inv with (x := x) in H1 as (? & ? & ? & -> & ?).
    apply IHtrans_ with (t := x1 x); auto.
    { intros ???. eapply trans_br in H3. rewrite <- H1 in H3. now apply H in H3. reflexivity. }
    now rewrite <- ctree_eta, H2.
  - apply step_thread_guard_inv in H1 as (? & ? & ?).
    apply IHtrans_ with (t := x); auto.
    { intros ???. eapply trans_guard in H3. rewrite <- H1 in H3. now apply H in H3. }
    now rewrite <- ctree_eta, H2.
  - apply step_thread_step_inv in H1 as (? & ? & ?).
    eapply H0. rewrite H1. now unshelve etrans.
  - apply step_thread_vis_inv in H1 as [(? & ? & -> & ? & ?) | (? & ? & -> & ? & ?)].
    + eapply H0. rewrite H1. now unshelve etrans.
    + eapply H0. rewrite H1. now unshelve etrans.
  - destruct r as ((? & ?) & ?). eapply step_thread_ret_inv in H1 as [| [|]].
    + destruct H0 as (? & ? & _).
      eapply H. rewrite H0. etrans.
    + destruct H0 as (? & ? & ? & ? & ? & ? & ?). eapply H. rewrite H0. now unshelve etrans.
    + destruct H0 as (? & ? & ? & ?). eapply H. rewrite H0. now unshelve etrans.
Qed.

Lemma step_interleave_is_stuck : forall
  fns get_val atomic nextTId (pl : TMap.t (ctree (ThreadE +' TE +' E) B X)) tidExec t,
  is_stuck t ->
  is_stuck (step_interleave (Arg := Arg) (F := F) fns get_val atomic nextTId tidExec pl t).
Proof.
  intros. unfold step_interleave.
  apply is_stuck_bind. now apply step_thread_is_stuck.
Qed.

End ThreadFacts.
