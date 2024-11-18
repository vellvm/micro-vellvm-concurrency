From Coq Require Import
     Classes.RelationPairs
     ZArith
     String
     List
     Lia
.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.HeterogeneousRelations
     Core.Subevent
     Events.Exception.

Unset Universe Checking.
From CTree Require Import
     CTree
     Eq
     Eq.SSimAlt
     Eq.SBisimAlt
     Interp.Fold
     Interp.FoldStateT
     Misc.Pure.

From Mem Require Import Utils Events Sched Thread ThreadFacts Alloc Var lang LangFacts Interp.

Import MonadNotation.
Import ListNotations.

Open Scope list_scope.


(* A CFG mid-execution has a current block and the rest of the graph. *)
Definition ecfg := (block * ocfg)%type.

(* A thread can be running its main task, or be in its initialization or cleanup phase. *)

Variant task_status :=
| Init (task cleanup : value -> ecfg)
| Task (cleanup : value -> ecfg)
| Cleanup.

Definition codes := TMap.t (ecfg * task_status).

Definition repr_ecfg (e : ecfg) : ctree E0 void1' value :=
  r <- repr_block (fst e);;
  match r with
  | inl bid => Guard (repr_cfg (mkCFG bid (snd e) []))
  | inr v => Ret v
  end.

Definition repr_task_k (tk : task_status) r :=
  match tk with
  | Init task cleanup =>
    trigger NewFrame;;
    trigger Yield;;
    r <- repr_ecfg (task r);;
    trigger NewFrame;;
    trigger Yield;;
    repr_ecfg (cleanup r)
  | Task cleanup =>
    trigger NewFrame;;
    trigger Yield;;
    repr_ecfg (cleanup r)
  | Cleanup => Ret r
  end.

Definition repr_task (tk : ecfg * task_status) :=
  r <- repr_ecfg (fst tk);;
  repr_task_k (snd tk) r.

Lemma repr_ecfg_instr : forall bid instr l term c,
  repr_ecfg (mk_block bid (instr::l) term, c) ≅ repr_instr' instr;; repr_ecfg (mk_block bid l term, c).
Proof.
  intros. cbn. rewrite !bind_bind. upto_bind_eq. intros. upto_bind_eq. intros.
  rewrite !bind_bind. upto_bind_eq. intros.
  rewrite !bind_ret_l. reflexivity.
Qed.

Lemma repr_task_instr : forall bid instr l term c tk,
  repr_task (mk_block bid (instr::l) term, c, tk) ≅ repr_instr' instr;; repr_task (mk_block bid l term, c, tk).
Proof.
  intros. cbn -[repr_ecfg].
  rewrite repr_ecfg_instr. cbn -[repr_ecfg].
  rewrite !bind_bind. reflexivity.
Qed.

Lemma repr_ecfg_term : forall bid term c,
  repr_ecfg (mk_block bid [] term, c) ≅
  r <- repr_term term;;
  match r with
  | inl bid =>
    Guard (match find_block c bid with
    | Some b => trigger Yield;; repr_ecfg (b, c)
    | None => throw ("Can't find block in repr_cfg " ++ bid)%string
    end)
  | inr v => Ret v
  end.
Proof.
  intros. cbn. rewrite !bind_bind. rewrite !bind_ret_l. upto_bind_eq. intros.
  destruct x. cbn. unfold repr_ocfg. rewrite unfold_iter.
  rewrite bind_bind.
  destruct (find_block c s) eqn:?.
  - step. constructor.
    setoid_rewrite bind_bind.
    rewrite !bind_trigger. step. constructor. intros _.
    cbn. rewrite !bind_bind.
    upto_bind_eq. intros.
    rewrite !bind_ret_l, bind_bind.
    upto_bind_eq. destruct x0.
    + rewrite bind_ret_l. rewrite bind_guard.
      reflexivity.
    + rewrite !bind_ret_l. reflexivity.
  - step. constructor.
    rewrite !bind_ret_l. reflexivity.
  - reflexivity.
Qed.

Lemma repr_task_term : forall bid term c tk,
  repr_task (mk_block bid [] term, c, tk) ≅
  r <- repr_term term;;
  match r with
  | inl bid =>
    Guard (match find_block c bid with
    | Some b => trigger Yield;; repr_task (b, c, tk)
    | None => throw ("Can't find block in repr_cfg " ++ bid)%string
    end)
  | inr v => repr_task_k tk v
  end.
Proof.
  intros. cbn -[repr_ecfg append].
  rewrite repr_ecfg_term. cbn -[repr_ecfg append].
  rewrite !bind_bind.
  upto_bind_eq. destruct x.
  2: now rewrite bind_ret_l.
  rewrite bind_guard.
  step. constructor.
  destruct (find_block c s).
  2: { unfold throw. rewrite bind_vis. step. constructor. intros []. }
  rewrite bind_bind. reflexivity.
Qed.

Lemma repr_task_k_init : forall task cleanup r,
  repr_task_k (Init task cleanup) r ≅
  trigger NewFrame;;
  trigger Yield;;
  repr_task (task r, Task cleanup).
Proof.
  intros. reflexivity.
Qed.

Lemma repr_task_k_task : forall cleanup r,
  repr_task_k (Task cleanup) r ≅
  trigger NewFrame;;
  trigger Yield;;
  repr_task (cleanup r, Cleanup).
Proof.
  intros. cbn -[repr_ecfg].
  upto_bind_eq. intros. upto_bind_eq. intros.
  now rewrite bind_ret_r.
Qed.

Definition repr_codes (c : codes) : TMap.t (ctree E0 void1' value) :=
  TMap.map (fun ll => repr_task ll) c.

Lemma find_interp0_l {A} : forall (p : TMap.t (ctree E0 void1' A)) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  forall tid,
    TMap.find tid (interp0_l p g vars) =
    match TMap.find tid p with
    | Some p => Some (interp0 p g (TMap.find_or tid StringMap.empty vars))
    | None => None
    end.
Proof.
  intros.
  unfold interp0_l. rewrite NatMapFacts.map2_1n; auto.
  destruct (TMap.find tid p) eqn:?.
  - assert (TMap.In tid p). { apply NatMapFacts.in_find. intro. now rewrite H0 in Heqo. }
    destruct (TMap.find tid vars) eqn:?.
    + unfold TMap.find_or. setoid_rewrite Heqo0. reflexivity.
    + apply H in H0. apply NatMapFacts.in_find in H0. now apply H0 in Heqo0.
  - reflexivity.
Qed.

Lemma find_interp0_l_repr_codes : forall (p : codes) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  forall tid,
    TMap.find tid (interp0_l (repr_codes p) g vars) =
    match TMap.find tid p with
    | Some p => Some (interp0 (repr_task p) g (TMap.find_or tid StringMap.empty vars))
    | None => None
    end.
Proof.
  intros. rewrite find_interp0_l.
  2: { intros. now apply NatMapFacts.map_in_iff, H in H0. }
  unfold repr_codes. rewrite NatMapFacts.map_find.
  destruct (TMap.find tid p) eqn:?; reflexivity.
Qed.

Lemma is_empty_interp0_l {A} : forall (p : TMap.t (ctree E0 void1' A)) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.is_empty (interp0_l p g vars) = TMap.is_empty p.
Proof.
  intros. apply eq_bool_alt.
  rewrite !TMap.is_empty_spec.
  setoid_rewrite find_interp0_l; auto.
  split; intros.
  - specialize (H0 x). now destruct (TMap.find x p).
  - now rewrite H0.
Qed.

Lemma is_empty_interp0_l_repr_codes : forall (p : codes) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.is_empty (interp0_l (repr_codes p) g vars) = TMap.is_empty p.
Proof.
  intros. rewrite is_empty_interp0_l.
  2: { intros. apply NatMapFacts.map_in_iff in H0. auto. }
  apply eq_bool_alt.
  rewrite !TMap.is_empty_spec.
  unfold repr_codes. setoid_rewrite NatMapFacts.map_find.
  split; intros.
  - specialize (H0 x). now destruct (TMap.find x p).
  - now rewrite H0.
Qed.

Definition empty_block := mk_block "" [] (Return (OP_Atom 0%Z)).

Definition init_ecfg (c : cfg) (args : list value) : ecfg :=
  (mk_block "" (
    List.map
      (fun '(n, v) => ("arg" ++ String.nat2string10 n, Op (OP_Atom (EXP_Cst (CST_Integer v)))))%string
      (combine (seq 0 (List.length args)) args))
    (Jmp1 (init c)), blks c).

Definition empty_cfg := mkCFG "" [] [].

Definition fn2ecfg (f : string) fns : option (list value -> ecfg) :=
  option_map init_ecfg (StringMap.find f (StringMapFacts.of_list fns)).

Definition init_task fns f init cleanup arg : option (ecfg * task_status) :=
  init <- fn2ecfg init fns;;
  f <- fn2ecfg f fns;;
  cleanup <- fn2ecfg cleanup fns;;
  Some (init [arg], Init (fun v => f [v]) (fun v => cleanup [arg; v])).

Definition add_task tid p (vars : TMap.t (StringMap.t value)) fns f init cleanup arg :=
  match init_task fns f init cleanup arg with
  | Some tk => (TMap.add tid tk p, TMap.add tid StringMap.empty vars)
  | None => (p, vars)
  end.

Definition update_task v (tk : task_status) : option _ :=
  match tk with
  | Init task cleanup => Some (task v, Task cleanup)
  | Task cleanup => Some (cleanup v, Cleanup)
  | Cleanup => None
  end.

Definition step_instr (fns : list definition) (nextTId : nat) (p : codes) (g : var_state) (vars : TMap.t var_state) (tidExec : nat) :
  ctree E2 (SchedC +' void1') (nat * codes * (TMap.t var_state)) :=
  match TMap.find tidExec p with
  | None => Ret (nextTId, p, vars)
  (* execute the terminator *)
  | Some (mk_block bid [] term, c, tk) =>
    '(nextTId, v) <- interp_thread (F := E2) tidExec nextTId
      (interp0 (repr_term (E := E0) (B := void1') term) g (TMap.find_or tidExec StringMap.empty vars));;
    match snd v : block_id + value with
    | inl bid =>
      match find_block c bid with
      | Some b => Ret (nextTId, TMap.add tidExec (b, c, tk) p, vars)
      | None => throw ("Can't find block in repr_cfg " ++ bid)%string
      end
    | inr v => Ret (nextTId, NatMapFacts.update tidExec (fun _ => update_task v tk) p,
        match tk with Cleanup => TMap.remove tidExec vars | _ => TMap.add tidExec StringMap.empty vars end)
    end
  (* execute an instruction *)
  | Some (mk_block bid (instr::code) term, c, tk) =>
    let p' := TMap.add tidExec (mk_block bid code term, c, tk) p in
    '(nextTId', (env, _)) <-
      interp_thread (F := E2) tidExec nextTId
        (interp0 (repr_code [instr]) g (TMap.find_or tidExec StringMap.empty vars))
      ;;
    '(p', vars) <-
      match instr with
      | (reg, ThreadCreate f init cleanup arg) =>
          '(_, arg) <- interp_var (E := E2) g _ (repr_exp arg) (TMap.find_or tidExec StringMap.empty vars);;
          Ret (add_task nextTId p' vars fns f init cleanup arg)
      | _ => Ret (p', vars)
      end;;
    Ret (nextTId', p', TMap.add tidExec env vars)
  end.

Lemma add_repr_codes : forall tid g l vars e (p : codes),
  TMap.Equal
    (TMap.add tid (interp_state (interp_var_h g) (repr_task e) l) (interp0_l (repr_codes p) g vars))
    (interp0_l (repr_codes (TMap.add tid e p)) g (TMap.add tid l vars)).
Proof.
  intros. unfold interp0_l. rewrite NatMapFacts.map2_add. 2: reflexivity.
  unfold repr_codes, NatMapFacts.map2. pose proof @NatMapFacts.merge_m. rewrite <- (NatMapFacts.map_add p tid e).
  reflexivity.
Qed.

Lemma remove_repr_codes : forall tid g vars (p : codes),
  TMap.Equal
    (TMap.remove tid (interp0_l (repr_codes p) g vars))
    (interp0_l (repr_codes (TMap.remove tid p)) g (TMap.remove tid vars)).
Proof.
  intros. unfold interp0_l. rewrite NatMapFacts.map2_remove.
  unfold repr_codes, NatMapFacts.map2. pose proof @NatMapFacts.merge_m. rewrite <- (NatMapFacts.map_remove p tid).
  reflexivity.
Qed.

Ltac ctsimpl_term t :=
  match t with
  | Guard ?t => ctsimpl_term t
  | CTree.bind (Ret ?x) ?k => rewrite (bind_ret_l x k)
  | CTree.bind (Guard ?t) ?k => rewrite (bind_guard t k)
  | CTree.bind (CTree.bind ?t ?k) ?k' => rewrite (bind_bind t k k')
  | CTree.bind (CTree.map ?f ?t) ?k => rewrite (bind_map f k t)
  | CTree.bind (CTree.trigger ?e) ?k => rewrite (bind_trigger e k)
  | CTree.bind (CTree.branch ?b ?c) ?k => rewrite (bind_branch c b k)
  | CTree.bind (Vis ?e ?k) ?k' => rewrite (bind_vis e k k')
  | CTree.bind (Br ?c ?k) ?k' => rewrite (bind_br c k k')
  | CTree.bind ?t ?k => ctsimpl_term t
  | interp_state ?h (Ret ?x) ?st => rewrite (interp_state_ret h st x)
  | interp_state ?h (Vis ?e ?k) ?st => rewrite (interp_state_vis h e k st)
  | interp_state ?h (Br ?c ?k) ?st => rewrite (interp_state_br h c k st)
  | interp_state ?h (Guard ?t) ?st => rewrite (interp_state_guard h t st)
  | interp_state ?h (CTree.trigger ?e) ?st => rewrite (interp_state_trigger h e st)
  | interp_state ?h (CTree.bind ?t ?k) ?st => rewrite (interp_state_bind h t k st)
  | interp_state ?h ?t ?st => ctsimpl_term t
  | step_interleave ?fns ?get_val ?atomic ?nextTId ?tid ?tl ?t => ctsimpl_term tl || ctsimpl_term t
  | interleave ?fns ?get_val ?tidExec ?nextTId ?tl => ctsimpl_term tl
  | TMap.add ?tid ?t ?tl => ctsimpl_term t || ctsimpl_term tl
  end.

Ltac ctsimpl_one :=
  match goal with
  | |- ?t (~?L) ?u => ctsimpl_term t || ctsimpl_term u
  end.

Ltac ctsimpl :=
  repeat (ctsimpl_one; cbn).

Definition interp_fns fns g := (interp0_top (repr_definitions fns)) g.

Arguments repr_ecfg : simpl never.
Arguments repr_task : simpl never.
Arguments repr_task_k : simpl never.

Theorem step_instr_op : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg e code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, Op e) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  pose proof (interp_repr_exp_case e g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2. rewrite !H2; [| typeclasses eauto].
  ctsimpl. setoid_rewrite step_interleave_setAtomic. rewrite ?sb_guard.
  ctsimpl. rewrite ?sb_guard.
  rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_alloc : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg size code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, Alloca size) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind, !interp_state_bind.
  ctsimpl. pose proof (interp_repr_exp_case size g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v & ?). rewrite !H2; try typeclasses eauto. clear H2.
  ctsimpl.
  unfold step_interleave. rewrite unfold_step_thread. cbn. rewrite bind_vis.
  apply sb_vis. intros. ctsimpl. rewrite ?sb_guard.
  cbn. rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_load : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg o e code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, AtomicLoad o e) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  pose proof (interp_repr_exp_case e g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v & ?). rewrite !H2; try typeclasses eauto. clear H2. rewrite !bind_bind.
  unfold get_pointer. ctsimpl. cbn.
  unfold step_interleave.
  rewrite unfold_step_thread. cbn. rewrite bind_vis.
  apply sb_vis. intros.
  ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_store : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg o val ptr code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, AtomicStore o val ptr) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  pose proof (interp_repr_exp_case ptr g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v & ?). rewrite !H2; [| typeclasses eauto]. clear H2. rewrite !bind_bind.
  unfold get_pointer. ctsimpl.
  pose proof (interp_repr_exp_case val g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v' & ?). rewrite !H2; [| typeclasses eauto]. clear H2.
  ctsimpl.
  unfold step_interleave.
  rewrite unfold_step_thread. cbn. rewrite bind_vis.
  apply sb_vis. intros.
  ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_rmw : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg o op val ptr code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, AtomicRMW o op val ptr) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  pose proof (interp_repr_exp_case ptr g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v & ?). rewrite !H2; [| typeclasses eauto]. clear H2. rewrite !bind_bind.
  unfold get_pointer. ctsimpl.
  pose proof (interp_repr_exp_case val g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v' & ?). rewrite !H2; [| typeclasses eauto]. clear H2.
  ctsimpl.
  unfold step_interleave.
  rewrite unfold_step_thread. cbn. rewrite bind_vis.
  apply sb_vis. intros.
  ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_cmpxchg : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg o cmp new ptr code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, AtomicCmpXchg o cmp new ptr) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  pose proof (interp_repr_exp_case ptr g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v & ?). rewrite !H2; [| typeclasses eauto]. clear H2. rewrite !bind_bind.
  unfold get_pointer. ctsimpl.
  pose proof (interp_repr_exp_case cmp g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v' & ?). rewrite !H2; [| typeclasses eauto]. clear H2.
  ctsimpl.
  pose proof (interp_repr_exp_case new g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
  destruct H2 as (v'' & ?). rewrite !H2; [| typeclasses eauto]. clear H2.
  ctsimpl.
  unfold step_interleave.
  rewrite unfold_step_thread. cbn. rewrite bind_vis.
  apply sb_vis. intros.
  ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_fence : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg o code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, Fence o) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H0.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  unfold throw.
  ctsimpl. unfold step_interleave. rewrite unfold_step_thread. cbn.
  ctsimpl. apply sb_vis. intros.
  ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
Qed.

Lemma interp0_top_map : forall {A} fns g,
  FnMap.Equal (interp0_top fns g)
  (FnMap.map (fun fn v => (interp0 (A := A) (wrap_thread fn v) g StringMap.empty)) fns).
Proof.
  intros * ?.
  unfold interp0_top, interp0_l', StringMapFacts.map2.
  rewrite StringMapFacts.merge_spec1mn; auto.
  2: typeclasses eauto.
  unfold wrap_threads.
  rewrite !StringMapFacts.map_find.
  destruct (StringMap.find y _) eqn:?; auto.
Qed.

Arguments StringMap.find : simpl never.
Arguments StringMap.find_or : simpl never.
Arguments StringMapFacts.of_list : simpl never.

Lemma repr_definitions_map : forall fns,
  StringMap.Equal
    (repr_definitions fns)
    (StringMap.map (repr_cfg (E := E0) (B := void1')) (StringMapFacts.of_list fns)).
Proof.
  intros ??. unfold repr_definitions.
  induction fns.
  - cbn. reflexivity.
  - cbn. rewrite StringMapFacts.map_find. unfold StringMapFacts.of_list. cbn.
    unfold StringMapFacts.uncurry at 1 3. destruct a. cbn.
    destruct (String_as_OT.eq_dec y f).
    + subst. rewrite !StringMapFacts.add_eq_o; auto.
    + rewrite !StringMapFacts.add_neq_o; auto. setoid_rewrite IHfns.
      rewrite StringMapFacts.map_find. reflexivity.
Qed.

Lemma repr_ecfg_repr_cfg : forall cfg args,
  repr_ecfg (init_ecfg cfg args) ~ (wrap_thread (repr_cfg cfg) args : ctree E0 void1' value).
Proof.
  intros. unfold repr_ecfg, init_ecfg, repr_cfg.
  unfold repr_ocfg. cbn -[append String.nat2string10]. repeat ctsimpl_one.
  apply sbisim_clo_bind_eq.
  - unfold repr_instr'.
    generalize 0%nat.
    induction args; intro.
    + reflexivity.
    + cbn -[append String.nat2string10].
      repeat ctsimpl_one. apply sb_vis. intros _.
      repeat ctsimpl_one. apply sb_vis. intros [].
      apply sbisim_clo_bind_eq. apply IHargs. reflexivity.
  - intros _. repeat ctsimpl_one. rewrite ?sb_guard. reflexivity.
Qed.

#[global] Instance wrap_thread_sbisim {E B X} `{ThreadE -< E} `{VarE -< E} `{B0 -< B} :
  Proper (sbisim eq ==> eq ==> sbisim eq) (@wrap_thread E B X _ _).
Proof.
  cbn -[append String.nat2string10]. intros. subst.
  apply sbisim_clo_bind_eq. reflexivity. intros _. apply H2.
Qed.

Lemma option_map_none {A B} : forall (o : option A) (f : A -> B),
  option_map f o = None ->
  o = None.
Proof.
  intros. now destruct o.
Qed.

Lemma option_none_iff_some : forall {A B} (o : option A) (o' : option B) x,
  (o = None <-> o' = None) ->
  o = Some x ->
  exists y, o' = Some y.
Proof.
  intros. subst. destruct o'.
  - eauto.
  - now pose proof (proj2 H eq_refl).
Qed.

Lemma find_interp0_top : forall fns fn args g,
  option_rel (sbisim eq)
    (option_map (fun fn => fn args) (FnMap.find fn (interp0_top (repr_definitions fns) g)))
    (option_map (fun fn => interp0 (repr_ecfg (fn args)) g StringMap.empty) (fn2ecfg fn fns)).
Proof.
  intros. pose proof (interp0_top_map (repr_definitions fns) g).
  unfold interp0, interp_var.
  unfold fn2ecfg, init_ecfg.
  rewrite interp0_top_map.
  rewrite StringMapFacts.map_find.
  rewrite repr_definitions_map, StringMapFacts.map_find.
  cbn -[append String.nat2string10].
  destruct (FnMap.find fn (StringMapFacts.of_list fns)) eqn:?.
  2: auto.
  cbn -[append String.nat2string10].
  apply interp_state_sbisim_eq; auto. 1: typeclasses eauto.
  setoid_rewrite repr_ecfg_repr_cfg.
  reflexivity.
Qed.

Lemma interp0_top_fn2ecfg : forall fns fn g,
  FnMap.find fn (interp0_top (repr_definitions fns) g) = None <->
  fn2ecfg fn fns = None.
Proof.
  intros.
  pose proof (find_interp0_top fns fn [] g).
  split; intro; rewrite H0 in H.
  - now destruct (fn2ecfg fn fns).
  - now destruct (FnMap.find _ _) eqn:?.
Qed.

#[global] Instance interp0_l_Equal : forall {A} tl g,
  Proper ((TMap.Equal (elt := _)) ==> TMap.Equal1 (equ eq)) (interp0_l (A := A) tl g).
Proof.
  cbn. intros. intro. unfold interp0_l. rewrite !NatMapFacts.map2_1n; auto.
  destruct (TMap.find y0 tl) eqn:?; auto.
  rewrite H. reflexivity.
Qed.

Lemma init_task_build_thread_ctree : forall fns g fn init cleanup v',
  option_rel (sbisim eq)
    (option_map (fun tk => interp_state (MM := @Monad_ctree E1 void1') (interp_var_h g)
      (repr_task tk) StringMap.empty) (init_task fns fn init cleanup v'))
    (build_thread_ctree (interp_fns fns g) snd fn init cleanup [v']).
Proof.
  intros. unfold init_task.
  unfold build_thread_ctree.
  unfold repr_task, repr_task_k. cbn -[bind].
  unfold interp_fns.
  destruct (fn2ecfg init fns) eqn:?.
  2: { rewrite <- interp0_top_fn2ecfg in Heqo. rewrite Heqo. auto. }
  eapply option_none_iff_some in Heqo as ?. destruct H. 2: symmetry; apply interp0_top_fn2ecfg.
  cbn. rewrite H.
  destruct (fn2ecfg fn fns) eqn:?.
  2: { rewrite <- interp0_top_fn2ecfg in Heqo0. rewrite Heqo0. auto. }
  eapply option_none_iff_some in Heqo0 as ?. destruct H0. 2: symmetry; apply interp0_top_fn2ecfg.
  rewrite H0.
  destruct (fn2ecfg cleanup fns) eqn:?.
  2: { rewrite <- interp0_top_fn2ecfg in Heqo1. rewrite Heqo1. auto. }
  eapply option_none_iff_some in Heqo1 as ?. destruct H1. 2: symmetry; apply interp0_top_fn2ecfg.
  rewrite H1.
  cbn.
  ctsimpl. apply sbisim_clo_bind_eq. {
    pose proof (find_interp0_top fns init [v'] g).
    rewrite Heqo, H in H2. cbn in H2. now rewrite H2.
  }
  intros. ctsimpl. rewrite ?sb_guard.
  apply sb_vis. intros []. ctsimpl. rewrite ?sb_guard.
  apply sbisim_clo_bind_eq. {
    pose proof (find_interp0_top fns fn [snd x2] g).
    rewrite Heqo0, H0 in H2. cbn in H2. now rewrite H2.
  }
  intros. ctsimpl. rewrite ?sb_guard.
  apply sb_vis. intros []. ctsimpl. rewrite ?sb_guard.
  pose proof (find_interp0_top fns cleanup [v'; snd x3] g).
  rewrite Heqo1, H1 in H2. cbn in H2. now rewrite H2.
Qed.

Theorem step_instr_threadcreate : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid reg fn init cleanup arg code term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  (forall tid, (tid >= nextTId)%nat -> TMap.find tid p = None) ->
  TMap.find tidExec p = Some (mk_block bid ((reg, ThreadCreate fn init cleanup arg) :: code) term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H2.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H1; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite repr_task_instr. cbn.
  rewrite H1.
  rewrite !bind_bind. cbn.
  rewrite !interp_state_bind.
  ctsimpl. rewrite ?sb_guard.
  pose proof (interp_repr_exp_case arg g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H3.
  destruct H3 as (v' & ?). rewrite !(H3 _ void1'); [| typeclasses eauto].
  ctsimpl. rewrite ?sb_guard. rewrite H3; [| typeclasses eauto]. clear H3. ctsimpl.
  unfold step_interleave. rewrite unfold_step_thread. cbn. ctsimpl. rewrite ?sb_guard.
  unfold add_thread_ctree, add_task.
  pose proof (init_task_build_thread_ctree fns g fn init cleanup v').
  destruct (build_thread_ctree _ _ _ _ _ _) eqn:?, (init_task _ _ _ _ _) eqn:?; try now inv H3.
  2: { ctsimpl. rewrite add_repr_codes. reflexivity. }
  ctsimpl. unfold interp1.
  pose proof @NatMapFacts.add_m.
  rewrite NatMapFacts.add_add_2.
  2: { intros ->. specialize (H0 nextTId). rewrite H0 in H1. discriminate. lia. }
  setoid_rewrite NatMapFacts.add_add_2 with (x := tidExec); auto.
  2: { intros ->. specialize (H0 nextTId). rewrite H0 in H1. discriminate. lia. }
  cbn in H3. rewrite <- H3.
  rewrite <- add_repr_codes.
  apply interleave_sbisim; auto.
  apply NatMapFacts.add_m1; auto. cbn.
  eapply NatMapFacts.Equal1_subrelation. apply eq_subrelation. typeclasses eauto.
  apply NatMapFacts.Equal_Equal1. rewrite add_repr_codes. reflexivity.
Qed.

Theorem step_instr_term : forall (fns : list definition) nextTId tidExec (p : codes) g vars bid term c tk t,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  TMap.find tidExec p = Some (mk_block bid [] term, c, tk) ->
  TMap.find_or tidExec Stuck (interp0_l (repr_codes p) g vars) ≅ t ->
  step_interleave (interp_fns fns g) snd false nextTId tidExec (interp0_l (repr_codes p) g vars) t ~
  (CTree.bind
    (step_instr fns nextTId p g vars tidExec)
    (fun '(nextTId, p', vars) => interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars))
  : ctree E2 (SchedC +' void1') nat).
Proof.
  intros. cbn. rewrite <- H1.
  unfold TMap.find_or at 1. rewrite find_interp0_l_repr_codes, H0; auto.
  unfold step_instr. unfold interp0, interp_var, interp_thread.
  cbn. rewrite H0. rewrite repr_task_term. cbn.
  ctsimpl.
  destruct term; cbn.
  - (* Return *)
    ctsimpl.
    pose proof (interp_repr_exp_case v g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
    destruct H2 as (v' & ?). rewrite !H2; [| typeclasses eauto]. clear H2.
    ctsimpl. destruct tk.
    + cbn. rewrite repr_task_k_init.
      cbn. ctsimpl. rewrite ?sb_guard.
      unfold interp1, step_interleave. rewrite unfold_step_thread. cbn.
      ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
    + cbn. rewrite repr_task_k_task.
      cbn. ctsimpl. rewrite ?sb_guard.
      unfold interp1, step_interleave. rewrite unfold_step_thread. cbn.
      ctsimpl. rewrite ?sb_guard. rewrite add_repr_codes. reflexivity.
    + unfold repr_task_k. cbn. unfold step_interleave. rewrite unfold_step_thread. cbn. ctsimpl.
      rewrite sb_guard. rewrite remove_repr_codes. reflexivity.
  - (* Jmp1 *)
    ctsimpl. rewrite ?sb_guard.
    destruct (find_block c br) eqn:?.
    + ctsimpl.
      unfold step_interleave. rewrite unfold_step_thread. cbn.
      setoid_rewrite bind_ret_l. rewrite ?sb_guard.
      ctsimpl. rewrite ?sb_guard.
      rewrite add_repr_codes. apply equ_sbisim_subrelation. typeclasses eauto.
      unfold interp1, interp_fns. apply interleave_equ; auto. apply interp0_l_Equal.
      apply NatMapFacts.add_find_or. apply H. apply NatMapFacts.in_find. now rewrite H0.
    + unfold throw. step. apply is_stuck_sb.
      apply step_interleave_is_stuck.
      rewrite interp_state_vis. cbn. rewrite bind_bind, bind_trigger.
      intros ???. now inv_trans.
      apply is_stuck_bind. intros ???. unfold throw in H2. now inv_trans.
  - (* Jmp2 *)
    ctsimpl.
    pose proof (interp_repr_exp_case v g (TMap.find_or tidExec StringMap.empty vars)); unfold interp_var in H2.
    destruct H2 as (v' & ?). rewrite !H2; [| typeclasses eauto]. clear H2. ctsimpl. rewrite ?sb_guard.
    destruct (find_block c _) eqn:?.
    + ctsimpl.
      unfold step_interleave. rewrite unfold_step_thread. cbn. setoid_rewrite bind_ret_l. rewrite ?sb_guard.
      ctsimpl. rewrite ?sb_guard.
      rewrite add_repr_codes. apply equ_sbisim_subrelation. typeclasses eauto.
      unfold interp_fns, interp1. apply interleave_equ; auto. apply interp0_l_Equal.
      apply NatMapFacts.add_find_or. apply H. apply NatMapFacts.in_find. now rewrite H0.
    + unfold throw. step. apply is_stuck_sb.
      apply step_interleave_is_stuck.
      rewrite interp_state_vis. cbn. rewrite bind_bind, bind_trigger.
      intros ???. now inv_trans.
      apply is_stuck_bind. intros ???. unfold throw in H2. now inv_trans.
Qed.

Lemma interp0_l_In {A} : forall (p : TMap.t (ctree E0 void1' A)) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  forall tid,
    TMap.In tid (interp0_l p g vars) <->
    TMap.In tid p.
Proof.
  intros. split; intro.
  - apply TMap.merge_spec2 in H0 as ?.
    apply NatMapFacts.in_find. intro. apply NatMapFacts.in_find in H0; auto.
    apply H0.
    eapply TMap.merge_spec1 in H1 as (? & ? & ?).
    unfold interp0_l, NatMapFacts.map2. rewrite H3.
    destruct (TMap.find tid p) eqn:?; auto.
    destruct (TMap.find tid vars) eqn:?; auto. discriminate.
  - eapply or_introl in H0 as ?. eapply TMap.merge_spec1 in H1 as (? & -> & ?).
    apply NatMapFacts.in_find. intro.
    unfold interp0_l, NatMapFacts.map2 in H2. rewrite H1 in H2.
    apply NatMapFacts.in_find in H0 as ?.
    destruct (TMap.find tid p) eqn:?; auto.
    destruct (TMap.find tid vars) eqn:?; auto. discriminate.
    apply H in H0. apply NatMapFacts.in_find in H0. now apply H0.
Qed.

Lemma interp0_l_repr_code_keys : forall (p : codes) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
   TMap.keys (interp0_l (repr_codes p) g vars) = TMap.keys p.
Proof.
  intros.
  apply NatMapFacts.in_keys; auto. intros. rewrite interp0_l_In.
  - apply NatMapFacts.map_in_iff.
  - intros. apply NatMapFacts.map_in_iff in H0. now apply H.
Qed.

Theorem step_instr_interleave : forall fns nextTId (p : codes) g vars,
  (forall tid, TMap.In tid p -> TMap.In tid vars) ->
  (forall tid, (tid >= nextTId)%nat -> TMap.find tid p = None) ->
  interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p) g vars) ~
  (if TMap.is_empty p then Ret nextTId else
    br (Sched (TMap.keys p)) (fun tid =>
      '(nextTId, p', vars) <- step_instr fns nextTId p g vars tid;;
      interp1 (interp0_top (repr_definitions fns) g) nextTId (interp0_l (repr_codes p') g vars)
  ) : ctree E2 (SchedC +' void1') nat).
Proof.
  cbn. intros * Hvars Hn.
  unfold interp1.
  rewrite interleave_step_interleave.
  destruct (TMap.is_empty _) eqn:Heqb; rewrite is_empty_interp0_l_repr_codes in Heqb; auto.
  { rewrite Heqb. reflexivity. }
  rewrite Heqb. ctsimpl.
  setoid_rewrite interp0_l_repr_code_keys; [| auto].
  apply sb_br_id. intros tidExec. rewrite bind_ret_l.
  destruct (TMap.find tidExec (interp0_l (repr_codes p) g vars)) eqn:?.
  2: {
    setoid_rewrite Heqo.
    unfold step_instr.
    rewrite find_interp0_l_repr_codes in Heqo.
    destruct (TMap.find tidExec p); [discriminate |].
    2: apply Hvars.
    ctsimpl. rewrite ?sb_guard. reflexivity.
  }
  setoid_rewrite Heqo.
  rewrite find_interp0_l_repr_codes in Heqo; auto.
  destruct (TMap.find tidExec p) eqn:?; [| discriminate]. inv Heqo.
  destruct p0. destruct e. destruct b. destruct blk_code. {
    (* terminator *)
    setoid_rewrite step_instr_term; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  }
  destruct p0 as (? & []).
  + (* Op *)
    setoid_rewrite step_instr_op; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* Alloca *)
    setoid_rewrite step_instr_alloc; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* AtomicLoad *)
    setoid_rewrite step_instr_load; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* AtomicStore *)
    setoid_rewrite step_instr_store; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* AtomicRMW *)
    setoid_rewrite step_instr_rmw; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* AtomicCmpXchg *)
    setoid_rewrite step_instr_cmpxchg; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* Fence *)
    setoid_rewrite step_instr_fence; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
  + (* ThreadCreate *)
    setoid_rewrite step_instr_threadcreate; auto.
    apply Heqo0.
    unfold TMap.find_or at 1; rewrite find_interp0_l_repr_codes, Heqo0; auto.
Qed.
