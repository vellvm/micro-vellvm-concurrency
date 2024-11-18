From Coq Require Import String List NArith ZArith.

From ExtLib Require Import Monad.

From ITree Require Import
     Indexed.Sum
     Core.Subevent
     Events.Exception
.

Unset Universe Checking.
From CTree Require Import
     CTree
     Eq
     Interp.FoldStateT.

From Mem Require Import Utils Events Var Thread Alloc Sched Pick lang SC TSO PS.

Import ListNotations.

Definition E0 := VarE +' @ThreadE (list value) +' MemoryE +' AllocE +' exceptE string.
Definition E1 := @ThreadE (list value) +' MemoryE +' AllocE +' exceptE string.
Definition E2 := AllocE +' ThreadAnnotE MemoryE +' exceptE string.
Definition E3 := ThreadAnnotE MemoryE +' exceptE string.
Definition E4 := exceptE string.

Definition Bsched := SchedC +' void1'.
Definition B_SC := PickC +' SchedC +' void1'.
Definition B_TSO := TSOFlushC +' PickC +' SchedC +' void1'.
Definition B_PS := PSMemC +' PickC +' SchedC +' DebugLogC +' ExceptC PSMem +' void1'.

Notation repr_code := (repr_code (E := E0) (B := void1')).

Definition repr_codes tl := TMap.map repr_code tl.

Definition repr_ll (p : toplevel) := repr_toplevel (E := E0) (B:= void1') p "main".

Definition wrap_threads {A} (fns : FnMap.t (ctree E0 void1' A)) :=
  FnMap.map wrap_thread fns.

Definition interp0 {A} (t : ctree E0 void1' A) g v :
    ctree E1 void1' (var_state * A) :=
  interp_var g _ t v.

Definition interp0_l {A} (tl : TMap.t (ctree E0 void1' A)) g (v : TMap.t var_state) :
    TMap.t (ctree E1 void1' (var_state * A)) :=
  NatMapFacts.map2 (fun (t : option _) (v : option _) =>
    match t, v with | Some t, Some v => Some (interp0 t g v) | _, _ => None end) tl v.

Definition interp0_l' {A} (fns : FnMap.t (list value -> ctree E0 void1' A)) g (v : FnMap.t var_state) :
    FnMap.t (list value -> ctree E1 void1' (var_state * A)) :=
  StringMapFacts.map2 (fun (t : option _) (v : option _) =>
    match t, v with | Some t, Some v => Some (fun arg => interp0 (t arg) g v) | _, _ => None end) fns v.

Definition interp0_top {A} (tl : FnMap.t (ctree E0 void1' A)) g :
    FnMap.t (list value -> ctree E1 void1' (var_state * A)) :=
  interp0_l' (wrap_threads tl) g (FnMap.map (fun f => StringMap.empty) tl).

(*Definition interp_fns fns g := (*wrap_threads*) (interp0_top (repr_definitions fns)) g.*)

Definition interp1 (fns : FnMap.t (list value -> ctree E1 void1' (var_state * value)))
  (nextTId : thread_id) (tl : TMap.t (ctree E1 void1' (var_state * value))) :
    ctree E2 Bsched nat :=
  interleave (TE := MemoryE) fns snd None nextTId tl.

Definition interp1_top (fns : FnMap.t (list value -> ctree E1 void1' (var_state * value))) :
    ctree E2 Bsched nat :=
  interleave_top fns snd (FnMap.find_or "main" (fun _ => Stuck) fns []).

Definition interp2 {A} (t : ctree E2 Bsched A) addr :
    ctree E3 Bsched (nat * A) :=
  interp_alloc _ t addr (*1%nat*).

Definition interp_common (fns : FnMap.t (ctree E0 void1' value))
  (nextTId : thread_id) (tl : TMap.t (ctree E0 void1' value)) g v addr :
    ctree E3 Bsched (nat * nat) :=
  interp2 (interp1 (interp0_top fns g) nextTId (interp0_l tl g v)) addr.

Definition interp_common_top (tl : FnMap.t (ctree E0 void1' value)) g addr :
    ctree E3 Bsched (nat * nat) :=
  interp2 (interp1_top (interp0_top tl g)) addr.

(* Initializes globals and alloc state. *)
Definition init_globals (globals : list global) :=
  (StringMapFacts.of_list (List.combine globals (List.map Z.of_nat (List.seq 1 (List.length globals)))), (List.length globals + 1)%nat).

Definition interp3_sc {A} (t : ctree E3 Bsched (nat * A)) sc :
    ctree E4 B_SC (SCMem * (nat * A)) :=
  SC.interp_mem _ t sc.

Definition interp_sc (fns : FnMap.t (ctree E0 void1' value))
  (nextTId : thread_id) (tl : TMap.t (ctree E0 void1' value)) g v addr sc :
    ctree E4 B_SC (SCMem * (nat * nat)) :=
  interp3_sc (interp_common fns nextTId tl g v addr) sc.

Definition interp_sc_top (tl : FnMap.t (ctree E0 void1' value)) g addr sc :
    ctree E4 B_SC (SCMem * (nat * nat)) :=
  interp3_sc (interp_common_top tl g addr) sc.

Definition interp_ll_sc ll : StringMap.t Z * ctree E4 B_SC (SCMem * (nat * nat)) :=
  let '(g, addr) := init_globals (snd ll) in
  (g, interp_sc_top (fst (repr_ll ll)) g addr NatMap.empty).

Definition interp_rand_sc tl g addr sc ss :=
  interp_sched handle_sched_random _
    (interp_pick handle_pick_random _ (interp_sc_top tl g addr sc) ss).

Definition interp_ll_rand_sc ll :=
  interp_rand_sc (fst (repr_ll ll)).

Definition eval_ll_rand_sc ll :=
  let '(g, addr) := init_globals (snd ll) in
  interp_rand_sc (fst (repr_ll ll)) g addr NatMap.empty 0 0%N.

Definition interp3_tso {A} (t : ctree E3 Bsched (nat * A)) sc :
    ctree E4 B_TSO (TSOMem * (nat * A)) :=
  TSO.interp_mem _ t sc.

Definition interp_tso (fns : FnMap.t (ctree E0 void1' value))
  (nextTId : thread_id) (tl : TMap.t (ctree E0 void1' value)) g v addr tso :
    ctree E4 B_TSO (TSOMem * (nat * nat)) :=
  interp3_tso (interp_common fns nextTId tl g v addr) tso.

Definition interp_tso_top (tl : FnMap.t (ctree E0 void1' value)) g addr tso :
    ctree E4 B_TSO (TSOMem * (nat * nat)) :=
  interp3_tso (interp_common_top tl g addr) tso.

Definition interp_ll_tso ll : StringMap.t Z * ctree E4 B_TSO (TSOMem * (nat * nat)) :=
  let '(g, addr) := init_globals (snd ll) in
  (g, interp_tso_top (fst (repr_ll ll)) g addr TSO.empty_mem).

Definition interp_rand_tso tl g addr tso fs ss :=
  interp_sched handle_sched_random _
    (interp_pick handle_pick_random _
      (interp_flush handle_flush_random _ (interp_tso_top tl g addr tso) fs) ss).

Definition interp_ll_rand_tso ll :=
  interp_rand_tso (fst (repr_ll ll)).

Definition eval_ll_rand_tso ll :=
  let '(g, addr) := init_globals (snd ll) in
  interp_rand_tso (fst (repr_ll ll)) g addr TSO.empty_mem 0 0 0%N.

Definition interp3_ps {A} (t : ctree E3 Bsched (nat * A)) ps :
    ctree E4 B_PS (PSMem * (nat * A)) :=
  PS.interp_mem _ t ps.

Definition interp_ps (fns : FnMap.t (ctree E0 void1' value))
  (nextTId : thread_id) (tl : TMap.t (ctree E0 void1' value)) g v addr ps :
    ctree E4 B_PS (PSMem * (nat * nat)) :=
  interp3_ps (interp_common fns nextTId tl g v addr) ps.

Definition interp_ps_top (tl : FnMap.t (ctree E0 void1' value)) g addr ps :
    ctree E4 B_PS (PSMem * (nat * nat)) :=
  interp3_ps (interp_common_top tl g addr) ps.

Definition interp_ll_ps ll : StringMap.t Z * ctree E4 B_PS (PSMem * (nat * nat)) :=
  let '(g, addr) := init_globals (snd ll) in
  (g, interp_ps_top (fst (repr_ll ll)) g addr PS.empty_mem).

Definition refine_rand_ps {X} (t : ctree E4 B_PS X) fs ss :=
  interp_sched handle_sched_random _
    (interp_pick handle_pick_random _
      (interp_view handle_view_random _ t fs) ss).

Definition interp_ll_rand_ps ll g addr ps fs ss :=
  refine_rand_ps (interp_ps_top (fst (repr_ll ll)) g addr ps) fs ss.

Definition eval_ll_rand_ps ll :=
  let '(g, addr) := init_globals (snd ll) in
  refine_rand_ps (interp_ps_top (fst (repr_ll ll)) g addr PS.empty_mem) 0 0 0%N.


Import MonadNotation.

(* Functions to recover the final values of global variables, for various memory models *)

Definition final_state {E C Mem X} read (t: ctree E C (Mem * X))
  (vars: list addr) : ctree E C (list (value)) :=
  r <- t;; Ret (List.map (fun addr => (read (fst r) addr)) vars).

Definition final_state_globals {E C Mem X} read (p: StringMap.t Z * ctree E C (Mem * X))
  (vars: list ident) : ctree E C (list value) :=
  final_state read (snd p) (List.map (fun g => Z.to_nat (StringMap.find_or g nullval (fst p))) vars).

Definition final_state_sc {E C X} (p : StringMap.t Z * ctree E C (_ * X)) vars :
  ctree E C (list value) :=
  final_state_globals (fun m addr => value_or (SC.mem_read m addr) 0) p vars.

Definition final_state_tso {E C X} (p : StringMap.t Z * ctree E C (_ * X)) vars :
  ctree E C (list value) :=
  final_state_globals (fun m addr => value_or (TSO.mem_read m O addr) 0) p vars.

Definition final_state_ps {E C X} (p : StringMap.t Z * ctree E C (_ * X)) vars :
  ctree E C (list value) :=
  final_state_globals (fun m addr => value_or (snd (PS.do_mem_read seq_cst m O addr (fst (PS.latest m addr PSRead)))) 0) p vars.


(* Proofs that the handlers for the various stages of interpretation are simple enough
   to be monad morphisms. *)

Unset Universe Checking.
From CTree Require Import Misc.Pure.

#[global] Instance pure_freeze :
  forall {E C} `{PickC -< C} o, pure_finite (@freeze E C _ o).
Proof.
  intros. destruct o; typeclasses eauto.
Qed.

#[global] Instance pure_force_def :
  forall {E C T} `{PickC -< C} `{ExceptC T -< C} o s t, pure_finite (@force_def E C T _ _ o s t).
Proof.
  intros. destruct o; try typeclasses eauto.
  cbn. apply pure_finite_br. intros [].
Qed.

#[global] Instance pure_lift_either :
  forall {E C X} `{ExceptC PSMem -< C} v, pure_finite (@lift_either E C X _ v).
Proof.
  intros. destruct v as [[] |]; try typeclasses eauto. cbn.
  apply pure_finite_br. intros [].
Qed.

#[global] Instance is_simple_handle_var :
  forall {E C X} g (e : VarE X) st, is_simple (@handle_var g E C X e st).
Proof.
  intros. unfold handle_var.
  destruct e; typeclasses eauto.
Qed.

#[global] Instance is_simple_interp_var_h :
  forall {E C X} g (e : (VarE +' E) X) st, is_simple (@interp_var_h g E C X e st).
Proof.
  intros.
  destruct e; typeclasses eauto.
Qed.

#[global] Instance is_simple_handle_thread :
  forall {Arg E C X} `{MemoryE -< E} (e : ThreadE X) tidExec n, is_simple (@handle_thread Arg E C tidExec X e n).
Proof.
  intros. destruct e; typeclasses eauto.
Qed.

#[global] Instance is_simple_interp_thread_h :
  forall {Arg E TE F C X} `{E -< F} `{ThreadAnnotE TE -< F} (e : (ThreadE +' TE +' E) X) tid n,
  is_simple (@interp_thread_h Arg E TE F C _ _ tid X e n).
Proof.
  intros. destruct e as [| []]; [destruct t | |]; try typeclasses eauto.
Qed.

#[global] Instance is_simple_handle_alloc_simple :
  forall {E C X} (e : AllocE X) n, is_simple (@handle_alloc_simple E C X e n).
Proof.
  intros. destruct e; typeclasses eauto.
Qed.

#[global] Instance is_simple_interp_alloc_h :
  forall {E F C X} `{E -< F} (e : (AllocE +' E) X) n,
  is_simple (@interp_alloc_h E F C _ X e n).
Proof.
  intros. destruct e; typeclasses eauto.
Qed.

#[global] Instance is_simple_handle_ps :
  forall {E C X} `{PSMemC -< C} `{SchedC -< C} `{PickC -< C} `{ExceptC PSMem -< C} `{DebugLogC -< C} (e : ThreadAnnotE MemoryE X) s,
  is_simple (@handle_mem E C _ _ _ _ _ X e s).
Proof.
  intros. destruct e. destruct e.
  - cbn. right. intros.
    destruct (is_not_atomic o). {
      apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
      inv_trans. eexists. now subs.
    }
    apply trans_bind_pure in H4 as ([] & _ & ?). 2: typeclasses eauto.
    apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
    apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
    inv_trans. eexists. now subs.
  - cbn. right. intros.
    apply trans_bind_pure in H4 as ([] & _ & ?). 2: typeclasses eauto.
    apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
    inv_trans. eexists. now subs.
  - cbn. right. intros.
    apply trans_bind_pure in H4 as ([] & _ & ?). 2: typeclasses eauto.
    apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
    apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
    apply trans_bind_pure in H4 as (? & _ & ?). 2: typeclasses eauto.
    inv_trans. eexists. now subs.
  - cbn. right. intros. inv_trans. eexists. now subs.
Qed.
