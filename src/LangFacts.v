From Coq Require Import
     String
     List
.

From ITree Require Import
     Core.Subevent
     Events.Exception.

Unset Universe Checking.

From CTree Require Import
     CTree
     Eq
     Interp.Fold
     Interp.FoldStateT
     Misc.Pure.

From Mem Require Import Utils Events Var lang.

Import ListNotations.

Open Scope list_scope.

Section interp_var.

Context {E : Type -> Type} {HasExcept : exceptE string -< E}.
Context {HasAlloc : AllocE -< E} {HasMemory : MemoryE -< E} {HasThread : @ThreadE (list value) -< E}.

#[local] Notation interp_var globals t locals := (interp_state (M := ctree E void1') (interp_var_h globals) (t : ctree (VarE +' E) void1' _) locals).

Lemma interp_repr_atom_pure :
  forall a globals locals,
  pure_finite (interp_var globals (repr_atom a) locals) \/
  interp_var globals (repr_atom a) locals ~ (Stuck : ctree E void1' (var_state * value)).
Proof.
  intros. destruct a; cbn.
  1,2: left; rewrite interp_state_trigger; cbn; typeclasses eauto.
  destruct c; cbn; try (left; rewrite interp_state_ret; typeclasses eauto).
Qed.

End interp_var.

Lemma interp_repr_atom_case :
  forall a globals locals,
  (exists v : value, forall E C `{exceptE string -< E}, interp_var (C := C) globals _ (repr_atom a) locals ~ (Ret (locals, v) : ctree E C (var_state * value))).
Proof.
  intros. unfold interp_var. destruct a; cbn.
  1,2: eexists _; intros; rewrite interp_state_trigger; cbn;
    rewrite bind_ret_l, sb_guard; reflexivity.
  destruct c; cbn; try (eexists _; intros; rewrite interp_state_ret; reflexivity).
Qed.

Lemma interp_repr_exp_case :
  forall e globals locals,
  (exists v : value, forall E C `{exceptE string -< E}, interp_var (C := C) globals _ (repr_exp e) locals ~ (Ret (locals, v) : ctree E C (var_state * value))).
Proof.
  intros. unfold interp_var. destruct e.
  - apply interp_repr_atom_case.
  - cbn.
    pose proof (interp_repr_atom_case v1 globals locals); unfold interp_var in H.
    destruct H.
    pose proof (interp_repr_atom_case v2 globals locals); unfold interp_var in H0.
    destruct H0.
    eexists. intros. rewrite interp_state_bind, H, bind_ret_l; auto.
    rewrite interp_state_bind, H0, bind_ret_l; auto. cbn. now rewrite interp_state_ret.
  - cbn.
    pose proof (interp_repr_atom_case v1 globals locals); unfold interp_var in H.
    destruct H.
    pose proof (interp_repr_atom_case v2 globals locals); unfold interp_var in H0.
    destruct H0.
    eexists. intros. rewrite interp_state_bind, H, bind_ret_l; auto.
    rewrite interp_state_bind, H0, bind_ret_l; auto. cbn. now rewrite interp_state_ret.
Qed.
