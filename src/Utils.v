From Coq Require Import
     Classes.RelationPairs
     List
     NArith.
From ExtLib Require Import Monad.
From Coinduction Require Import all.
From ITree Require Import
     Basics.Basics
     Core.Subevent
     Events.Exception.
From CTree Require Import
     CTree
     Eq
     Eq.Epsilon
     Eq.SBisimAlt.

From Mem Require Export Maps.

Import MonadNotation.
Import ListNotations.
Import CoindNotations.

#[global] Arguments RelCompFun _ _ _ _ /.
#[global] Arguments RelProd _ _ _ _ / _ _.

Lemma option_map_none {A B} : forall (o : option A) (f : A -> B),
  option_map f o = None ->
  o = None.
Proof.
  intros. now destruct o.
Qed.

Definition option_sum {A} (o : option A) :=
  match o with
  | Some a => inr a
  | None => inl tt
  end.

Lemma app_cons_app_app {A} a (l1 l2 : list A) :
  l1 ++ a :: l2 = (l1 ++ [a]) ++ l2.
Proof.
  induction l1.
  - reflexivity.
  - cbn. rewrite IHl1. reflexivity.
Qed.

Lemma split_cons {A B} : forall (l : list (A * B)) x, split (x :: l) = (fst x :: fst (split l), snd x :: snd (split l)).
Proof.
  intros. destruct x. cbn. now destruct (split l).
Qed.

Lemma fst_split_map : forall {A B} (l : list (A * B)),
  fst (split l) = map fst l.
Proof.
  intros. induction l.
  - reflexivity.
  - destruct a. rewrite split_cons, IHl. reflexivity.
Qed.

#[global] Instance Symmetric_respectful : forall {A B} (R : relation A) (R' : relation B),
  Symmetric R ->
  Symmetric R' ->
  Symmetric (R ==> R').
Proof.
  intros **. cbn. intros. auto.
Qed.

#[global] Instance Transitive_respectful_eq :
  forall X Y (R : relation Y), Transitive R ->
  Transitive (@eq X ==> R).
Proof.
  repeat intro. subst. transitivity (y y0).
  now apply H0. now apply H1.
Qed.

#[global] Instance Symmetric_respectful_eq :
  forall X Y (R : relation Y), Symmetric R ->
  Symmetric (@eq X ==> R).
Proof.
  repeat intro. symmetry. now apply H0.
Qed.

#[global] Instance pointwise_relation_respectful :
  forall X Y (R : relation Y),
  subrelation (eq ==> R) (pointwise_relation X R).
Proof.
  unfold subrelation. cbn. auto.
Qed.


Open Scope monad_scope.

(* Pseudo-random number in [0,max) *)
Definition rand (seed max: N) : N * N :=
  (N.modulo (seed * 1103515245 + 12345) (2 ^ 64), N.modulo (N.div seed 65536) max)%N.

(*Definition alist_find_or [K : Type] [R : K -> K -> Prop] (RD_K : RelDec R) [V : Type] (k : K) (m : alist K V) (d : V) : V :=
  match alist_find RD_K k m with
  | Some v => v
  | None => d
  end.*)

(* from vellvm. *)
Definition map_monad {m : Type -> Type} {H : Monad m} {A B} (f:A -> m B) : list A -> m (list B) :=
  fix loop l :=
    match l with
    | [] => ret []
    | a::l' =>
      b <- f a ;;
      bs <- loop l' ;;
      ret (b::bs)
    end.

(* from vellvm *)
Definition map_monad_ {m : Type -> Type} {H : Monad m} {A}
  (f: A -> m unit) (l: list A): m unit :=
  map_monad f l;; ret tt.

(* adapted from InteractionTrees. *)
Definition throw {Err : Type} {E C : Type -> Type} `{exceptE Err -< E} {X}
           (e : Err)
  : ctree E C X
  := vis (Throw e) (fun v : void => match v with end).

(* lemmas for CTrees *)

Lemma st_guard : forall E C A (t t' : ctree E C A) (R : Chain (sb eq)), `R t t' -> `R t (Guard t').
Proof.
  intros. rewrite sb_guard. apply H.
Qed.

Ltac sb_guard :=
    (*rewrite ?brD1_guard;*)
    match goal with
    | |- context [ Guard ?t ~ _ ] => transitivity t; [ apply sb_guard |]
    | |- context [ _ ~ Guard ?t ] => transitivity t; [| symmetry; apply sb_guard ]
    | |- context [ _ _ (Guard _) _ ] => symmetry; apply st_guard; symmetry
    | |- context [ _ _ _ (Guard _) ] => apply st_guard
    end.

Variant void1' : Type -> Prop := .

Lemma epsilon_det_guard : forall {E B X} `{B1 -< B} (t : ctree E B X),
  epsilon_det (Guard t) t.
Proof.
  intros. eright; auto.
Qed.

#[global] Instance equ_sbisim_subrelation_gen {E B X R} `{HasB0 : B0 -< B} :
   subrelation (@equ E B X X R) (sbisim (lift_val_rel R)).
Proof.
  red. intros. rewrite sbisim_sbisim'. red.
  revert x y H. coinduction CR CH. intros.
  rewrite (ctree_eta x), (ctree_eta y) in H |- *. destruct (observe x) eqn:?, (observe y) eqn:?; inv_equ.
  - apply step_sbt'_ret. now constructor.
  - apply sb'_stuck.
  - apply step_sb'_step; auto. constructor; etrans.
  - apply step_sb'_guard; auto.
  - apply step_sb'_vis_id. intros. split; auto. constructor; etrans.
  - apply step_sb'_br_id; auto.
Qed.
