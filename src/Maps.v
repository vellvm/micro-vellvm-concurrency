From Coq Require Import Classes.RelationPairs.
From MMaps Require Export Utils MMaps.
From ITree Require Import Basics.HeterogeneousRelations. (* for option_rel *)

Definition is_none {A} (o : option A) :=
  match o with
  | Some _ => false
  | None => true
  end.

Definition value_or {A} (o : option A) d :=
  match o with
  | Some v => v
  | None => d
  end.

Lemma value_or_eq {A} :
  forall (o : option A) d,
  (forall v, o = Some v -> v = d) ->
  value_or o d = d.
Proof.
  intros. destruct o.
  - now apply H.
  - reflexivity.
Qed.

#[global] Instance value_or_option_rel {A} {R : relation A} :
  Proper (option_rel R ==> R ==> R) value_or.
Proof.
  now intros [] [].
Qed.

#[global] Instance Reflexive_option_rel {X} (R : relation X) :
  Reflexive R -> Reflexive (option_rel R).
Proof.
  red. intros ? []; auto.
Qed.

#[global] Instance Symmetric_option_rel {X} (R : relation X) :
  Symmetric R -> Symmetric (option_rel R).
Proof.
  red. intros ? [] []; auto.
Qed.

#[global] Instance Transitive_option_rel {X} (R : relation X) :
  Transitive R -> Transitive (option_rel R).
Proof.
  red. intros ? [] [] [] ??; eauto. destruct H0.
Qed.

#[global] Instance option_map_proper {A B} {R : relation A} {R' : relation B} :
  Proper ((R ==> R') ==> option_rel R ==> option_rel R') (@option_map A B).
Proof.
  intros ??????. destruct x0, y0; auto. cbn.
  now apply H in H0.
Qed.

#[global] Instance option_rel_eq_sub : forall X, @subrelation (option X) (option_rel Logic.eq) Logic.eq.
Proof.
  intros. apply option_rel_eq.
Qed.

Lemma option_rel_subrelation {X} (R R' : relation X) :
  subrelation R R' ->
  subrelation (option_rel R) (option_rel R').
Proof.
  red. destruct x, y; auto.
Qed.

Module Type ExtMMaps (K : OrderedType).
  Include (S K).
  Definition find_or {elt} (x : key) (v : elt) m :=
    value_or (find x m) v.

  Definition keys {elt} (m : t elt) := List.map fst (bindings m).

  Definition Equal1 {elt} R (m m':t elt) := forall y, option_rel R (find y m) (find y m').

  Definition Equal1d {elt} R d (m m':t elt) : Prop := forall y, R (find_or y d m) (find_or y d m').
End ExtMMaps.

Module ExtMMap (K : OrderedType) (M : S K) <: ExtMMaps K.
  Include M.
  Definition find_or {elt} (x : key) (v : elt) m :=
    value_or (find x m) v.

  Definition keys {elt} (m : t elt) := List.map fst (bindings m).

  Definition Equal1 {elt} R (m m':t elt) := forall y, option_rel R (find y m) (find y m').

  Definition Equal1d {elt} R d (m m':t elt) : Prop := forall y, R (find_or y d m) (find_or y d m').
End ExtMMap.

Module ExtMMapFacts (K : OrderedType) (M : ExtMMaps K).
  Include MMaps.Facts.Properties K M.
  Module Import O := MMaps.Facts.OrdProperties K M.

  Lemma in_add_eq : forall {elt} k (v : elt) m,
    M.In k (M.add k v m).
  Proof.
    intros. exists v. now apply P.add_1.
  Qed.

  Lemma in_find_some : forall {elt} k (v : elt) m,
    M.find k m = Some v ->
    M.In k m.
  Proof.
    intros. apply in_find. intro. now rewrite H in H0.
  Qed.

  Lemma add_is_empty : forall {elt} k (v : elt) m,
    M.is_empty (M.add k v m) = false.
  Proof.
    intros. apply not_true_iff_false. intro.
    rewrite M.is_empty_spec in H.
    specialize (H k). now rewrite add_eq_o in H.
  Qed.

  Lemma find_or_add_eq_o : forall {elt} (k : M.key) (v d : elt) m,
    M.find_or k d (M.add k v m) = v.
  Proof.
    intros. unfold M.find_or. now rewrite add_eq_o.
  Qed.

  Lemma find_or_add_neq_o : forall {elt} (k k' : M.key) (v d : elt) m,
    ~K.eq k' k ->
    M.find_or k d (M.add k' v m) = M.find_or k d m.
  Proof.
    intros. unfold M.find_or. rewrite add_neq_o; auto.
  Qed.

  Lemma find_or_remove_eq_o : forall {elt} (k : M.key) (d : elt) m,
    M.find_or k d (M.remove k m) = d.
  Proof.
    intros. unfold M.find_or. now rewrite remove_eq_o.
  Qed.

  Lemma find_or_remove_neq_o : forall {elt} (k k' : M.key) (d : elt) m,
    ~K.eq k' k ->
    M.find_or k d (M.remove k' m) = M.find_or k d m.
  Proof.
    intros. unfold M.find_or. rewrite remove_neq_o; auto.
  Qed.

  #[global] Instance find_or_m {elt} :
    Proper (K.eq ==> Logic.eq ==> M.Equal (elt := elt) ==> Logic.eq) M.find_or.
  Proof.
    intros ??? ?? <- ???. unfold M.find_or. now rewrite H, H0.
  Qed.

  Lemma add_find_or : forall {elt} (k : M.key) (d : elt) m,
    M.In k m ->
    M.add k (M.find_or k d m) m == m.
  Proof.
    intros. intro. destruct (K.eq_dec k y).
    2: { rewrite add_neq_o; auto. }
    rewrite add_eq_o; auto.
    unfold M.find_or. destruct (M.find k m) eqn:?.
    - erewrite find_o in Heqo; [| eassumption].
      now setoid_rewrite Heqo.
    - apply not_in_find in Heqo.
      exfalso. apply Heqo. apply H.
  Qed.

  Lemma find_find_or : forall {elt} k k' (d : elt) m m',
    M.find k m = M.find k' m' ->
    M.find_or k d m = M.find_or k' d m'.
  Proof.
    intros. unfold M.find_or. rewrite H. reflexivity.
  Qed.

  Lemma find_some_find_or : forall {elt} k (d : elt) m e,
    M.find k m = Some e ->
    M.find_or k d m = e.
  Proof.
    intros. unfold M.find_or. rewrite H. reflexivity.
  Qed.

  Lemma find_none_find_or : forall {elt} k (d : elt) m,
    M.find k m = None ->
    M.find_or k d m = d.
  Proof.
    intros. unfold M.find_or. rewrite H. reflexivity.
  Qed.

  Lemma map_find_or : forall {elt elt'} k (d : elt) m (f : elt -> elt'),
    M.find_or k (f d) (M.map f m) = f (M.find_or k d m).
  Proof.
    intros. unfold M.find_or. rewrite P.map_o.
    now destruct (M.find k m).
  Qed.

  Lemma map_find_or' : forall {elt elt'} k (d : elt) (d' : elt') m (f : elt -> elt'),
    d' = f d ->
    M.find_or k d' (M.map f m) = f (M.find_or k d m).
  Proof.
    intros. unfold M.find_or. rewrite P.map_o.
    now destruct (M.find k m).
  Qed.

  Lemma extend_find_iff : forall {elt} m m' k (e : elt),
    M.find k (extend m m') = Some e <->
    M.find k m' = Some e \/ M.find k m = Some e /\ M.find k m' = None.
  Proof.
    intros. rewrite <- !find_mapsto_iff. rewrite <- not_in_find.
    apply extend_mapsto_iff.
  Qed.

  Lemma extend_find_none_iff : forall {elt} (m m' : M.t elt) k,
    M.find k (extend m m') = None <->
    M.find k m = None /\ M.find k m' = None.
  Proof.
    intros. rewrite <- !not_in_find.
    rewrite extend_in_iff.
    split; intro.
    - split; intro; apply H; auto.
    - intro. destruct H0; now apply H.
  Qed.

  Lemma extend_find : forall {elt} (m m' : M.t elt) k,
    M.find k (extend m m') =
      match (M.find k m') with
      | Some x => Some x
      | None => M.find k m
      end.
  Proof.
    intros. destruct (M.find k m') eqn:?.
    - apply extend_find_iff. now left.
    - destruct (M.find k m) eqn:?.
      + apply extend_find_iff. now right.
      + now apply extend_find_none_iff.
  Qed.

  Lemma extend_find_or : forall {elt} m m' k (d : elt),
    M.find_or k d (extend m m') = M.find_or k (M.find_or k d m) m'.
  Proof.
    intros. unfold M.find_or.
    destruct (M.find _ _) eqn:?.
    - apply extend_find_iff in Heqo as [| []].
      + now rewrite H.
      + now rewrite H0, H.
    - apply extend_find_none_iff in Heqo as [].
      now rewrite H0, H.
  Qed.

  Lemma add_extend_l : forall {elt} m m' k (x : elt),
    extend (M.add k x m) m' == M.add k (M.find_or k x m') (extend m m').
  Proof.
    intros ** ?.
    rewrite extend_find.
    destruct (K.eq_dec k y).
    - rewrite !add_eq_o; auto. rewrite e.
      unfold M.find_or. now destruct (M.find y m').
    - rewrite !add_neq_o; auto.
      now rewrite extend_find.
  Qed.

  Lemma add_extend_r : forall {elt} m m' k (x : elt),
    extend m (M.add k x m') == M.add k x (extend m m').
  Proof.
    intros ** ?.
    rewrite extend_find.
    destruct (K.eq_dec k y).
    - rewrite !add_eq_o; auto.
    - rewrite !add_neq_o; auto.
      now rewrite extend_find.
  Qed.

  #[global] Instance Equal_equiv' {elt} : Equivalence (M.Equal (elt := elt)) := Equal_equiv.

  Lemma is_empty_Equal : forall {elt} (x y : M.t elt),
    x == y ->
    M.is_empty x = true -> M.is_empty y = true.
  Proof.
    intros. now rewrite <- H, H0.
  Qed.

  #[global] Instance is_empty_Equal' : forall {elt},
    Proper (M.Equal (elt := elt) ==> Logic.eq) (M.is_empty (elt := elt)).
  Proof.
    intros ????.
    destruct (M.is_empty x) eqn:?, (M.is_empty y) eqn:?; auto.
    - now rewrite (is_empty_Equal _ _ H Heqb) in Heqb0.
    - now rewrite (is_empty_Equal _ _ (symmetry H) Heqb0) in Heqb.
  Qed.

  #[global] Instance bindings_m {elt} : Proper (M.Equal ==> eqlistA (K.eq * Logic.eq)%signature) (@M.bindings elt).
  Proof.
    intros m m' Hm. now apply bindings_Equal_eqlistA.
  Qed.

  #[global] Instance bindings_Equal_eq : forall {elt},
    K.eq = Logic.eq ->
    Proper (M.Equal (elt := elt) ==> Logic.eq) (M.bindings (elt := elt)).
  Proof.
    intros ?????. apply bindings_Equal_eqlistA in H0.
    induction H0.
    - reflexivity.
    - subst. destruct x0, x', H0. compute in H0, H2.
      rewrite H in H0. now subst.
  Qed.

  Lemma add_update_neq {elt} : forall k k' f v (m : M.t elt),
    ~K.eq k k' ->
    M.Equal (M.add k v (update k' f m)) (update k' f (M.add k v m)).
  Proof.
    intros. intro k''.
    unfold update.
    setoid_rewrite add_neq_o at 2; auto.
    destruct (f (M.find k' m)) eqn:?.
    - rewrite add_add_2; auto.
    - rewrite remove_add_2; auto.
  Qed.

  Lemma map_add : forall {elt elt' : Type}
      (m : M.t elt)
      (k : M.key) (x : elt)
      (f : elt -> elt'),
    M.add k (f x) (M.map f m) == M.map f (M.add k x m).
  Proof.
    intros * k'. rewrite map_find. unfold option_map.
    destruct (K.eq_dec k k').
    - rewrite !add_eq_o; auto.
    - rewrite !add_neq_o; auto.
      now rewrite map_find.
  Qed.

  Lemma map_remove : forall {elt elt' : Type}
      (m : M.t elt)
      (k : M.key)
      (f : elt -> elt'),
    M.remove k (M.map f m) == M.map f (M.remove k m).
  Proof.
    intros * k'. rewrite map_find. unfold option_map.
    destruct (K.eq_dec k k').
    - rewrite !remove_eq_o; auto.
    - rewrite !remove_neq_o; auto.
      now rewrite map_find.
  Qed.

  Lemma map2_1n : forall {elt elt' elt'' : Type}
      (m : M.t elt) (m' : M.t elt')
      (x : M.key) (f : option elt -> option elt' -> option elt''),
    f None None = None ->
    M.find x (map2 f m m') = f (M.find x m) (M.find x m').
  Proof.
    intros. unfold map2.
    edestruct merge_spec1n as (? & ? & ?).
    - intro; apply H.
    - rewrite H1. reflexivity.
  Qed.

  Lemma map2_add : forall {elt elt' elt'' : Type}
      (m : M.t elt) (m' : M.t elt')
      (k : M.key) (x : elt) (y : elt') (z : elt'')
      (f : option elt -> option elt' -> option elt''),
    f (Some x) (Some y) = Some z ->
    M.add k z (map2 f m m') == map2 f (M.add k x m) (M.add k y m').
  Proof.
    intros * ? k'.
    destruct (K.eq_dec k k').
    - rewrite add_eq_o; auto.
      pose proof (in_add_eq k x m).
      eapply or_introl in H0. rewrite e in H0 at 1.
      eapply M.merge_spec1 in H0 as (k'' & ? & ?).
      unfold map2. rewrite H1.
      rewrite !add_eq_o; auto.
    - rewrite add_neq_o; auto.
      destruct (P.In_dec (map2 f m m') k').
      + apply M.merge_spec2 in i. eapply M.merge_spec1 in i as ?.
        destruct H0 as (k'' & ? & ?). unfold map2. rewrite H1. clear k'' H0 H1.
        assert (M.In k' (M.add k x m) \/ M.In k' (M.add k y m')).
        { destruct i; [left | right]; now apply in_add. }
        eapply M.merge_spec1 in H0 as (k'' & ? & ?). rewrite H1. clear k'' H0 H1.
        rewrite !add_neq_o; auto.
      + apply not_in_find in n0 as ?. rewrite H0.
        symmetry. apply not_in_find. intro.
        apply M.merge_spec2 in H1 as ?. rewrite !add_neq_in_iff in H2; auto.
        eapply M.merge_spec1 in H2 as (k'' & ? & ?). unfold map2 in H0. rewrite H3 in H0.
        apply M.merge_spec2 in H1 as ?.
        eapply M.merge_spec1 with (f := fun _ : M.key => f) in H4 as (k''' & ? & ?).
        rewrite !add_neq_o in H5; auto. rewrite H0 in H5.
        apply in_find in H5; auto.
  Qed.

  Lemma merge_remove : forall {elt elt' elt'' : Type}
      (m : M.t elt) (m' : M.t elt') (k : M.key)
      (f : M.key -> option elt -> option elt' -> option elt''),
      Proper (K.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq) f ->
    M.remove k (M.merge f m m') == M.merge f (M.remove k m) (M.remove k m').
  Proof.
    intros * Hf k'.
    destruct (K.eq_dec k k').
    - rewrite remove_eq_o; auto.
      destruct (P.In_dec (M.merge f (M.remove k m) (M.remove k m')) k').
      + apply M.merge_spec2 in i as [].
        * now apply remove_1 in H.
        * now apply remove_1 in H.
      + now apply not_in_find in n.
    - rewrite remove_neq_o; auto.
      destruct (In_dec (M.merge f m m') k').
      + apply M.merge_spec2 in i. eapply M.merge_spec1 in i as ?.
        destruct H as (k'' & ? & ?). unfold map2. rewrite H0, H. clear k'' H H0.
        assert (M.In k' (M.remove k m) \/ M.In k' (M.remove k m')).
        { rewrite !remove_in_iff. tauto. }
        eapply M.merge_spec1 in H as (k'' & ? & ?). rewrite H0, H. clear k'' H H0.
        rewrite !remove_neq_o; auto.
      + apply not_in_find in n0 as ?. rewrite H.
        symmetry. apply not_in_find. intro.
        apply M.merge_spec2 in H0 as ?. rewrite !remove_neq_in_iff in H1; auto.
        eapply M.merge_spec1 in H1 as (k'' & ? & ?). rewrite H2, H1 in H.
        apply M.merge_spec2 in H0 as ?.
        eapply M.merge_spec1 with (f := f) in H3 as (k''' & ? & ?). rewrite H3 in H4.
        rewrite !remove_neq_o in H4; auto. rewrite H in H4.
        apply in_find in H4; auto.
  Qed.

  Lemma map2_remove : forall {elt elt' elt'' : Type}
      (m : M.t elt) (m' : M.t elt') (k : M.key)
      (f : option elt -> option elt' -> option elt''),
    M.remove k (map2 f m m') == map2 f (M.remove k m) (M.remove k m').
  Proof.
    intros. apply merge_remove.
    intros _ _ _ ?? <- ?? <-. reflexivity.
  Qed.

  (* Equal1 *)

  Section Equal1.

    Context {elt : Type} (d : elt) (R : relation elt)
      (HR : Reflexive R) (HR' : Transitive R) (HR'' : Symmetric R).

    #[global] Instance Equal1_Eqdom : subrelation (@M.Equal1 elt R) (@M.Eqdom elt).
    Proof.
      intros m m' E k. rewrite !in_find. specialize (E k).
      split; intros ??; rewrite H0 in E.
      - now destruct (M.find k m).
      - now destruct (M.find k m').
    Qed.

    #[global] Instance Reflexive_Equal1 : Reflexive (@M.Equal1 elt R).
    Proof.
      unfold M.Equal1. intros m k. reflexivity.
    Qed.

    #[global] Instance Symmetric_Equal1 : Symmetric (@M.Equal1 elt R).
    Proof.
      intros m m' ? k. now symmetry.
    Qed.

    #[global] Instance Transitive_Equal1 : Transitive (@M.Equal1 elt R).
    Proof.
      intros m m' m'' ?? k. now etransitivity.
    Qed.

    #[global] Instance find_m1 : Proper (K.eq ==> M.Equal1 R ==> option_rel R) (@M.find elt).
    Proof.
      intros k k' Hk m m' E. red in E. now rewrite Hk.
    Qed.

    #[global] Instance find_or_m1 :
      Proper (K.eq ==> R ==> M.Equal1 R ==> R) M.find_or.
    Proof.
      intros ??? ??? ???. unfold M.find_or.
      pose proof (find_m1 x y H x1 y1 H1).
      now destruct (M.find x x1), (M.find y y1).
    Qed.

    Lemma map_find_or'' : forall {elt'} k (d : elt') (d' : elt) m (f : elt' -> elt),
      R d' (f d) ->
      R (M.find_or k d' (M.map f m)) (f (M.find_or k d m)).
    Proof.
      intros. unfold M.find_or. rewrite P.map_o.
      now destruct (M.find k m).
    Qed.

    #[global] Instance add_m1 : Proper (K.eq ==> R ==> M.Equal1 R ==> M.Equal1 R) (@M.add elt).
    Proof.
      intros k k' Hk x y E m m' E' k''.
      rewrite Hk. destruct (K.eq_dec k' k'').
      - rewrite e. now rewrite !add_eq_o.
      - now rewrite !add_neq_o.
    Qed.

    #[global] Instance remove_m1 : Proper (K.eq ==> M.Equal1 R ==> M.Equal1 R) (@M.remove elt).
    Proof.
      clear HR.
      intros k k' Hk m m' E' k''.
      rewrite Hk. destruct (K.eq_dec k' k'').
      - rewrite e. now rewrite !remove_eq_o.
      - now rewrite !remove_neq_o.
    Qed.

    #[global] Instance singleton_m1 : Proper (K.eq ==> R ==> M.Equal1 R) (@M.singleton elt).
    Proof.
      intros k k' Hk x y E k''.
      rewrite Hk. destruct (K.eq_dec k' k'').
      - rewrite e. now rewrite !singleton_o1.
      - now rewrite !singleton_o2.
    Qed.

    Theorem Equiv_Equal1 : forall m m', M.Equiv R m m' <-> M.Equal1 R m m'.
    Proof.
      split; intro.
      - intro. red in H.
        destruct (M.find y m) eqn:?, (M.find y m') eqn:?; auto.
        + apply M.find_spec in Heqo, Heqo0. eapply H; eauto.
        + exfalso. apply not_in_find in Heqo0. apply Heqo0.
          apply H. apply in_find. now rewrite Heqo.
        + exfalso. apply not_in_find in Heqo. apply Heqo.
          apply H. apply in_find. now rewrite Heqo0.
      - split. { now apply Equal1_Eqdom in H. }
        intros. specialize (H k).
        apply M.find_spec in H0, H1. now rewrite H0, H1 in H.
    Qed.

    #[global] Instance bindings_m1 : Proper (M.Equal1 R ==> eqlistA (K.eq * R)%signature) (@M.bindings elt).
    Proof.
      intros m m' Hm. apply bindings_Equiv_eqlistA. now apply Equiv_Equal1.
    Qed.

    #[global] Instance Equal1_Equal1d : subrelation (@M.Equal1 elt R) (@M.Equal1d elt R d).
    Proof.
      intros m m' E k. specialize (E k).
      destruct (M.find k m) eqn:?, (M.find k m') eqn:?; try now destruct E.
      - erewrite !find_some_find_or; eauto.
      - now rewrite !find_none_find_or.
    Qed.

    #[global] Instance Reflexive_Equal1d : Reflexive (M.Equal1d R d).
    Proof.
      intros m k. reflexivity.
    Qed.

    #[global] Instance Symmetric_Equal1d : Symmetric (M.Equal1d R d).
    Proof.
      intros m m' ? k. now symmetry.
    Qed.

    #[global] Instance Transitive_Equal1d : Transitive (M.Equal1d R d).
    Proof.
      intros m m' m'' ?? k. etransitivity. apply H. apply H0.
    Qed.

    #[global] Instance find_or_m1d k :
      Proper (M.Equal1d R d ==> R) (M.find_or k d).
    Proof.
      intros ???. apply H.
    Qed.

    #[global] Instance add_m1d : Proper (K.eq ==> R ==> M.Equal1d R d ==> M.Equal1d R d) (@M.add elt).
    Proof.
      clear HR. intros k k' Hk x y E m m' E' k''.
      rewrite Hk. destruct (K.eq_dec k' k'').
      - rewrite e. now rewrite !find_or_add_eq_o.
      - now rewrite !find_or_add_neq_o.
    Qed.

    #[global] Instance remove_m1d : Proper (K.eq ==> M.Equal1d R d ==> M.Equal1d R d) (@M.remove elt).
    Proof.
      intros k k' Hk m m' E' k''.
      rewrite Hk. destruct (K.eq_dec k' k'').
      - rewrite e. now rewrite !find_or_remove_eq_o.
      - now rewrite !find_or_remove_neq_o.
    Qed.

  End Equal1.

  Lemma Equal_Equal1 {elt} :
    subrelation (M.Equal (elt := elt)) (M.Equal1 Logic.eq).
  Proof.
    red. intros ????. apply option_rel_eq. apply H.
  Qed.

  Lemma Equal1_subrelation {elt} (R R' : relation elt) :
    subrelation R R' ->
    subrelation (M.Equal1 R) (M.Equal1 R').
  Proof.
    red. intros ?????.
    apply option_rel_subrelation in H.
    apply H. apply H0.
  Qed.

  (* keys *)

  Lemma Sorted_keys : forall {elt} (m : M.t elt),
    Sorted K.lt (M.keys m).
  Proof.
    intros. unfold M.keys.
    pose proof (M.bindings_spec2 m). induction H.
    - constructor.
    - rewrite map_cons.
      constructor. assumption.
      destruct H0.
      + constructor.
      + rewrite map_cons. constructor. apply H0.
  Qed.

  Lemma Inf_In : forall a b l,
    Sorted K.lt l ->
    HdRel K.lt a l ->
    In b l ->
    K.lt a b.
  Proof.
    intros.
    eapply InfA_alt with (l := l); try typeclasses eauto; eauto.
    apply In_InA; auto; typeclasses eauto.
  Qed.

  Lemma Sorted_In : forall (l l' : list K.t),
    Sorted K.lt l ->
    Sorted K.lt l' ->
    (forall x, In x l <-> In x l') ->
    l = l'.
  Proof.
    intros. revert l' H0 H1. induction H; intros. 1: {
      destruct l'; [reflexivity |].
      specialize (H1 t). cbn in H1. tauto.
    }
    destruct H1.
    { specialize (H2 a). cbn in H2. tauto. }
    specialize (IHSorted l0 H1).
    f_equal.
    - destruct H0.
      { pose proof (proj2 (H2 a0)). cbn in H0. tauto. }
      pose proof (proj1 (H2 a)). cbn in H4. intuition.
      pose proof (proj2 (H2 a0)). cbn in H6. intuition.
      + subst.
        eapply Inf_In in H3; auto. 2: apply H5.
        exfalso. apply (F.lt_irrefl (x := a)). etransitivity; eassumption.
      + eapply Inf_In in H3; auto. 2: apply H5.
        pose proof (proj1 (H2 b)). cbn in H8. intuition.
        { subst. exfalso. apply (F.lt_irrefl (x := a)). etransitivity; eassumption. }
        apply Sorted_inv in H as [].
        eapply Inf_In in H11; auto. 2: apply H6.
        exfalso. apply (F.lt_irrefl (x := a)). etransitivity; try eassumption. etransitivity; eassumption.
    - apply IHSorted.
      intros. split; intro.
      + pose proof (proj1 (H2 x)). cbn in H5. intuition. subst.
        eapply Inf_In in H0; auto. 2: apply H4.
        pose proof (proj1 (H2 a)). cbn in H5. intuition.
        { subst. exfalso. apply (F.lt_irrefl (x := a)). etransitivity; eassumption. }
        eapply Inf_In in H3; auto. 2: apply H7.
        { exfalso. apply (F.lt_irrefl (x := a)). etransitivity; eassumption. }
      + pose proof (proj2 (H2 x)). cbn in H5. intuition. subst.
        eapply Inf_In in H3; auto. 2: apply H4.
        pose proof (proj2 (H2 a0)). cbn in H5. intuition.
        { subst. exfalso. apply (F.lt_irrefl (x := a0)). etransitivity; eassumption. }
        eapply Inf_In in H0; auto. 2: apply H7.
        { exfalso. apply (F.lt_irrefl (x := a0)). etransitivity; eassumption. }
  Qed.

  Lemma InA_In : forall {A} (l : list A) (x : A),
    InA Logic.eq x l <-> In x l.
  Proof.
    intros. split; intro.
    - induction H.
      + subst. now left.
      + now right.
    - apply In_InA. typeclasses eauto. assumption.
  Qed.

  (* bindings_Eqdom_eqlistA would help, but it needs homogeneous element types *)
  Lemma in_keys {elt elt'} : forall (m : M.t elt) (m' : M.t elt'),
    K.eq = Logic.eq ->
    (forall k, M.In k m <-> M.In k m') ->
    M.keys m =
    M.keys m'.
  Proof.
    intros.
    setoid_rewrite in_fst_bindings_iff in H0.
    apply Sorted_In. 1, 2: apply Sorted_keys.
    intros.
    rewrite <- !InA_In.
    rewrite <- H. apply H0.
  Qed.

  Lemma add_filter_false {elt} : forall k v (m : M.t elt) f,
    Proper (K.eq ==> Logic.eq ==> Logic.eq) f ->
    ((f k v = false /\ ~ M.In k m) \/ forall v, f k v = false) ->
    M.filter f (M.add k v m) == M.filter f m.
  Proof.
    intros * ???.
    rewrite !filter_find; auto.
    destruct (K.eq_dec k y).
    - rewrite add_eq_o, <- e; auto. cbn.
      rewrite <- e.
      destruct H0 as [[] |].
      + apply not_in_find in H1.
        now rewrite H0, H1.
      + rewrite H0. destruct (M.find k m) eqn:?; auto. cbn.
        now rewrite <- e, H0.
    - rewrite add_neq_o; auto.
  Qed.

  Lemma add_filter_true {elt} : forall k v (m : M.t elt) f,
    Proper (K.eq ==> Logic.eq ==> Logic.eq) f ->
    f k v = true ->
    M.filter f (M.add k v m) == M.add k v (M.filter f m).
  Proof.
    intros * ???.
    rewrite filter_find; auto.
    destruct (K.eq_dec k y).
    - rewrite !add_eq_o; auto. cbn.
      now rewrite <- e, H0.
    - rewrite !add_neq_o; auto.
      now rewrite filter_find.
  Qed.

  Lemma filter_spec' {elt} : forall f (m : M.t elt),
    filter f (M.bindings m) = M.bindings (M.filter (fun k e => f (k, e)) m).
  Proof.
    intros. rewrite M.filter_spec.
    apply Utils.filter_ext; auto.
    red. intros. subst. now destruct y.
  Qed.

  Lemma optlast_app {A} : forall (l l' : list A),
    l' <> nil ->
    optlast (l ++ l') = optlast l'.
  Proof.
    intros. induction l.
    - reflexivity.
    - cbn. destruct (l ++ l') eqn:?.
      + apply app_eq_nil in Heql0 as []. now apply H in H1.
      + apply IHl.
  Qed.

  Lemma filter_is_empty {elt} : forall f (m : M.t elt),
    Proper (K.eq ==> Logic.eq ==> Logic.eq) f ->
    M.is_empty (M.filter f m) = true ->
    forall k v, M.find k m = Some v -> f k v = false.
  Proof.
    intros * Hf **.
    rewrite <- eq_empty in H. specialize (H k). rewrite filter_find in H; auto.
    rewrite H0 in H. cbn in H. rewrite empty_o in H. now destruct (f k v).
  Qed.

  Lemma max_elt_add_lt {elt} : forall k k' v v' (m : M.t elt),
    max_elt m = Some (k, v) ->
    K.lt k' k ->
    option_rel (K.eq * Logic.eq)%signature (max_elt (M.add k' v' m)) (Some (k, v)).
  Proof.
    intros.
    assert (Hf : Proper (K.eq ==> Logic.eq ==> Logic.eq)
      (fun (k0 : M.key) (e : elt) => leb (k, v) (k0, e))).
    { repeat intro. subst. now rewrite H1. }
    apply max_elt_MapsTo in H as Hmax.
    apply find_mapsto_iff in Hmax.
    unfold max_elt in H |- *.
    rewrite (bindings_split (k, v)) in H |- *.
    assert (bindings_ge (k, v) m <> nil). {
      intro. unfold bindings_ge in H1.
      rewrite filter_spec' in H1. apply is_empty_bindings in H1.
      epose proof (filter_is_empty _ _ _ H1). apply H2 in Hmax.
      apply not_true_iff_false in Hmax. apply Hmax. apply leb_1. apply F.lt_irrefl.
    }
    rewrite optlast_app in H; auto.
    rewrite optlast_app. 2: {
      intro. unfold bindings_ge in H2.
      rewrite filter_spec' in H2. apply is_empty_bindings in H2. rewrite add_filter_false in H2; auto.
      2: { right. intro. apply not_true_iff_false. intro. apply leb_1 in H3. now apply H3 in H0. }
      epose proof (filter_is_empty _ _ _ H2). apply H3 in Hmax.
      apply not_true_iff_false in Hmax. apply Hmax. apply leb_1. apply F.lt_irrefl.
    }
    unfold bindings_ge. rewrite filter_spec'. rewrite add_filter_false; auto.
    2: { right. intro. apply not_true_iff_false. intro. apply leb_1 in H2. now apply H2 in H0. }
    rewrite <- filter_spec'. setoid_rewrite H. reflexivity.
  Qed.

  Lemma max_elt_lt_Above {elt} : forall k k' v (m : M.t elt),
    max_elt m = Some (k, v) ->
    K.lt k k' ->
    Above k' m.
  Proof.
    intros. red. intros.
    destruct (K.eq_dec k y).
    { now rewrite <- e. }
    transitivity k; auto. eapply max_elt_Above; eauto.
    apply remove_in_iff; split; auto.
  Qed.

  Lemma max_elt_add_gt {elt} : forall k k' v v' (m : M.t elt),
    max_elt m = Some (k, v) ->
    K.lt k k' ->
    option_rel (K.eq * Logic.eq)%signature (max_elt (M.add k' v' m)) (Some (k', v')).
  Proof.
    intros.
    apply max_elt_MapsTo in H as Hmax.
    apply find_mapsto_iff in Hmax.
    unfold max_elt.
    erewrite bindings_Add_Above.
    3: apply Add_add.
    { now rewrite optlast_app. }
    eapply max_elt_lt_Above; eauto.
  Qed.

  Lemma max_elt_add_empty {elt} : forall k v (m : M.t elt),
    M.is_empty m = true ->
    option_rel (K.eq * Logic.eq)%signature (max_elt (M.add k v m)) (Some (k, v)).
  Proof.
    intros.
    unfold max_elt.
    rewrite bindings_Add. 3: apply Add_add.
    - unfold bindings_lt, bindings_ge.
      apply is_empty_bindings in H. rewrite H.
      cbn. split; reflexivity.
    - rewrite M.is_empty_spec in H.
      setoid_rewrite <- not_in_find in H. apply H.
  Qed.

End ExtMMapFacts.

Module NatMap.
  Module Import M := MMaps.OrdList.Make Nat_as_OT.
  Include ExtMMap Nat_as_OT M.
End NatMap.

Module NatMapFacts := ExtMMapFacts Nat_as_OT NatMap.

Arguments NatMap.find : simpl never.
Arguments NatMap.find_or : simpl never.
Arguments NatMap.merge : simpl never.

Module TMap := NatMap.

Module StringMap.
  Module Import M := MMaps.OrdList.Make String_as_OT.
  Include ExtMMap String_as_OT M.
End StringMap.

Module StringMapFacts := ExtMMapFacts String_as_OT StringMap.

Module FnMap := StringMap.
