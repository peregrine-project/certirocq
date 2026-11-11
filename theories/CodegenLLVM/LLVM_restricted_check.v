(** * Soundness of the check of the LLVM fragment

    [llvm_fragmentb_sound] shows that [llvm_fragmentb] in [LLVM_fragment.v]
    implies [llvm_restricted], so a program that passes the check needs no
    further assumption from the LambdaANF pipeline.
    [llvm_fragment_buildable] shows that the compile-time rejection in
    [LambdaANF_to_LLVM_Wrapper] spares every program in the checked fragment. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From CertiRocq.LambdaANF Require Import term term_util identifiers set_util Ensembles_util.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM LLVM_fragment LambdaANF_to_LLVM_statement.
Import ListNotations.

Lemma fragment_chunk cenv e : snd (fragment cenv e) = chunk_words e.
Proof.
  induction e using exp_ind'; simpl; unfold constr_chunk; try rewrite IHe; try reflexivity.
Qed.

Lemma buildable_chunk cenv al e : snd (buildable cenv al e) = chunk_words e.
Proof.
  induction e using exp_ind'; simpl; unfold constr_chunk; try rewrite IHe; try reflexivity.
Qed.

Lemma tag_okb_sound cenv t : tag_okb cenv t = true -> tag_ok cenv t.
Proof.
  unfold tag_okb, tag_ok. destruct (M.get t cenv) eqn:E; [|discriminate].
  intros H. apply andb_true_iff in H as [H1 H2].
  apply N.ltb_lt in H1, H2. split; [eauto | split; assumption].
Qed.

Lemma fragment_sound cenv e : fst (fragment cenv e) = true -> body_ok cenv e.
Proof.
  induction e using exp_ind'; simpl; intros H.
  - repeat (apply andb_true_iff in H as [H ?]).
    match goal with Hc : N.leb _ max_chunk = true |- _ => apply N.leb_le in Hc end.
    match goal with Ha : N.eqb _ _ = true |- _ => apply N.eqb_eq in Ha end.
    apply BO_constr; auto using tag_okb_sound.
    assert (E : chunk_words (Econstr v t l e) = constr_chunk l (snd (fragment cenv e)))
      by (rewrite fragment_chunk; destruct l; reflexivity).
    rewrite E. assumption.
  - apply BO_case. constructor.
  - apply andb_true_iff in H as [H Hgo]. apply andb_true_iff in H as [Ht He].
    assert (B : body_ok cenv (Ecase v l)) by (apply IHe0; exact Hgo).
    inversion B; subst. apply BO_case. constructor; [split|]; auto using tag_okb_sound.
  - apply andb_true_iff in H as [Hn He]. apply N.ltb_lt in Hn.
    apply BO_proj; auto.
  - apply BO_letapp; auto.
  - discriminate.
  - apply BO_app.
  - destruct p as [tag n]. destruct tag; simpl in H; try discriminate.
    apply BO_prim_val; auto.
  - discriminate.
  - apply BO_halt.
Qed.

Lemma fundefs_all_sound cenv fds :
  fundefs_all (fun b => fst (fragment cenv b)) fds = true -> fundefs_ok cenv fds.
Proof.
  induction fds; simpl; intros H; constructor;
    try (apply andb_true_iff in H as [H1 H2]); auto using fragment_sound.
Qed.

Lemma cenv_okb_sound cenv : cenv_okb cenv = true -> cenv_ok cenv.
Proof.
  unfold cenv_okb, cenv_ok. intros H t t' i i' Hne Ht Ht' Hind Hord.
  apply M.elements_correct in Ht, Ht'.
  rewrite forallb_forall in H. specialize (H _ Ht).
  rewrite forallb_forall in H. specialize (H _ Ht').
  unfold cenv_pair_okb in H; simpl in H.
  apply Pos.eqb_neq in Hne.
  rewrite Hne, Hind, Pos.eqb_refl, Hord, N.eqb_refl in H; simpl in H.
  apply Bool.eqb_prop in H.
  destruct (N.eqb_spec (ctor_arity i) 0), (N.eqb_spec (ctor_arity i') 0);
    simpl in H; try discriminate; tauto.
Qed.

(** ** Unique bindings *)

Lemma add_fresh_spec x s s1 :
  add_fresh x s = Some s1 ->
  ~ PS.In x s /\ (forall y, PS.In y s1 <-> y = x \/ PS.In y s).
Proof.
  unfold add_fresh. destruct (PS.mem x s) eqn:E; [discriminate|]. intros H. inversion H; subst.
  split.
  - intros Hc. apply PS.mem_spec in Hc. congruence.
  - intros y. rewrite PS.add_spec. reflexivity.
Qed.

Lemma add_list_spec ys s s' :
  add_list ys s = Some s' ->
  NoDup ys /\ (forall x, List.In x ys -> ~ PS.In x s) /\
  (forall y, PS.In y s' <-> PS.In y s \/ List.In y ys).
Proof.
  revert s s'. induction ys as [|y ys IH]; simpl; intros s s' H.
  - inversion H; subst. repeat split; [constructor|contradiction|tauto..].
  - destruct (add_fresh y s) as [s1|] eqn:Ha; [|discriminate].
    destruct (add_fresh_spec _ _ _ Ha) as [Hn Hs].
    destruct (IH _ _ H) as (Hnd & Hd & Hm).
    split; [|split].
    + constructor; [|exact Hnd]. intros Hin. apply (Hd _ Hin). apply Hs. auto.
    + intros x [->|Hin]; [exact Hn|]. intros Hc. apply (Hd _ Hin). apply Hs. auto.
    + intros z. rewrite Hm, Hs. intuition.
Qed.

Lemma bound_case_cons v c e l y :
  bound_var (Ecase v ((c, e) :: l)) y <-> bound_var e y \/ bound_var (Ecase v l) y.
Proof.
  split.
  - intros H. inversion H; subst.
    match goal with Hi : List.In _ ((c, e) :: l) |- _ => destruct Hi as [Heq|Hi] end.
    + inversion Heq; subst. auto.
    + right. econstructor; eauto.
  - intros [H|H].
    + econstructor; [exact H | left; reflexivity].
    + inversion H; subst. econstructor; [eassumption | right; eassumption].
Qed.

Lemma bound_fcons f t ys e B y :
  bound_var_fundefs (Fcons f t ys e B) y <->
  y = f \/ List.In y ys \/ bound_var e y \/ bound_var_fundefs B y.
Proof.
  split.
  - intros H. inversion H; subst; auto.
    match goal with Hv : Ensembles.In _ (Ensembles.Union _ _ _) _ |- _ => destruct Hv as [? Hu|? Hu] end.
    + inversion Hu; subst. auto.
    + right; left. exact Hu.
  - intros [->|[H|[H|H]]].
    + apply Bound_Fcons1. left. constructor.
    + apply Bound_Fcons1. right. exact H.
    + apply Bound_Fcons3. exact H.
    + apply Bound_Fcons2. exact H.
Qed.

Ltac ub_binder IHe H v s :=
  destruct (add_fresh v s) as [s1|] eqn:Ha; [|discriminate];
  let Hn := fresh "Hn" in let Hs := fresh "Hs" in
  destruct (add_fresh_spec _ _ _ Ha) as [Hn Hs];
  let Hu := fresh "Hu" in let Hd := fresh "Hd" in let Hm := fresh "Hm" in
  destruct (IHe _ _ H) as (Hu & Hd & Hm);
  split;
  [ first [ apply UBound_Econstr | apply UBound_Eproj | apply UBound_Eletapp
          | apply UBound_Eprim_val | apply UBound_Eprim ];
    [ intros Hb; apply (Hd _ Hb); apply Hs; left; reflexivity | exact Hu ]
  | split ];
  [ intros y Hb; inversion Hb; subst;
    [ exact Hn | intros Hc; refine (Hd _ _ (proj2 (Hs _) (or_intror Hc))); assumption ]
  | intros y; rewrite Hm, Hs; split;
    [ intros [[->|Hy]|Hy]; [right; constructor | left; exact Hy | right; constructor; exact Hy]
    | intros [Hy|Hy]; [ auto | inversion Hy; subst; auto ] ] ].

Lemma ub_spec e s s' :
  ub e s = Some s' ->
  unique_bindings e /\ (forall x, bound_var e x -> ~ PS.In x s) /\
  (forall y, PS.In y s' <-> PS.In y s \/ bound_var e y).
Proof.
  revert s s'. induction e using exp_ind'; intros s s' H; simpl in H.
  - ub_binder IHe H v s.
  - inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb; subst. contradiction.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy; subst; contradiction]].
  - destruct (ub e s) as [s1|] eqn:He; [|discriminate].
    destruct (IHe _ _ He) as (Hu & Hd & Hm).
    destruct (IHe0 s1 s' H) as (Hu' & Hd' & Hm').
    split; [|split].
    + constructor; [exact Hu'|exact Hu|].
      constructor. intros y Hc. destruct Hc as [y H1 H2].
      apply (Hd' _ H2). apply Hm. auto.
    + intros x Hb. apply bound_case_cons in Hb as [Hb|Hb]; [exact (Hd _ Hb)|].
      intros Hc. apply (Hd' _ Hb). apply Hm. auto.
    + intros y. rewrite Hm', Hm, bound_case_cons. tauto.
  - ub_binder IHe H v s.
  - ub_binder IHe H x s.
  - discriminate.
  - inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy]].
  - ub_binder IHe H v s.
  - ub_binder IHe H v s.
  - inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy]].
Qed.

Lemma ub_fundefs_spec fds s s' :
  ub_fundefs fds s = Some s' ->
  unique_bindings_fundefs fds /\ (forall x, bound_var_fundefs fds x -> ~ PS.In x s) /\
  (forall y, PS.In y s' <-> PS.In y s \/ bound_var_fundefs fds y).
Proof.
  revert s s'. induction fds as [f t ys e fds IH|]; intros s s' H; simpl in H.
  - destruct (add_fresh f s) as [s1|] eqn:Ha; [|discriminate].
    destruct (add_list ys s1) as [s2|] eqn:Hl; [|discriminate].
    destruct (ub e s2) as [s3|] eqn:He; [|discriminate].
    destruct (add_fresh_spec _ _ _ Ha) as [Hn Hs].
    destruct (add_list_spec _ _ _ Hl) as (Hnd & Hdl & Hml).
    destruct (ub_spec _ _ _ He) as (Hu & Hd & Hm).
    destruct (IH _ _ H) as (Hu' & Hd' & Hm').
    assert (Hf2 : PS.In f s2) by (apply Hml; left; apply Hs; auto).
    assert (Hys3 : forall y, List.In y ys -> PS.In y s3)
      by (intros y Hy; apply Hm; left; apply Hml; auto).
    assert (He3 : forall y, bound_var e y -> PS.In y s3) by (intros y Hy; apply Hm; auto).
    split; [|split].
    + constructor; auto.
      * intros Hb. exact (Hd _ Hb Hf2).
      * intros Hb. refine (Hd' _ Hb _). apply Hm. auto.
      * constructor. intros y Hc. destruct Hc as [y H1 H2].
        refine (Hd _ H1 _). apply Hml. right. exact H2.
      * constructor. intros y Hc. destruct Hc as [y H1 H2].
        refine (Hd' _ H1 (Hys3 _ H2)).
      * constructor. intros y Hc. destruct Hc as [y H1 H2].
        exact (Hd' _ H2 (He3 _ H1)).
      * intros Hc. refine (Hdl _ Hc _). apply Hs. auto.
    + intros x Hb. apply bound_fcons in Hb as [->|[Hb|[Hb|Hb]]].
      * exact Hn.
      * intros Hc. refine (Hdl _ Hb _). apply Hs. auto.
      * intros Hc. refine (Hd _ Hb _). apply Hml. left. apply Hs. auto.
      * intros Hc. refine (Hd' _ Hb _). apply Hm. left. apply Hml. left. apply Hs. auto.
    + intros y. rewrite Hm', Hm, Hml, Hs, bound_fcons. intuition.
  - inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy]].
Qed.

Lemma llvm_uniqueb_sound fds main :
  llvm_uniqueb fds main = true -> unique_bindings (Efun fds main).
Proof.
  unfold llvm_uniqueb. destruct (ub_fundefs fds PS.empty) as [s|] eqn:Hf; [|discriminate].
  destruct (ub main s) as [s'|] eqn:Hm; [|discriminate]. intros _.
  destruct (ub_fundefs_spec _ _ _ Hf) as (Hu & _ & Hms).
  destruct (ub_spec _ _ _ Hm) as (Hu' & Hd & _).
  constructor; [exact Hu'|exact Hu|].
  constructor. intros y Hc. destruct Hc as [y H1 H2].
  refine (Hd _ H1 _). apply Hms. auto.
Qed.

Lemma llvm_closedb_sound e :
  llvm_closedb e = true -> ~ exists x, occurs_free e x.
Proof.
  unfold llvm_closedb. intros H [x Hx].
  apply PS.is_empty_spec in H.
  refine (H x (FromSet_sound _ _ x (exp_fv_correct e) Hx)).
Qed.

Theorem llvm_fragmentb_sound cenv fds main :
  llvm_fragmentb cenv (Efun fds main) = true ->
  llvm_restricted cenv fds main.
Proof.
  unfold llvm_fragmentb, llvm_restricted. simpl. intros H.
  apply andb_true_iff in H as [H Hu]. apply andb_true_iff in H as [H Hc].
  apply andb_true_iff in H as [H Hcenv]. apply andb_true_iff in H as [Hf Hm].
  exact (conj (fundefs_all_sound _ _ Hf) (conj (fragment_sound _ _ Hm)
    (conj (llvm_closedb_sound _ Hc) (conj (llvm_uniqueb_sound _ _ Hu) (cenv_okb_sound _ Hcenv))))).
Qed.

Lemma fragment_buildable_exp cenv al e :
  fst (fragment cenv e) = true -> fst (buildable cenv al e) = true.
Proof.
  induction e using exp_ind'; simpl; intros H.
  - apply andb_true_iff in H as [H Hc]. apply andb_true_iff in H as [H _].
    apply andb_true_iff in H as [H Ht].
    rewrite IHe by exact H. rewrite buildable_chunk. rewrite fragment_chunk in Hc.
    rewrite Hc. simpl.
    unfold tag_okb in Ht. destruct (M.get t cenv); [|discriminate].
    apply andb_true_iff in Ht as [Ht _]. destruct l; [reflexivity | exact Ht].
  - reflexivity.
  - apply andb_true_iff in H as [H Hgo]. apply andb_true_iff in H as [_ He].
    rewrite IHe by exact He. simpl. apply IHe0. exact Hgo.
  - apply andb_true_iff in H as [_ He]. auto.
  - auto.
  - discriminate.
  - reflexivity.
  - apply andb_true_iff in H as [_ He]. auto.
  - discriminate.
  - reflexivity.
Qed.

Theorem llvm_fragment_buildable cenv al e :
  llvm_fragmentb cenv e = true -> llvm_buildable cenv al e = true.
Proof.
  unfold llvm_fragmentb, llvm_buildable. destruct (prog_parts e) as [fds main].
  intros H. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H _].
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [Hf Hm].
  apply andb_true_iff. split; [|auto using fragment_buildable_exp].
  induction fds; simpl in *; auto.
  apply andb_true_iff in Hf as [H1 H2]. apply andb_true_iff.
  split; auto using fragment_buildable_exp.
Qed.

(** ** The three rejections, on small programs *)

Section Examples.
  Local Open Scope positive_scope.

  Local Definition info (a o : N) : ctor_ty_info :=
    {| ctor_name := BasicAst.nAnon; ctor_ind_name := BasicAst.nAnon;
       ctor_ind_tag := 1%positive; ctor_arity := a; ctor_ordinal := o |}.
  Local Definition ex_cenv : ctor_env :=
    M.set 2%positive (info 1 251) (M.set 1%positive (info 1 0) (M.empty _)).
  Local Definition no_alloc (_ : prim) := false.

  Example accepts_low_ordinal :
    llvm_buildable ex_cenv no_alloc (Efun Fnil (Econstr 2 1 [1] (Ehalt 2))) = true.
  Proof. reflexivity. Qed.

  Example rejects_high_ordinal :
    llvm_buildable ex_cenv no_alloc (Efun Fnil (Econstr 2 2 [1] (Ehalt 2))) = false.
  Proof. reflexivity. Qed.

  Example rejects_allocating_primitive :
    llvm_buildable ex_cenv (fun _ => true) (Efun Fnil (Eprim 2 1 [1] (Ehalt 2))) = false.
  Proof. reflexivity. Qed.

  Example accepts_nursery_sized_chunk :
    llvm_buildable ex_cenv no_alloc
      (Efun Fnil (Econstr 2 1 (repeat 1%positive (N.to_nat 65535)) (Ehalt 2))) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example rejects_chunk_over_nursery :
    llvm_buildable ex_cenv no_alloc
      (Efun Fnil (Econstr 2 1 (repeat 1%positive (N.to_nat 65536)) (Ehalt 2))) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example rejects_repeated_binder :
    llvm_uniqueb Fnil (Econstr 2 1 [] (Econstr 2 1 [] (Ehalt 2))) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example accepts_distinct_binders :
    llvm_uniqueb Fnil (Econstr 2 1 [] (Econstr 3 1 [] (Ehalt 3))) = true.
  Proof. vm_compute. reflexivity. Qed.

  Example rejects_free_variable :
    llvm_closedb (Efun Fnil (Ehalt 1)) = false.
  Proof. vm_compute. reflexivity. Qed.

  Example strict_fragment_excludes_primitive :
    llvm_fragmentb ex_cenv (Efun Fnil (Eprim 2 1 [1] (Ehalt 2))) = false.
  Proof. reflexivity. Qed.
End Examples.
