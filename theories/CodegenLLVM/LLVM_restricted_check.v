(** * Soundness of the check of the LLVM fragment

    [llvm_fragmentb] in [LLVM_fragment.v] decides the conditions of [llvm_restricted]
    other than closedness and unique bindings, which the theorem's statement
    takes from the LambdaANF pipeline.  [llvm_fragmentb_sound] gives
    [llvm_restricted] from the check and those two conditions.
    [llvm_fragment_buildable] shows that the compile-time rejection in
    [LambdaANF_to_LLVM_Wrapper] spares every program in the checked fragment. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From CertiRocq.LambdaANF Require Import term term_util identifiers.
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
    rewrite E. unfold max_chunk in *. lia.
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

Theorem llvm_fragmentb_sound cenv fds main :
  llvm_fragmentb cenv (Efun fds main) = true ->
  (~ exists x, occurs_free (Efun fds main) x) ->
  unique_bindings (Efun fds main) ->
  llvm_restricted cenv fds main.
Proof.
  unfold llvm_fragmentb, llvm_restricted. simpl. intros H Hc Hu.
  apply andb_true_iff in H as [H Hcenv]. apply andb_true_iff in H as [Hf Hm].
  exact (conj (fundefs_all_sound _ _ Hf) (conj (fragment_sound _ _ Hm)
    (conj Hc (conj Hu (cenv_okb_sound _ Hcenv))))).
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
  intros H. apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [Hf Hm].
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

  Example strict_fragment_excludes_primitive :
    llvm_fragmentb ex_cenv (Efun Fnil (Eprim 2 1 [1] (Ehalt 2))) = false.
  Proof. reflexivity. Qed.
End Examples.
