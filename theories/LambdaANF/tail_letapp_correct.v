(** Correctness of [tail_letapp]: [Eletapp x f ft ys (Ehalt x)] becomes [Eapp f ft ys].

    The source takes one more step than the target at every rewritten call (the
    [Ehalt]).  The bound [inline_bound 1 1], also used for [shrink], absorbs it: it
    allows the source 2 extra steps per application it performs, and the rewritten
    [Eletapp] is one.  Since the pass also rewrites function bodies, the same bound
    is the local and the global post-condition. *)

From Stdlib Require Import Arith.Wf_nat PArith.BinPos NArith.BinNat Relations.Relations Lists.List micromega.Lia Sets.Ensembles.
Require Import LambdaANF.term LambdaANF.eval LambdaANF.identifiers LambdaANF.Ensembles_util
        LambdaANF.List_util LambdaANF.tactics LambdaANF.set_util LambdaANF.algebra
        LambdaANF.logical_relations LambdaANF.bounds LambdaANF.tail_letapp.

Import ListNotations.

Section TailLetapp.

  Context (cenv : ctor_env).

  Local Notation PG := (inline_bound 1 1).

  Ltac unfold_all :=
    try unfold zero in *;
    try unfold one_ctx in *;
    try unfold one in *;
    try unfold one_i in *;
    try unfold HRes in *;
    try unfold HRexp_f in *; try unfold fuel_res in *; try unfold fuel_res_exp in *; try unfold fuel_res_pre in *;
    try unfold HRexp_t in *; try unfold trace_res in *; try unfold trace_res_exp in *; try unfold trace_res_pre in *.

  (** * Syntactic properties *)

  Lemma tail_letapp_Eletapp x f ft ys e :
    (e = Ehalt x /\ tail_letapp (Eletapp x f ft ys e) = Eapp f ft ys) \/
    tail_letapp (Eletapp x f ft ys e) = Eletapp x f ft ys (tail_letapp e).
  Proof.
    destruct e; simpl; eauto.
    destruct (Pos.eqb_spec x v); subst; eauto.
  Qed.

  Lemma tail_letapp_find_def f B t xs e :
    find_def f B = Some (t, xs, e) ->
    find_def f (tail_letapp_fds B) = Some (t, xs, tail_letapp e).
  Proof.
    induction B; simpl; [| congruence ].
    destruct (M.elt_eq f v); [ congruence | eauto ].
  Qed.

  Lemma tail_letapp_name_in_fundefs B :
    name_in_fundefs (tail_letapp_fds B) <--> name_in_fundefs B.
  Proof.
    induction B; simpl; [| reflexivity ].
    rewrite IHB. reflexivity.
  Qed.

  Ltac not_bv :=
    let Hc := fresh "Hc" in
    intro Hc;
    match goal with
    | [ Hn : ~ _ |- False ] =>
      apply Hn; match goal with [ Hs : _ \subset _ |- _ ] => eapply Hs; eassumption end
    end.

  Lemma tail_letapp_syntactic :
    (forall e,
        bound_var (tail_letapp e) \subset bound_var e /\
        occurs_free (tail_letapp e) \subset occurs_free e /\
        (unique_bindings e -> unique_bindings (tail_letapp e))) /\
    (forall B,
        bound_var_fundefs (tail_letapp_fds B) \subset bound_var_fundefs B /\
        occurs_free_fundefs (tail_letapp_fds B) \subset occurs_free_fundefs B /\
        (unique_bindings_fundefs B -> unique_bindings_fundefs (tail_letapp_fds B))).
  Proof.
    eapply exp_def_mutual_ind.
    - intros x c ys e [Hbv [Hfv Hub]]. simpl.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x. simpl. split; [| split ]; [ sets | sets | now auto ].
    - intros x bs c e [Hbv [Hfv Hub]] [Hbvs [Hfvs Hubs]]. simpl in *.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
      eapply Disjoint_Included; [| | eassumption ]; eauto.
    - intros x c n y e [Hbv [Hfv Hub]]. simpl.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x f ft ys e [Hbv [Hfv Hub]].
      destruct (tail_letapp_Eletapp x f ft ys e) as [[Heq Htl] | Htl]; rewrite Htl.
      + subst. repeat normalize_bound_var. repeat normalize_occurs_free.
        split; [| split ]; [ sets | sets | ].
        intros. constructor.
      + repeat normalize_bound_var. repeat normalize_occurs_free.
        split; [| split ]; [ sets | sets | ].
        intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros B [Hbvs [Hfvs Hubs]] e [Hbv [Hfv Hub]]. simpl.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      rewrite tail_letapp_name_in_fundefs.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
      eapply Disjoint_Included; [| | eassumption ]; eauto.
    - intros. simpl. split; [| split ]; [ sets | sets | now auto ].
    - intros x p e [Hbv [Hfv Hub]]. simpl.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x p ys e [Hbv [Hfv Hub]]. simpl.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x. simpl. split; [| split ]; [ sets | sets | now auto ].
    - intros f ft xs e [Hbv [Hfv Hub]] B [Hbvs [Hfvs Hubs]]. simpl.
      repeat normalize_bound_var. repeat normalize_occurs_free.
      rewrite !tail_letapp_name_in_fundefs.
      split; [| split ]; [ sets | sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
      all: match goal with
           | [ H : Disjoint _ _ _ |- _ ] =>
             eapply Disjoint_Included; [ | | exact H ]; solve [ eassumption | sets ]
           end.
    - simpl. split; [| split ]; [ sets | sets | now auto ].
  Qed.

  (** * Evaluation *)

  (** The last step of a terminating evaluation is an [Ehalt], which costs [(1, 0)]:
      with one unit of fuel less, the same term runs out of fuel with the trace
      minus that [Ehalt]. *)
  Lemma bstep_fuel_Res_OOT_pred rho e c v cout :
    @bstep_fuel cenv nat fuel_res (nat * nat) trace_res rho e c (Res v) cout ->
    exists c' cout',
      @bstep_fuel cenv nat fuel_res (nat * nat) trace_res rho e c' OOT cout' /\
      c = c' + 1 /\ cout = (fst cout' + 1, snd cout').
  Proof.
    set (P := fun rho e (c : nat) (r : @res val) (cout : nat * nat) =>
                forall v, r = Res v ->
                          (c = 0 /\ cout = (0, 0) /\ exists x, e = Ehalt x) \/
                          (exists c' cout',
                              @bstep cenv nat fuel_res (nat * nat) trace_res rho e c' OOT cout' /\
                              c = c' + 1 /\ cout = (fst cout' + 1, snd cout'))).
    set (P0 := fun rho e (c : nat) (r : @res val) (cout : nat * nat) =>
                 forall v, r = Res v ->
                           exists c' cout',
                             @bstep_fuel cenv nat fuel_res (nat * nat) trace_res rho e c' OOT cout' /\
                             c = c' + 1 /\ cout = (fst cout' + 1, snd cout')).
    intros Hstep.
    assert (Hs : P0 rho e c (Res v) cout).
    { induction Hstep using bstep_fuel_ind' with (P := P) (P0 := P0); unfold P, P0 in *;
        intros v1 Heq; subst;
        try (now right; edestruct IHHstep as [c' [cout' [Hs [Hc Hcout]]]]; [ reflexivity | ];
             do 2 eexists; split; [ econstructor; eauto | split; eassumption ]).
      - right. edestruct IHHstep2 as [c' [cout' [Hs [Hc Hcout]]]]; [ reflexivity | ].
        do 2 eexists. split. eapply BStept_letapp; eauto.
        subst. destruct cout1. unfold_all. simpl. split; [ lia | f_equal; lia ].
      - congruence.
      - left. inv Heq. eauto.
      - congruence.
      - edestruct IHHstep as [[Hc [Hcout [x Hx]]] | [c' [cout' [Hs [Hc Hcout]]]]]; [ reflexivity | | ].
        + subst. exists 0, (0, 0). split.
          * econstructor 1. unfold_all. simpl. lia.
          * unfold_all. simpl. split; reflexivity.
        + subst. do 2 eexists. split. econstructor 2. eassumption.
          destruct cout'. unfold_all. simpl. split; [ lia | f_equal; lia ]. }
    eapply Hs. reflexivity.
  Qed.

  (** The one interesting case. *)
  Lemma preord_exp_tail_letapp k rho1 rho2 x f ft ys :
    preord_var_env cenv PG k rho1 rho2 f f ->
    Forall2 (preord_var_env cenv PG k rho1 rho2) ys ys ->
    preord_exp cenv PG PG k (Eletapp x f ft ys (Ehalt x), rho1) (Eapp f ft ys, rho2).
  Proof.
    intros Hvar Hall v1 cin cout Hleq1 Hstep1. inv Hstep1.
    - (* OOT before the call *)
      exists OOT, cin, <0>. split. econstructor 1. unfold_all. simpl in *. lia.
      split; [| now eauto ].
      unfold_all. simpl in *. unfold inline_bound. simpl. lia.
    - unfold_all. simpl in Hleq1.
      inv H.
      + (* The body terminates *)
        edestruct Hvar as [v' [Hget Hpre]]; eauto.
        rewrite preord_val_eq in Hpre.
        destruct v'; try (now simpl in Hpre; contradiction).
        edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
        edestruct (Hpre vs vs2 (k - 1)) as [xs2 [e2' [rho2' [Hf' [Hset H']]]]]; eauto.
        now eapply Forall2_length; eauto.
        edestruct H' with (cin := cin1) as [v2 [cin' [cout' [Hstep' [Hpost' Hpre'']]]]];
          [ simpl in *; lia | | simpl in *; lia | eassumption | ].
        { eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic.
          eassumption. lia. }
        destruct v2; try contradiction.
        match goal with [ Hh : bstep_fuel _ _ (Ehalt _) _ _ _ |- _ ] => inv Hh end.
        * (* The [Ehalt] runs out of fuel *)
          eapply bstep_fuel_Res_OOT_pred in Hstep'.
          destruct Hstep' as [c' [cout'' [Hs [Hc Hcout]]]]. subst.
          exists OOT, (c' + 1), (fst cout'' , snd cout'' + 1). split; [| split ].
          -- replace (c' + 1) with (c' <+> one (Eapp f ft ys)) by (unfold_all; simpl; lia).
             replace (fst cout'', snd cout'' + 1) with (cout'' <+> one (Eapp f ft ys))
               by (destruct cout''; unfold_all; simpl; f_equal; lia).
             econstructor 2. econstructor; eauto.
          -- unfold_all. simpl in *. destruct cout1 as [t1 a1]. destruct cout'' as [t2 a2].
             unfold inline_bound in *. simpl in *. lia.
          -- simpl. eauto.
        * (* The [Ehalt] returns the result *)
          inv H. match goal with [ Hg : (M.set _ _ _) ! _ = Some _ |- _ ] => rewrite M.gss in Hg; inv Hg end.
          exists (Res v2), (cin' + 1), (fst cout' , snd cout' + 1). split; [| split ].
          -- replace (cin' + 1) with (cin' <+> one (Eapp f ft ys)) by (unfold_all; simpl; lia).
             replace (fst cout', snd cout' + 1) with (cout' <+> one (Eapp f ft ys))
               by (destruct cout'; unfold_all; simpl; f_equal; lia).
             econstructor 2. econstructor; eauto.
          -- unfold_all. simpl in *. destruct cout1 as [t1 a1]. destruct cout' as [t2 a2].
             unfold inline_bound in *. simpl in *. lia.
          -- simpl. eapply preord_val_monotonic. eassumption. simpl in *. lia.
      + (* The body runs out of fuel *)
        edestruct Hvar as [v' [Hget Hpre]]; eauto.
        rewrite preord_val_eq in Hpre.
        destruct v'; try (now simpl in Hpre; contradiction).
        edestruct preord_var_env_get_list as [vs2 [Hget' Hpre']]; eauto.
        edestruct (Hpre vs vs2 (k - 1)) as [xs2 [e2' [rho2' [Hf' [Hset H']]]]]; eauto.
        now eapply Forall2_length; eauto.
        edestruct H' with (cin := cin0) as [v2 [cin' [cout' [Hstep' [Hpost' Hpre'']]]]];
          [ simpl in *; lia | | simpl in *; lia | eassumption | ].
        { eapply Forall2_monotonic; [| eassumption ]. intros. eapply preord_val_monotonic.
          eassumption. lia. }
        destruct v2; try contradiction.
        exists OOT, (cin' <+> one (Eapp f ft ys)), (cout' <+> one (Eapp f ft ys)). split; [| split ].
        -- econstructor 2. econstructor; eauto.
        -- unfold_all. simpl in *. destruct cout0 as [t1 a1]. destruct cout' as [t2 a2].
           unfold inline_bound in *. simpl in *. lia.
        -- simpl. eauto.
  Qed.

  (** * The logical relation *)

  Lemma tail_letapp_def_funs k B rho1 rho2 B' e :
    (forall m e rho1 rho2,
        m < k ->
        preord_env_P cenv PG (occurs_free e) m rho1 rho2 ->
        preord_exp cenv PG PG m (e, rho1) (tail_letapp e, rho2)) ->
    preord_env_P cenv PG (occurs_free (Efun B' e)) k rho1 rho2 ->
    preord_env_P cenv PG (occurs_free (Efun B' e) :|: name_in_fundefs B) k
                 (def_funs B' B rho1 rho1)
                 (def_funs (tail_letapp_fds B') (tail_letapp_fds B) rho2 rho2).
  Proof with eauto 6 with Ensembles_DB.
    revert B rho1 rho2 e B'.
    induction k as [ k IH' ] using lt_wf_rec1. intros B rho1 rho2 e B'.
    induction B; intros Hyp Hpre.
    - simpl. apply preord_env_P_extend.
      + eapply preord_env_P_antimon; [ now eapply IHB; eauto | ]...
      + rewrite preord_val_eq.
        intros vs1 vs2 j t1 xs1 e1 rho1' Hlen Hf' Hs.
        edestruct (@set_lists_length val) with (vs2 := vs2) as [rho2' Hs']; eauto.
        exists xs1, (tail_letapp e1), rho2'. split; [ now eapply tail_letapp_find_def; eauto | ].
        split; [ now eauto |]. intros Hleq Hpre'.
        eapply Hyp. lia.
        eapply preord_env_P_set_lists_l; [| | eauto | eauto | eauto].
        * eapply IH'; eauto. intros. eapply Hyp; eauto. lia.
          eapply (preord_env_P_monotonic _ _ _ k); eauto. lia.
        * intros x Hin Hfr. simpl.
          apply find_def_correct in Hf'; eauto.
          specialize (occurs_free_in_fun _ _ _ _ _ Hf' x Hfr); intros H1.
          inv H1; eauto; try contradiction. inv H.
          now right; eauto. now left; eauto.
    - simpl. intros x HP. inv HP. inv H. apply Hpre; eauto.
      apply Hpre; eauto. inv H.
  Qed.

  Lemma Forall2_fst_tail_letapp (l : list (ctor_tag * exp)) :
    Forall2 (fun p p' => fst p = fst p') l (map (fun b => (fst b, tail_letapp (snd b))) l).
  Proof. induction l; simpl; constructor; eauto. Qed.

  Lemma tail_letapp_preord_exp k e rho1 rho2 :
    preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
    preord_exp cenv PG PG k (e, rho1) (tail_letapp e, rho2).
  Proof with eauto with Ensembles_DB.
    assert (Hprops : Post_properties cenv PG PG PG) by (eapply inline_bound_compat; lia).
    revert e rho1 rho2.
    induction k as [ k IH ] using lt_wf_rec1.
    intros e. revert k IH.
    induction e using exp_ind'; intros k IH rho rho' Henv; inv Hprops.
    - eapply preord_exp_constr_compat; eauto; intros.
      * eapply Forall2_same. intros x HIn. apply Henv. now constructor.
      * eapply IHe. intros. eapply IH; eauto. lia.
        eapply preord_env_P_extend.
        eapply preord_env_P_antimon. eapply preord_env_P_monotonic; [| eassumption ].
        lia.
        now (normalize_occurs_free; eauto with Ensembles_DB).
        rewrite preord_val_eq. constructor; eauto.
    - eapply preord_exp_case_nil_compat. now eauto.
    - eapply preord_exp_case_cons_compat; eauto.
      eapply Forall2_fst_tail_letapp.
      intros m Hlt. apply IHe; try eassumption.
      intros. eapply IH; eauto. lia.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      normalize_occurs_free. sets.
      eapply IHe0; eauto.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      normalize_occurs_free. sets.
    - eapply preord_exp_proj_compat; eauto.
      intros m v1 v2 Hlt Hval. apply IHe; try eassumption.
      intros. eapply IH; eauto. lia.
      eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      now (normalize_occurs_free; eauto with Ensembles_DB).
    - destruct (tail_letapp_Eletapp x f ft ys e) as [[Heq Htl] | Htl]; rewrite Htl.
      + subst. eapply preord_exp_tail_letapp.
        eapply Henv. constructor. now left.
        eapply Forall2_same. intros. apply Henv. constructor. now right.
      + eapply preord_exp_letapp_compat; eauto.
        eapply Henv. constructor. now left.
        eapply Forall2_same. intros. apply Henv. constructor. now right.
        intros m v1 v2 Hlt Hval.
        eapply IHe; try eassumption.
        intros. eapply IH; eauto. lia.
        eapply preord_env_P_extend; eauto.
        eapply preord_env_P_antimon.
        eapply preord_env_P_monotonic; [| eassumption ]. lia.
        now (normalize_occurs_free; eauto with Ensembles_DB).
    - eapply preord_exp_fun_compat; eauto.
      eapply IHe; try eassumption.
      intros. eapply IH; eauto. lia.
      eapply preord_env_P_antimon.
      eapply tail_letapp_def_funs; eauto.
      intros. eapply IH; eauto. lia.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      now eapply occurs_free_Efun_Included.
    - eapply preord_exp_app_compat. now eauto. now eauto.
      intros x HP. apply Henv; eauto.
      apply Forall2_same. intros. apply Henv. now constructor.
    - eapply preord_exp_prim_val_compat; eauto.
      intros m Hlt. eapply IHe; try eassumption.
      intros. eapply IH. lia. assumption.
      eapply preord_env_P_extend; eauto.
      eapply preord_env_P_antimon.
      eapply preord_env_P_monotonic; [| eassumption ]. lia.
      now (normalize_occurs_free; eauto with Ensembles_DB).
      rewrite preord_val_eq; eauto. reflexivity.
    - eapply preord_exp_prim_compat; eauto; intros.
      eapply Forall2_same. intros. apply Henv. now constructor.
    - eapply preord_exp_halt_compat; try eassumption. now eauto. now eauto.
      intros x HP. apply Henv; eauto.
  Qed.

  (** * Top-level statement *)

  Lemma tail_letapp_correct_top e :
    unique_bindings e ->
    Disjoint _ (bound_var e) (occurs_free e) ->
    unique_bindings (tail_letapp e) /\
    Disjoint _ (bound_var (tail_letapp e)) (occurs_free (tail_letapp e)) /\
    occurs_free (tail_letapp e) \subset occurs_free e /\
    bound_var (tail_letapp e) \subset bound_var e /\
    (forall k rho1 rho2,
        preord_env_P cenv PG (occurs_free e) k rho1 rho2 ->
        preord_exp cenv PG PG k (e, rho1) (tail_letapp e, rho2)).
  Proof.
    intros Hun Hdis.
    destruct (proj1 tail_letapp_syntactic e) as [Hbv [Hfv Hub]].
    split; [| split; [| split; [| split ] ] ]; eauto.
    - eapply Disjoint_Included; [| | eassumption ]; eassumption.
    - intros. eapply tail_letapp_preord_exp. eassumption.
  Qed.

End TailLetapp.
