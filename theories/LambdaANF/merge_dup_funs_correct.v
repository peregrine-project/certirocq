(** Correctness of [merge_dup_funs].

    One round of the pass turns [Efun fds k] into [Efun (rename_fds σ K) (rename_exp σ k)],
    where [K] are the kept functions and [σ] maps each dropped function [f] to a kept
    function [g] such that [fundef_eqb f g]: the body of [f], with [f] renamed to [g], is
    alpha-equivalent to the body of [g].  Source and target take the same steps, so
    [simple_bound 0] is the local and the global post-condition.

    The proof relates source and target environments along the (non-injective) renaming
    [rn σ]: a source variable [x] corresponds to the target variable [rn σ x].
    - [rename_preord_exp]: [e] is related to [rename_exp σ e].
    - [alpha_preord_exp]: if [exp_alpha_eqb f g σl ρl e1 e2 = true] then [e1] is related
      to [rename_exp σ e2]; this is the soundness of the boolean check.
    - [def_funs_inj]: closures of two function bundles are related along a renaming when
      their bodies are; used both for nested [Efun]s and for the merged bundle.
    - [merge_list_spec]: what [merge_list] computes. *)

From Stdlib Require Import Arith.PeanoNat Arith.Wf_nat PArith.BinPos NArith.BinNat Relations.Relations Lists.List micromega.Lia Sets.Ensembles.
Require Import LambdaANF.term LambdaANF.eval LambdaANF.identifiers LambdaANF.Ensembles_util
        LambdaANF.List_util LambdaANF.tactics LambdaANF.set_util LambdaANF.algebra LambdaANF.map_util
        LambdaANF.logical_relations LambdaANF.alpha_conv LambdaANF.bounds LambdaANF.merge_dup_funs.

Import ListNotations.

Section MergeDupFunsCorrect.

  Context (cenv : ctor_env).

  Local Notation PG := (simple_bound 0).

  Lemma PG_props : Post_properties cenv PG PG PG.
  Proof. eapply simple_bound_compat. Qed.

  (** * Renamings *)

  Definition Dom (σ : M.t var) : Ensemble var := fun x => exists y, M.get x σ = Some y.
  Definition Ran (σ : M.t var) : Ensemble var := fun y => exists x, M.get x σ = Some y.
  Definition DR (σ : M.t var) : Ensemble var := Dom σ :|: Ran σ.

  Lemma rn_not_Dom σ x : ~ Dom σ x -> rn σ x = x.
  Proof.
    unfold rn, Dom. intros H. destruct (M.get x σ) eqn:Hg; eauto. exfalso; eauto.
  Qed.

  Lemma rn_not_DR σ x : ~ DR σ x -> rn σ x = x.
  Proof. intros H. eapply rn_not_Dom. intros Hc. apply H. now left. Qed.

  Lemma rn_neq σ x z : ~ DR σ x -> z <> x -> rn σ z <> x.
  Proof.
    unfold rn, DR, Dom, Ran. intros H Hneq Heq. destruct (M.get z σ) eqn:Hg; subst; eauto.
    apply H. right. eauto.
  Qed.

  Lemma rn_cases σ x : (rn σ x = x /\ ~ Dom σ x) \/ (Dom σ x /\ Ran σ (rn σ x)).
  Proof.
    unfold rn, Dom, Ran. destruct (M.get x σ) eqn:Hg.
    - right. split; eauto.
    - left. split; eauto. intros [y Hy]. congruence.
  Qed.

  Lemma find_def_rename σ f B :
    find_def f (rename_fds σ B) =
    match find_def f B with Some (t, xs, e) => Some (t, xs, rename_exp σ e) | None => None end.
  Proof.
    induction B; simpl; eauto. destruct (M.elt_eq f v); eauto.
  Qed.

  Lemma name_in_fundefs_rename σ B :
    name_in_fundefs (rename_fds σ B) <--> name_in_fundefs B.
  Proof.
    induction B; simpl; [| reflexivity ].
    rewrite IHB. reflexivity.
  Qed.

  Lemma Forall2_fst_rename σ (l : list (ctor_tag * exp)) :
    Forall2 (fun p p' => fst p = fst p') l (map (fun b => (fst b, rename_exp σ (snd b))) l).
  Proof. induction l; simpl; constructor; eauto. Qed.

  Ltac not_bv :=
    let Hc := fresh "Hc" in
    intro Hc;
    match goal with
    | [ Hn : ~ _ |- False ] =>
      apply Hn; match goal with [ Hs : _ \subset _ |- _ ] => eapply Hs; eassumption end
    end.

  Lemma rename_syntactic σ :
    (forall e,
        bound_var (rename_exp σ e) \subset bound_var e /\
        (unique_bindings e -> unique_bindings (rename_exp σ e))) /\
    (forall B,
        bound_var_fundefs (rename_fds σ B) \subset bound_var_fundefs B /\
        (unique_bindings_fundefs B -> unique_bindings_fundefs (rename_fds σ B))).
  Proof.
    eapply exp_def_mutual_ind.
    - intros x c ys e [Hbv Hub]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x. simpl. split; [| intros; constructor ].
      intros z Hz; inv Hz; match goal with H : List.In _ [] |- _ => inv H end.
    - intros x bs c e [Hbv Hub] [Hbvs Hubs]. simpl in *.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
      eapply Disjoint_Included; [| | eassumption ]; eauto.
    - intros x c n y e [Hbv Hub]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x f ft ys e [Hbv Hub]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros B [Hbvs Hubs] e [Hbv Hub]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
      eapply Disjoint_Included; [| | eassumption ]; eauto.
    - intros. simpl. split; [ intros z Hz; inv Hz | intros; constructor ].
    - intros x p e [Hbv Hub]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x p ys e [Hbv Hub]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
    - intros x. simpl. split; [ intros z Hz; inv Hz | intros; constructor ].
    - intros f ft xs e [Hbv Hub] B [Hbvs Hubs]. simpl.
      repeat normalize_bound_var.
      split; [ sets | ].
      intros Hu; inv Hu. constructor; eauto; try not_bv.
      all: match goal with
           | [ H : Disjoint _ _ _ |- _ ] =>
             eapply Disjoint_Included; [ | | exact H ]; solve [ eassumption | sets ]
           end.
    - simpl. split; [ sets | now auto ].
  Qed.

  Lemma rn_FromList σ ys z :
    FromList (map (rn σ) ys) z -> (FromList ys z /\ ~ Dom σ z) \/ Ran σ z.
  Proof.
    unfold FromList, Ensembles.In. intros Hz. eapply in_map_iff in Hz.
    destruct Hz as [y [Heq Hin]]. subst.
    destruct (rn_cases σ y) as [[Heq Hd] | [Hd Hr]]; eauto.
    rewrite Heq. eauto.
  Qed.

  Lemma rename_occurs_free σ :
    (forall e z, occurs_free (rename_exp σ e) z -> (occurs_free e z /\ ~ Dom σ z) \/ Ran σ z) /\
    (forall B z, occurs_free_fundefs (rename_fds σ B) z ->
                 (occurs_free_fundefs B z /\ ~ Dom σ z) \/ Ran σ z).
  Proof.
    eapply exp_def_mutual_ind; simpl.
    - intros x c ys e IHe z Hz. inv Hz.
      + destruct (rn_FromList σ ys z) as [[? ?] | ?]; eauto.
      + destruct (IHe z) as [[? ?] | ?]; eauto.
    - intros x z Hz. inv Hz.
      destruct (rn_cases σ x) as [[Heq Hd] | [Hd Hr]]; eauto. rewrite Heq; eauto.
    - intros x bs c e IHe IHbs z Hz. inv Hz.
      + destruct (rn_cases σ x) as [[Heq Hd] | [Hd Hr]]; eauto. rewrite Heq; eauto.
      + destruct (IHe z) as [[? ?] | ?]; eauto.
      + destruct (IHbs z) as [[Hfv ?] | ?]; eauto.
    - intros x c n y e IHe z Hz. inv Hz.
      + destruct (rn_cases σ y) as [[Heq Hd] | [Hd Hr]]; eauto. rewrite Heq; eauto.
      + destruct (IHe z) as [[? ?] | ?]; eauto.
    - intros x f ft ys e IHe z Hz. inv Hz.
      all: first [ solve [ destruct (rn_cases σ f) as [[Heq Hd] | [Hd Hr]]; eauto; rewrite Heq; eauto ]
                 | solve [ destruct (rn_FromList σ ys z) as [[? ?] | ?]; eauto ]
                 | solve [ destruct (rn_FromList σ (f :: ys) z) as [[? ?] | ?]; eauto ]
                 | solve [ destruct (IHe z) as [[? ?] | ?]; eauto ] ].
    - intros B IHB e IHe z Hz. inv Hz.
      + destruct (IHe z) as [[? ?] | ?]; eauto.
        left. split; eauto. constructor; eauto. intros Hc.
        match goal with H : ~ name_in_fundefs _ _ |- _ => eapply H end.
        eapply name_in_fundefs_rename. eassumption.
      + destruct (IHB z) as [[? ?] | ?]; eauto.
    - intros f ft ys z Hz. inv Hz.
      all: first [ solve [ destruct (rn_cases σ f) as [[Heq Hd] | [Hd Hr]]; eauto; rewrite Heq; eauto ]
                 | solve [ destruct (rn_FromList σ ys z) as [[? ?] | ?]; eauto ]
                 | solve [ destruct (rn_FromList σ (f :: ys) z) as [[? ?] | ?]; eauto ] ].
    - intros x p e IHe z Hz. inv Hz. destruct (IHe z) as [[? ?] | ?]; eauto.
    - intros x p ys e IHe z Hz. inv Hz.
      + destruct (rn_FromList σ ys z) as [[? ?] | ?]; eauto.
      + destruct (IHe z) as [[? ?] | ?]; eauto.
    - intros x z Hz. inv Hz.
      destruct (rn_cases σ x) as [[Heq Hd] | [Hd Hr]]; eauto. rewrite Heq; eauto.
    - intros f ft xs e IHe B IHB z Hz. inv Hz.
      + destruct (IHe z) as [[? ?] | ?]; eauto.
        left. split; eauto. constructor; eauto. intros Hc.
        match goal with H : ~ name_in_fundefs _ _ |- _ => eapply H end.
        eapply name_in_fundefs_rename. eassumption.
      + destruct (IHB z) as [[? ?] | ?]; eauto.
    - intros z Hz. inv Hz.
  Qed.

  (** * Environments related along a renaming *)

  Lemma inj_set σ S k rho1 rho2 x v1 v2 :
    preord_env_P_inj cenv PG (S \\ [set x]) k (rn σ) rho1 rho2 ->
    preord_val cenv PG k v1 v2 ->
    ~ DR σ x ->
    preord_env_P_inj cenv PG S k (rn σ) (M.set x v1 rho1) (M.set x v2 rho2).
  Proof.
    intros Henv Hv Hx z Hz v Hget.
    destruct (Pos.eq_dec z x); subst.
    - rewrite M.gss in Hget. inv Hget. rewrite rn_not_DR; eauto.
      eexists. rewrite M.gss. eauto.
    - rewrite M.gso in Hget; eauto. edestruct Henv as [v' [Hget' Hv']]; eauto.
      constructor; eauto. intros Hc; inv Hc; eauto.
      eexists. rewrite M.gso; eauto. eapply rn_neq; eauto.
  Qed.

  Lemma inj_set_lists σ S k xs vs1 vs2 rho1 rho2 rho1' rho2' :
    preord_env_P_inj cenv PG (S \\ FromList xs) k (rn σ) rho1 rho2 ->
    Forall2 (preord_val cenv PG k) vs1 vs2 ->
    (forall x, List.In x xs -> ~ DR σ x) ->
    set_lists xs vs1 rho1 = Some rho1' ->
    set_lists xs vs2 rho2 = Some rho2' ->
    preord_env_P_inj cenv PG S k (rn σ) rho1' rho2'.
  Proof.
    revert S vs1 vs2 rho1' rho2'.
    induction xs as [| a xs IHxs ]; intros S vs1 vs2 rho1' rho2' Henv Hall Hxs Hs1 Hs2.
    - destruct vs1; destruct vs2; simpl in *; try congruence. inv Hs1; inv Hs2.
      eapply preord_env_P_inj_antimon; [ eassumption | ].
      intros z Hz. constructor; [ eassumption | intros Hc; inv Hc ].
    - destruct vs1 as [| v1 vs1]; destruct vs2 as [| v2 vs2]; simpl in *; try congruence. inv Hall.
      destruct (set_lists xs vs1 rho1) eqn:Hs1'; try congruence.
      destruct (set_lists xs vs2 rho2) eqn:Hs2'; try congruence. inv Hs1; inv Hs2.
      eapply inj_set; eauto.
      eapply IHxs; eauto. eapply preord_env_P_inj_antimon; [ eassumption | ].
      intros z Hz. inv Hz. inv H. constructor; eauto. intros Hc. inv Hc; eauto.
  Qed.

  (** Function bundles whose bodies are related give related closures. *)
  Lemma def_funs_inj (r : var -> var) k S B1 B2 rho1 rho2 :
    (forall f t xs1 e1,
        find_def f B1 = Some (t, xs1, e1) ->
        exists xs2 e2, find_def (r f) B2 = Some (t, xs2, e2) /\ length xs1 = length xs2) ->
    (forall m, m < k ->
       forall f t xs1 e1 xs2 e2 vs1 vs2 rho1' rho2',
         find_def f B1 = Some (t, xs1, e1) ->
         find_def (r f) B2 = Some (t, xs2, e2) ->
         Forall2 (preord_val cenv PG m) vs1 vs2 ->
         set_lists xs1 vs1 (def_funs B1 B1 rho1 rho1) = Some rho1' ->
         set_lists xs2 vs2 (def_funs B2 B2 rho2 rho2) = Some rho2' ->
         preord_env_P_inj cenv PG (S :|: name_in_fundefs B1) m r
                          (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2) ->
         preord_exp cenv PG PG m (e1, rho1') (e2, rho2')) ->
    (forall x, S x -> ~ name_in_fundefs B1 x -> ~ name_in_fundefs B2 (r x)) ->
    preord_env_P_inj cenv PG S k r rho1 rho2 ->
    preord_env_P_inj cenv PG (S :|: name_in_fundefs B1) k r
                     (def_funs B1 B1 rho1 rho1) (def_funs B2 B2 rho2 rho2).
  Proof.
    revert rho1 rho2.
    induction k as [ k IH ] using lt_wf_rec1.
    intros rho1 rho2 Hstruct Hsem Hneq Henv x Hx v Hget.
    destruct (Decidable_name_in_fundefs B1) as [Dec]. destruct (Dec x) as [Hin | Hnin].
    - rewrite def_funs_eq in Hget; eauto. inv Hget.
      edestruct name_in_fundefs_find_def_is_Some as [t [xs1 [e1 Hfd1]]]; eauto.
      edestruct Hstruct as [xs2 [e2 [Hfd2 Hlen]]]; eauto.
      eexists. split. eapply def_funs_eq. eapply find_def_name_in_fundefs. eassumption.
      rewrite preord_val_eq.
      intros vs1 vs2 j t' xs1' e1' rho1' Hlen' Hf' Hs. symmetry in Hs.
      rewrite Hfd1 in Hf'. inv Hf'.
      edestruct set_lists_length2 with (xs2 := xs2) (vs2 := vs2) (rho' := def_funs B2 B2 rho2 rho2)
        as [rho2' Hs']; eauto.
      exists xs2, e2, rho2'. split; [ eassumption | ]. split; [ now rewrite Hs' | ].
      intros Hlt Hall. eapply Hsem; eauto.
      eapply IH; eauto.
      + intros. eapply Hsem; eauto. lia.
      + eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
    - inv Hx; try contradiction.
      rewrite def_funs_neq in Hget; eauto.
      edestruct Henv as [v' [Hget' Hv']]; eauto.
      eexists. rewrite def_funs_neq; eauto.
  Qed.

  (** * [e] is related to [rename_exp σ e] *)

  Section Rename.

    Context (σ : M.t var).

    Lemma rename_preord_exp k e rho1 rho2 :
      (forall y, bound_var e y -> ~ DR σ y) ->
      preord_env_P_inj cenv PG (occurs_free e) k (rn σ) rho1 rho2 ->
      preord_exp cenv PG PG k (e, rho1) (rename_exp σ e, rho2).
    Proof with eauto with Ensembles_DB.
      assert (Hprops := PG_props).
      revert e rho1 rho2.
      induction k as [ k IH ] using lt_wf_rec1.
      intros e. revert k IH.
      induction e using exp_ind'; intros k IH rho rho' Hbv Henv; inv Hprops; cbn [rename_exp].
      - eapply preord_exp_constr_compat; eauto; intros.
        + eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. sets.
        + eapply IHe; eauto.
          * intros. eapply IH; eauto. lia.
          * eapply inj_set; eauto.
            eapply preord_env_P_inj_antimon. eapply preord_env_P_inj_monotonic; [| eassumption ].
            lia. normalize_occurs_free. sets.
            rewrite preord_val_eq. constructor; eauto.
      - eapply preord_exp_case_nil_compat. now eauto.
      - eapply preord_exp_case_cons_compat; eauto.
        + eapply Forall2_fst_rename.
        + intros m Hlt. apply IHe; try eassumption.
          * intros. eapply IH; eauto. lia.
          * intros y Hy. eapply Hbv. econstructor. eassumption. now left.
          * eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
            normalize_occurs_free. sets.
        + eapply IHe0; eauto.
          * intros y Hy. eapply Hbv. inv Hy. econstructor. eassumption. now right.
          * eapply preord_env_P_inj_antimon. eassumption.
            normalize_occurs_free. sets.
      - eapply preord_exp_proj_compat; eauto.
        intros m v1 v2 Hlt Hval. eapply IHe; eauto.
        + intros. eapply IH; eauto. lia.
        + eapply inj_set; eauto.
          eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets.
      - eapply preord_exp_letapp_compat; eauto.
        + eapply Henv. constructor. now left.
        + eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. sets.
        + intros m v1 v2 Hlt Hval.
          eapply IHe; eauto.
          * intros. eapply IH; eauto. lia.
          * eapply inj_set; eauto.
            eapply preord_env_P_inj_antimon.
            eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
            normalize_occurs_free. sets.
      - eapply preord_exp_fun_compat; eauto.
        eapply IHe; eauto.
        + intros. eapply IH; eauto. lia.
        + eapply preord_env_P_inj_antimon; [| now eapply occurs_free_Efun_Included ].
          eapply def_funs_inj with (S := occurs_free (Efun f2 e)).
          * intros f t xs1 e1 Hfd.
            rewrite rn_not_DR. rewrite find_def_rename, Hfd. eauto.
            eapply Hbv. constructor. eapply fun_in_fundefs_bound_var_fundefs.
            eapply find_def_correct. eassumption. now left.
          * intros m Hlt f t xs1 e1 xs2 e2 vs1 vs2 rho1' rho2' Hfd1 Hfd2 Hall Hs1 Hs2 Henv'.
            assert (Hbvf : forall y, bound_var_fundefs f2 y -> ~ DR σ y) by eauto.
            assert (Hfun := find_def_correct _ _ _ _ _ Hfd1).
            assert (Hsub := fun_in_fundefs_bound_var_fundefs _ _ _ _ _ Hfun).
            rewrite rn_not_DR in Hfd2; [| eapply Hbvf; eapply Hsub; now left ].
            rewrite find_def_rename, Hfd1 in Hfd2. inv Hfd2.
            eapply IH. lia.
            -- intros y Hy. eapply Hbvf. eapply Hsub. right. now right.
            -- eapply inj_set_lists; [| eassumption | | eassumption | eassumption ].
               ++ eapply preord_env_P_inj_antimon. eassumption.
                  eapply Setminus_Included_Included_Union.
                  eapply Included_trans. eapply occurs_free_in_fun. eassumption.
                  normalize_occurs_free. sets.
               ++ intros y Hy. eapply Hbvf. eapply Hsub. right. now left.
          * intros x Hx Hnin Hc. apply (proj1 (name_in_fundefs_rename σ f2)) in Hc.
            destruct (rn_cases σ x) as [[Heq Hd] | [Hd Hr]].
            -- rewrite Heq in Hc. eauto.
            -- eapply (Hbv (rn σ x)).
               constructor. eapply name_in_fundefs_bound_var_fundefs. eassumption.
               now right.
          * eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
      - eapply preord_exp_app_compat. now eauto. now eauto.
        eapply Henv; eauto.
        eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. sets.
      - eapply preord_exp_prim_val_compat; eauto.
        intros m Hlt. eapply IHe; eauto.
        + intros. eapply IH; eauto. lia.
        + eapply inj_set; eauto.
          eapply preord_env_P_inj_antimon.
          eapply preord_env_P_inj_monotonic; [| eassumption ]. lia.
          normalize_occurs_free. sets.
          rewrite preord_val_eq; eauto. reflexivity.
      - eapply preord_exp_prim_compat; eauto; intros.
        eapply Forall2_preord_var_env_map. eassumption. normalize_occurs_free. sets.
      - eapply preord_exp_halt_compat; try eassumption. now eauto. now eauto.
        eapply Henv; eauto.
    Qed.

  End Rename.

  (** * Soundness of [exp_alpha_eqb] *)

  Lemma lazy_and (a b : bool) : (if a then b else false) = true -> a = true /\ b = true.
  Proof. destruct a; [ eauto | discriminate ]. Qed.

  Ltac split_checks :=
    repeat match goal with
           | [ H : (if ?a then ?b else false) = true |- _ ] =>
             let H1 := fresh "Hc" in let H2 := fresh "Hc" in
             apply lazy_and in H; destruct H as [H1 H2]
           | [ H : Pos.eqb _ _ = true |- _ ] => apply Pos.eqb_eq in H; subst
           | [ H : N.eqb _ _ = true |- _ ] => apply N.eqb_eq in H; subst
           | [ H : Nat.eqb _ _ = true |- _ ] => apply Nat.eqb_eq in H
           end.

  Section Alpha.

    Context (σ : M.t var) (f1 f2 : var).

    (* Renaming [f1] to [f2] and then applying [σ] is the same as applying [σ]. *)
    Context (Hsw : forall x, rn σ (if Pos.eqb x f1 then f2 else x) = rn σ x).

    (** A source variable [x] and a target variable [y] that the check accepts hold
        related values, [y] being renamed by [σ] in the target. *)
    Definition alpha_env (σl ρl : M.t var) (S : Ensemble var) k rho1 rho2 :=
      forall x y, S x -> var_eqb f1 f2 σl ρl x y = true ->
                  preord_var_env cenv PG k rho1 rho2 x (rn σ y).

    (* The bound variables of the target are not touched by [σ]. *)
    Definition ran_ok (σl : M.t var) := forall x y, M.get x σl = Some y -> ~ DR σ y.

    Lemma alpha_env_antimon σl ρl S1 S2 k rho1 rho2 :
      alpha_env σl ρl S2 k rho1 rho2 -> S1 \subset S2 -> alpha_env σl ρl S1 k rho1 rho2.
    Proof. intros Henv Hsub x y Hx. eapply Henv. eapply Hsub. eassumption. Qed.

    Lemma alpha_env_monotonic σl ρl S k j rho1 rho2 :
      j <= k -> alpha_env σl ρl S k rho1 rho2 -> alpha_env σl ρl S j rho1 rho2.
    Proof.
      intros Hle Henv x y Hx Heq. eapply preord_var_env_monotonic; [| eassumption ].
      eapply Henv; eassumption.
    Qed.

    Lemma ran_ok_set σl x1 x2 : ran_ok σl -> ~ DR σ x2 -> ran_ok (M.set x1 x2 σl).
    Proof.
      intros Hok Hx x y Hg. destruct (Pos.eq_dec x x1); subst.
      - rewrite M.gss in Hg. inv Hg. eassumption.
      - rewrite M.gso in Hg; eauto.
    Qed.

    Lemma alpha_env_set σl ρl S k rho1 rho2 x1 x2 v1 v2 :
      alpha_env σl ρl (S \\ [set x1]) k rho1 rho2 ->
      preord_val cenv PG k v1 v2 ->
      ran_ok σl -> ~ DR σ x2 ->
      alpha_env (M.set x1 x2 σl) (M.set x2 x1 ρl) S k (M.set x1 v1 rho1) (M.set x2 v2 rho2).
    Proof.
      intros Henv Hv Hok Hx2 x y Hx Heq. unfold var_eqb in Heq.
      destruct (Pos.eq_dec x x1); subst.
      - rewrite M.gss in Heq.
        destruct (M.get y (M.set x2 x1 ρl)) eqn:Hy; [| discriminate ].
        split_checks.
        intros v Hget. rewrite M.gss in Hget. inv Hget.
        rewrite rn_not_DR; eauto. eexists. rewrite M.gss. eauto.
      - rewrite M.gso in Heq; eauto.
        assert (Hx' : (S \\ [set x1]) x) by (constructor; eauto; intros Hc; inv Hc; eauto).
        destruct (M.get x σl) eqn:Hxs.
        + destruct (M.get y (M.set x2 x1 ρl)) eqn:Hy; [| discriminate ].
          split_checks.
          destruct (Pos.eq_dec y x2); subst.
          * rewrite M.gss in Hy. inv Hy. congruence.
          * rewrite M.gso in Hy; eauto.
            assert (Hold : var_eqb f1 f2 σl ρl x y = true).
            { unfold var_eqb. rewrite Hxs, Hy, !Pos.eqb_refl. reflexivity. }
            intros v Hget. rewrite M.gso in Hget; eauto.
            edestruct (Henv x y) as [v' [Hg' Hv']]; eauto.
            eexists. rewrite M.gso; eauto. rewrite rn_not_DR in *; eauto.
        + destruct (M.get y (M.set x2 x1 ρl)) eqn:Hy; [ discriminate | ].
          destruct (Pos.eq_dec y x2); subst.
          * rewrite M.gss in Hy. discriminate.
          * rewrite M.gso in Hy; eauto.
            assert (Hold : var_eqb f1 f2 σl ρl x y = true).
            { unfold var_eqb. rewrite Hxs, Hy. eassumption. }
            intros v Hget. rewrite M.gso in Hget; eauto.
            edestruct (Henv x y) as [v' [Hg' Hv']]; eauto.
            eexists. rewrite M.gso; eauto. eapply rn_neq; eauto.
    Qed.

    Lemma alpha_env_vars σl ρl S k rho1 rho2 xs ys :
      alpha_env σl ρl S k rho1 rho2 -> FromList xs \subset S ->
      vars_eqb f1 f2 σl ρl xs ys = true ->
      Forall2 (preord_var_env cenv PG k rho1 rho2) xs (map (rn σ) ys).
    Proof.
      revert ys. induction xs as [| x xs IHxs ]; intros ys Henv Hsub Heq;
        destruct ys as [| y ys ]; cbn [vars_eqb] in Heq; try discriminate; simpl; constructor.
      - apply lazy_and in Heq. destruct Heq as [Heq1 Heq2].
        eapply Henv; [| eassumption ]. eapply Hsub. now left.
      - apply lazy_and in Heq. destruct Heq as [Heq1 Heq2].
        eapply IHxs; eauto. intros z Hz. eapply Hsub. now right.
    Qed.

    Lemma alpha_case_fst σl ρl x1 x2 bs1 bs2 :
      exp_alpha_eqb f1 f2 σl ρl (Ecase x1 bs1) (Ecase x2 bs2) = true ->
      Forall2 (fun p p' => fst p = fst p') bs1 (map (fun b => (fst b, rename_exp σ (snd b))) bs2).
    Proof.
      intros Heq. cbn [exp_alpha_eqb] in Heq. apply lazy_and in Heq. destruct Heq as [_ Heq].
      revert bs2 Heq. induction bs1 as [| [c1 b1] bs1 IHbs ]; intros [| [c2 b2] bs2 ] Heq;
        try discriminate; simpl; constructor.
      - split_checks. reflexivity.
      - split_checks. eapply IHbs. eassumption.
    Qed.

    Lemma alpha_preord_exp e1 :
      forall e2 σl ρl k rho1 rho2,
        exp_alpha_eqb f1 f2 σl ρl e1 e2 = true ->
        (forall y, bound_var e2 y -> ~ DR σ y) ->
        ran_ok σl ->
        alpha_env σl ρl (occurs_free e1) k rho1 rho2 ->
        preord_exp cenv PG PG k (e1, rho1) (rename_exp σ e2, rho2).
    Proof.
      assert (Hprops := PG_props).
      induction e1 using exp_ind'; intros e2 σl ρl k rho1 rho2 Heq Hbv Hok Henv; inv Hprops;
        destruct e2; cbn [exp_alpha_eqb] in Heq; try discriminate; cbn [rename_exp].
      - (* Econstr *)
        split_checks.
        eapply preord_exp_constr_compat; eauto.
        + eapply alpha_env_vars; [ eassumption | normalize_occurs_free; sets | eassumption ].
        + intros m vs1 vs2 Hlt Hall. eapply IHe1; eauto.
          * eapply ran_ok_set; eauto.
          * eapply alpha_env_set; eauto.
            -- eapply alpha_env_monotonic; [| eapply alpha_env_antimon; [ eassumption | ] ]. lia.
               normalize_occurs_free. sets.
            -- rewrite preord_val_eq. constructor; eauto.
      - (* Ecase nil *)
        destruct l; split_checks; try discriminate.
        eapply preord_exp_case_nil_compat. now eauto.
      - (* Ecase cons *)
        destruct l0 as [| [c2 b2] bs2 ]; split_checks; try discriminate.
        assert (Htl : exp_alpha_eqb f1 f2 σl ρl (Ecase v l) (Ecase v0 bs2) = true).
        { cbn [exp_alpha_eqb]. rewrite Hc. eassumption. }
        eapply preord_exp_case_cons_compat; eauto.
        + eapply alpha_case_fst. eassumption.
        + intros m Hlt. eapply IHe1; eauto.
          * intros y Hy. eapply Hbv. econstructor. eassumption. now left.
          * eapply alpha_env_monotonic; [| eapply alpha_env_antimon; [ eassumption | ] ]. lia.
            normalize_occurs_free. sets.
        + eapply (IHe0 (Ecase v0 bs2)); eauto.
          * intros y Hy. eapply Hbv. inv Hy. econstructor. eassumption. now right.
          * eapply alpha_env_antimon. eassumption. normalize_occurs_free. sets.
      - (* Eproj *)
        split_checks.
        eapply preord_exp_proj_compat; [ now eauto | now eauto | eapply Henv; now eauto | ].
        + intros m w1 w2 Hlt Hval. eapply IHe1; eauto.
          * eapply ran_ok_set; eauto.
          * eapply alpha_env_set; eauto.
            eapply alpha_env_monotonic; [| eapply alpha_env_antimon; [ eassumption | ] ]. lia.
            normalize_occurs_free. sets.
      - (* Eletapp *)
        split_checks.
        eapply preord_exp_letapp_compat; [ now eauto | now eauto | now eauto | eapply Henv; [ constructor; now left | eassumption ] | | ].
        + eapply alpha_env_vars; [ eassumption | normalize_occurs_free; sets | eassumption ].
        + intros m w1 w2 Hlt Hval. eapply IHe1; eauto.
          * eapply ran_ok_set; eauto.
          * eapply alpha_env_set; eauto.
            eapply alpha_env_monotonic; [| eapply alpha_env_antimon; [ eassumption | ] ]. lia.
            normalize_occurs_free. sets.
      - (* Eapp *)
        split_checks.
        eapply preord_exp_app_compat. now eauto. now eauto.
        + eapply Henv; eauto.
        + eapply alpha_env_vars; [ eassumption | normalize_occurs_free; sets | eassumption ].
      - (* Eprim *)
        split_checks.
        eapply preord_exp_prim_compat; eauto.
        eapply alpha_env_vars; [ eassumption | normalize_occurs_free; sets | eassumption ].
      - (* Ehalt *)
        eapply preord_exp_halt_compat; try eassumption. now eauto. now eauto.
        eapply Henv; eauto.
    Qed.

  End Alpha.

  (** * Lists of functions *)

  Inductive sublist {A} : list A -> list A -> Prop :=
  | sl_nil : sublist [] []
  | sl_keep a l1 l2 : sublist l1 l2 -> sublist (a :: l1) (a :: l2)
  | sl_skip a l1 l2 : sublist l1 l2 -> sublist l1 (a :: l2).

  Lemma sublist_refl {A} (l : list A) : sublist l l.
  Proof. induction l; constructor; eauto. Qed.

  Lemma sublist_trans {A} (l1 l2 l3 : list A) : sublist l1 l2 -> sublist l2 l3 -> sublist l1 l3.
  Proof.
    intros H12 H23. revert l1 H12.
    induction H23; intros l0 H12.
    - inv H12. constructor.
    - inv H12; constructor; eauto.
    - constructor; eauto.
  Qed.

  Lemma sublist_In {A} (l1 l2 : list A) x : sublist l1 l2 -> List.In x l1 -> List.In x l2.
  Proof. intros H. induction H; simpl; intros Hin; try contradiction; eauto. inv Hin; eauto. Qed.

  Lemma sublist_app_drop {A} (a l : list A) d : sublist (a ++ l) (a ++ d :: l).
  Proof. induction a; simpl; constructor; eauto. eapply sublist_refl. Qed.

  Lemma list_to_fds_fds_to_list B : list_to_fds (fds_to_list B) = B.
  Proof. induction B; simpl; congruence. Qed.

  Lemma fun_in_list_to_fds l d : fun_in_fundefs (list_to_fds l) d <-> List.In d l.
  Proof.
    induction l as [| [[[f t] xs] e] l IHl ]; simpl.
    - split; intros H; inv H.
    - split; intros H.
      + inv H. inv H0. now left. right. eapply IHl. eassumption.
      + inv H. left. reflexivity. right. eapply IHl. eassumption.
  Qed.

  Lemma name_in_list_to_fds l x : name_in_fundefs (list_to_fds l) x <-> List.In x (map fundef_name l).
  Proof.
    induction l as [| [[[f t] xs] e] l IHl ]; simpl.
    - split; intros H; inv H.
    - split; intros H.
      + inv H. inv H0. now left. right. eapply IHl. eassumption.
      + inv H. left. reflexivity. right. eapply IHl. eassumption.
  Qed.

  Lemma find_def_list_to_fds l f t xs e :
    NoDup (map fundef_name l) -> List.In (f, t, xs, e) l ->
    find_def f (list_to_fds l) = Some (t, xs, e).
  Proof.
    induction l as [| [[[f' t'] xs'] e'] l IHl ]; simpl; intros Hnd Hin; [ contradiction | ].
    inv Hnd. destruct (M.elt_eq f f'); subst.
    - inv Hin. inv H; eauto. exfalso. eapply H1. eapply in_map_iff. eexists; split; [| eassumption ].
      reflexivity.
    - inv Hin. inv H; congruence. eauto.
  Qed.

  Lemma find_def_In B f t xs e :
    find_def f B = Some (t, xs, e) -> List.In (f, t, xs, e) (fds_to_list B).
  Proof.
    induction B; simpl; intros H; [| discriminate ].
    destruct (M.elt_eq f v); subst; [ inv H; now left | right; eauto ].
  Qed.

  Lemma fds_to_list_In B d : List.In d (fds_to_list B) -> fun_in_fundefs B d.
  Proof.
    rewrite <- (list_to_fds_fds_to_list B) at 2. eapply fun_in_list_to_fds.
  Qed.

  Lemma fds_to_list_name B x : List.In x (map fundef_name (fds_to_list B)) <-> name_in_fundefs B x.
  Proof.
    rewrite <- (list_to_fds_fds_to_list B) at 2. symmetry. eapply name_in_list_to_fds.
  Qed.

  Lemma NoDup_names_eq l d1 d2 :
    NoDup (map fundef_name l) -> List.In d1 l -> List.In d2 l -> fundef_name d1 = fundef_name d2 -> d1 = d2.
  Proof.
    induction l as [| d l IHl ]; simpl; intros Hnd H1 H2 Heq; [ contradiction | ].
    inv Hnd. inv H1; inv H2; eauto.
    - exfalso. eapply H3. rewrite Heq. eapply in_map. eassumption.
    - exfalso. eapply H3. rewrite <- Heq. eapply in_map. eassumption.
  Qed.

  Lemma disj_contra {A} (S1 S2 : Ensemble A) x : Disjoint _ S1 S2 -> S1 x -> S2 x -> False.
  Proof. intros [H] H1 H2. eapply (H x). constructor; eassumption. Qed.

  Lemma ub_NoDup B : unique_bindings_fundefs B -> NoDup (map fundef_name (fds_to_list B)).
  Proof.
    induction B; simpl; intros Hun; constructor; inv Hun; eauto.
    intros Hc. eapply fds_to_list_name in Hc.
    match goal with H : ~ bound_var_fundefs _ _ |- _ => eapply H end.
    eapply name_in_fundefs_bound_var_fundefs. eassumption.
  Qed.

  Lemma ub_fun B f t xs e :
    unique_bindings_fundefs B -> fun_in_fundefs B (f, t, xs, e) ->
    NoDup xs /\ (forall x, FromList xs x \/ bound_var e x -> ~ name_in_fundefs B x).
  Proof.
    induction B as [ g gt gxs ge B IHB |]; simpl; intros Hun Hin; [| now inv Hin ].
    inversion Hun as [ ? ? ? ? ? Hg1 Hg2 Hd1 Hd2 Hd3 Hg3 Hnd Hue HuB |]; subst.
    inversion Hin as [ d Hd | d Hd ]; subst.
    - assert (Heq : (g, gt, gxs, ge) = (f, t, xs, e)) by (inv Hd; reflexivity).
      inv Heq. split; [ eassumption | ]. intros x Hx Hc. destruct Hc as [x Hc | x Hc].
      + inv Hc. destruct Hx as [Hx | Hx]; eauto.
      + eapply name_in_fundefs_bound_var_fundefs in Hc.
        destruct Hx as [Hx | Hx]; [ eapply (disj_contra _ _ x Hd2) | eapply (disj_contra _ _ x Hd3) ]; eassumption.
    - edestruct IHB as [Hnd' Hx]; eauto. split; eauto.
      intros x Hx' Hc. destruct Hc as [x Hc | x Hc].
      + inv Hc. eapply Hg2. eapply fun_in_fundefs_bound_var_fundefs. eassumption.
        destruct Hx'; [ right; now left | right; now right ].
      + eapply Hx; eauto.
  Qed.

  Lemma sublist_fds l1 l2 :
    sublist l1 l2 ->
    (unique_bindings_fundefs (list_to_fds l2) -> unique_bindings_fundefs (list_to_fds l1)) /\
    bound_var_fundefs (list_to_fds l1) \subset bound_var_fundefs (list_to_fds l2).
  Proof.
    intros H. induction H as [| [[[f t] xs] e] l1 l2 H [IH1 IH2] | [[[f t] xs] e] l1 l2 H [IH1 IH2] ];
      simpl in *.
    - split; [ now eauto | reflexivity ].
    - split.
      + intros Hun. inv Hun. constructor; eauto; try not_bv.
        eapply Disjoint_Included_l; [ eassumption | eassumption ].
        eapply Disjoint_Included_r; [ eassumption | eassumption ].
      + rewrite !bound_var_fundefs_Fcons. sets.
    - split.
      + intros Hun. inv Hun. eauto.
      + rewrite !bound_var_fundefs_Fcons. sets.
  Qed.

  Lemma occurs_free_fundefs_sub K B z :
    (forall d, fun_in_fundefs K d -> fun_in_fundefs B d) ->
    occurs_free_fundefs K z -> ~ name_in_fundefs B z -> occurs_free_fundefs B z.
  Proof.
    intros Hsub Hz Hn. eapply occurs_free_fundefs_big_cup in Hz.
    eapply occurs_free_fundefs_big_cup.
    destruct Hz as [[[[f t] xs] e] [Hin Hz]]. inv Hz.
    eexists. split. eapply Hsub. eassumption. constructor; eauto.
  Qed.

  (** * [merge_list] *)

  Lemma find_callee_spec d gs keptm g :
    find_callee d gs keptm = Some g -> exists r, M.get g keptm = Some r /\ fundef_eqb d r = true.
  Proof.
    induction gs; simpl; intros H; [ discriminate | ].
    destruct (M.get a keptm) eqn:Hg; eauto.
    destruct (fundef_eqb d f) eqn:Heq; eauto. inv H. eauto.
  Qed.

  Lemma find_dup_spec d reps g :
    find_dup d reps = Some g -> exists r, List.In r reps /\ fundef_name r = g /\ fundef_eqb d r = true.
  Proof.
    induction reps; simpl; intros H; [ discriminate | ].
    destruct (fundef_eqb d a) eqn:Heq.
    - inv H. eexists. split; eauto.
    - edestruct IHreps as [r [Hin [Hn Hr]]]; eauto.
  Qed.

  Lemma get_bucket_add t n d bs t' n' d' :
    List.In d' (get_bucket t' n' (add_to_bucket t n d bs)) -> d' = d \/ List.In d' (get_bucket t' n' bs).
  Proof.
    unfold get_bucket, add_to_bucket. destruct (Pos.eq_dec t' t); subst.
    - rewrite M.gss. destruct (Pos.eq_dec n' n); subst.
      + rewrite M.gss. intros H. inv H; eauto.
      + rewrite M.gso; eauto. destruct (M.get t bs); eauto; try (rewrite M.gempty; intros H; inv H).
    - rewrite M.gso; eauto.
  Qed.

  Definition merged_ok (L kept : list fundef) (σ : M.t var) :=
    forall f g, M.get f σ = Some g ->
      ~ List.In f (map fundef_name kept) /\
      exists d r, List.In d L /\ fundef_name d = f /\ List.In r kept /\ fundef_name r = g /\
                  fundef_eqb d r = true.

  Lemma merge_list_spec funs L l kept bs keptm σ :
    NoDup (map fundef_name l) ->
    (forall d, List.In d l -> M.get (fundef_name d) σ = None /\ ~ List.In (fundef_name d) (map fundef_name kept)) ->
    (forall t n d, List.In d (get_bucket t n bs) -> List.In d kept) ->
    (forall g r, M.get g keptm = Some r -> List.In r kept /\ fundef_name r = g) ->
    merged_ok L kept σ ->
    sublist (rev kept ++ l) L ->
    (forall d, List.In d L -> List.In d l \/ List.In d kept \/ Dom σ (fundef_name d)) ->
    forall kept' σ', merge_list funs l kept bs keptm σ = (kept', σ') ->
    sublist kept' L /\ merged_ok L kept' σ' /\
    (forall d, List.In d L -> List.In d kept' \/ Dom σ' (fundef_name d)).
  Proof.
    revert kept bs keptm σ.
    induction l as [| d l IHl ]; intros kept bs keptm σ Hnd Hl Hbs Hkm Hok Hsub Hcov kept' σ' Hm.
    - simpl in Hm. inv Hm. rewrite app_nil_r in Hsub. split; [ eassumption | split ].
      + intros f g Hg. edestruct Hok as [Hn [d [r [H1 [H2 [H3 [H4 H5]]]]]]]; eauto.
        split. rewrite map_rev, <- in_rev. eassumption.
        do 2 eexists. repeat (split; eauto). rewrite <- in_rev. eassumption.
      + intros d Hd. destruct (Hcov d Hd) as [Hc | [Hc | Hc]]; [ contradiction | | eauto ].
        left. rewrite <- in_rev. eassumption.
    - assert (HdL : List.In d L) by (eapply sublist_In; [ eassumption | eapply in_or_app; right; now left ]).
      destruct (Hl d (or_introl eq_refl)) as [Hdσ Hdk].
      inv Hnd.
      assert (Hl' : forall d', List.In d' l -> fundef_name d' <> fundef_name d).
      { intros d' Hin Heq. eapply H1. rewrite <- Heq. eapply in_map. eassumption. }
      destruct d as [[[f t] xs] e]. simpl in Hm, Hdσ, Hdk, Hl'.
      (* Dropping [d] in favour of a kept [r] named [g]. *)
      assert (Hdrop : forall g r, List.In r kept -> fundef_name r = g -> fundef_eqb (f, t, xs, e) r = true ->
                                  merge_list funs l kept bs keptm (M.set f g σ) = (kept', σ') ->
                                  sublist kept' L /\ merged_ok L kept' σ' /\
                                  (forall d, List.In d L -> List.In d kept' \/ Dom σ' (fundef_name d))).
      { intros g r Hr Hrn Hreq Hm'. eapply IHl; [ eassumption | | eassumption | eassumption | | | | eassumption ].
        - intros d' Hin. destruct (Hl d' (or_intror Hin)) as [Hn1 Hn2]. split; eauto.
          rewrite M.gso; eauto.
        - intros f' g' Hg'. destruct (Pos.eq_dec f' f); subst.
          + rewrite M.gss in Hg'. inv Hg'. split; eauto.
            exists (f, t, xs, e), r. repeat (split; eauto).
          + rewrite M.gso in Hg'; eauto.
        - eapply sublist_trans; [ eapply sublist_app_drop | eassumption ].
        - intros d' Hd'. destruct (Hcov d' Hd') as [[Hc | Hc] | [Hc | [y Hy]]]; subst; eauto.
          + right. right. eexists. simpl. rewrite M.gss. reflexivity.
          + right. right. destruct (Pos.eq_dec (fundef_name d') f) as [Heq | Hneq].
            * rewrite Heq. eexists. rewrite M.gss. reflexivity.
            * eexists. rewrite M.gso; eauto. }
      match type of Hm with
      | context [ find_callee ?a ?b ?c ] => destruct (find_callee a b c) as [g |] eqn:Hfc
      end.
      { edestruct find_callee_spec as [r [Hg Hreq]]; eauto.
        edestruct Hkm as [Hr Hrn]; eauto; try (eapply Hdrop; eauto). }
      match type of Hm with
      | context [ find_dup ?a ?b ] => destruct (find_dup a b) as [g |] eqn:Hfd
      end.
      { edestruct find_dup_spec as [r [Hr [Hrn Hreq]]]; eauto. }
      (* Keeping [d]. *)
      eapply IHl; [ eassumption | | | | | | | eassumption ].
      + intros d' Hin. destruct (Hl d' (or_intror Hin)) as [Hn1 Hn2]. split; eauto.
        simpl. intros [Hc | Hc]; eauto. eapply Hl'; eauto.
      + intros t' n' d' Hin. eapply get_bucket_add in Hin. destruct Hin; subst; [ now left | right; eauto ].
      + intros g r Hg. destruct (Pos.eq_dec g f); subst.
        * rewrite M.gss in Hg. inv Hg. split; [ now left | reflexivity ].
        * rewrite M.gso in Hg; eauto. edestruct Hkm; eauto. split; [ right |]; eauto.
      + intros f' g Hg. edestruct Hok as [Hn [d [r [Hd1 [Hd2 [Hd3 [Hd4 Hd5]]]]]]]; eauto. split.
        * simpl. intros [Hc | Hc]; eauto. subst. congruence.
        * exists d, r. repeat (split; eauto). now right.
      + simpl. rewrite <- app_assoc. eassumption.
      + intros d' Hd'. destruct (Hcov d' Hd') as [[Hc | Hc] | [Hc | Hc]]; subst; eauto.
        * right. left. now left.
        * right. left. now right.
  Qed.

  (** * One round of the pass *)

  Lemma bind_vars_get σ0 xs ys x y :
    length xs = length ys -> M.get x (bind_vars σ0 xs ys) = Some y ->
    (exists i, nth_error xs i = Some x /\ nth_error ys i = Some y) \/
    (~ List.In x xs /\ M.get x σ0 = Some y).
  Proof.
    revert σ0 ys. induction xs as [| a xs IHxs ]; intros σ0 ys Hlen Hg;
      destruct ys as [| b ys ]; simpl in *; try discriminate.
    - right. split; eauto.
    - inv Hlen. edestruct IHxs as [[i [H1 H2]] | [Hn Hg']]; eauto.
      + left. exists (S i). simpl. eauto.
      + destruct (Pos.eq_dec x a); subst.
        * rewrite M.gss in Hg'. inv Hg'. left. exists 0. simpl. eauto.
        * rewrite M.gso in Hg'; eauto. right. split; eauto. intros [Hc | Hc]; eauto.
  Qed.

  Lemma bind_vars_not_None σ0 xs ys x :
    M.get x σ0 <> None -> M.get x (bind_vars σ0 xs ys) <> None.
  Proof.
    revert σ0 ys. induction xs as [| a xs IHxs ]; intros σ0 ys Hg; destruct ys as [| b ys ]; simpl; eauto.
    eapply IHxs. destruct (Pos.eq_dec x a); subst.
    - rewrite M.gss. congruence.
    - rewrite M.gso; eauto.
  Qed.

  Lemma bind_vars_None σ0 xs ys x :
    length xs = length ys -> M.get x (bind_vars σ0 xs ys) = None -> ~ List.In x xs.
  Proof.
    revert σ0 ys. induction xs as [| a xs IHxs ]; intros σ0 ys Hlen Hg;
      destruct ys as [| b ys ]; simpl in *; try discriminate; eauto.
    inv Hlen. intros [Hc | Hc]; subst.
    - eapply bind_vars_not_None; [| eassumption ]. rewrite M.gss. congruence.
    - eapply IHxs; eauto.
  Qed.

  Lemma set_lists_nth {A} xs (vs : list A) rho rho' i x :
    NoDup xs -> set_lists xs vs rho = Some rho' -> nth_error xs i = Some x ->
    exists v, nth_error vs i = Some v /\ M.get x rho' = Some v.
  Proof.
    revert vs rho' i. induction xs as [| a xs IHxs ]; intros vs rho' i Hnd Hs Hi;
      [ destruct i; discriminate | ].
    destruct vs as [| v vs ]; simpl in Hs; [ discriminate | ].
    destruct (set_lists xs vs rho) eqn:Hs'; [| discriminate ]. inv Hs. inv Hnd.
    destruct i as [| i ]; simpl in Hi.
    - inv Hi. eexists. split; [ reflexivity | ]. rewrite M.gss. reflexivity.
    - edestruct IHxs as [v' [Hv' Hg]]; eauto. eexists. split; [ eassumption | ].
      rewrite M.gso; eauto. intros Hc; subst. eapply H1. eapply nth_error_In. eassumption.
  Qed.

  Lemma Forall2_nth {A B} (P : A -> B -> Prop) l1 l2 i a b :
    Forall2 P l1 l2 -> nth_error l1 i = Some a -> nth_error l2 i = Some b -> P a b.
  Proof.
    intros H. revert i. induction H; intros [| i] H1 H2; simpl in *; try discriminate.
    - inv H1; inv H2; eauto.
    - eauto.
  Qed.

  Section Merge.

    Context (fds K : fundefs) (k0 : exp) (σ : M.t var).

    Context (Hun : unique_bindings (Efun fds k0))
            (Hdis : Disjoint _ (bound_var (Efun fds k0)) (occurs_free (Efun fds k0)))
            (HDom : Dom σ \subset name_in_fundefs fds)
            (HKsub : forall g t xs e, find_def g K = Some (t, xs, e) -> find_def g fds = Some (t, xs, e))
            (Hkept : forall f t xs e, find_def f fds = Some (t, xs, e) -> M.get f σ = None ->
                                      find_def f K = Some (t, xs, e))
            (Hdrop : forall f g t xs1 e1, find_def f fds = Some (t, xs1, e1) -> M.get f σ = Some g ->
                       exists xs2 e2, find_def g K = Some (t, xs2, e2) /\ M.get g σ = None /\
                                      fundef_eqb (f, t, xs1, e1) (g, t, xs2, e2) = true).

    Lemma DR_names : DR σ \subset name_in_fundefs fds.
    Proof.
      intros x [x' Hx | x' [y Hy]].
      - eapply HDom. eassumption.
      - assert (Hn : name_in_fundefs fds y) by (eapply HDom; eexists; eassumption).
        edestruct name_in_fundefs_find_def_is_Some as [t [xs [e Hfd]]]; [ exact Hn | ].
        edestruct Hdrop as [xs2 [e2 [HfK _]]]; eauto.
        eapply find_def_name_in_fundefs. eapply HKsub. eassumption.
    Qed.

    Lemma merge_preord k rho1 rho2 :
      preord_env_P cenv PG (occurs_free (Efun fds k0)) k rho1 rho2 ->
      preord_exp cenv PG PG k (Efun fds k0, rho1) (Efun (rename_fds σ K) (rename_exp σ k0), rho2).
    Proof.
      intros Henv.
      assert (Hprops := PG_props).
      assert (Hunf : unique_bindings_fundefs fds) by (inv Hun; eauto).
      assert (Hdk : Disjoint _ (bound_var k0) (bound_var_fundefs fds)) by (inv Hun; eauto).
      assert (HS : forall x, occurs_free (Efun fds k0) x ->
                             ~ DR σ x /\ ~ name_in_fundefs fds x /\ ~ bound_var (Efun fds k0) x).
      { intros x Hx. assert (Hn : ~ name_in_fundefs fds x).
        { intros Hn. inv Hx; eauto.
          eapply disj_contra; [ eapply occurs_free_fundefs_name_in_fundefs_Disjoint | eassumption | eassumption ]. }
        split; [ intros Hc; eapply Hn; eapply DR_names; eassumption | split; [ eassumption | ] ].
        intros Hc. eapply disj_contra; [ exact Hdis | eassumption | eassumption ]. }
      inv Hprops.
      eapply preord_exp_fun_compat; eauto.
      eapply rename_preord_exp.
      { intros y Hy Hc. eapply DR_names in Hc.
        eapply disj_contra; [ exact Hdk | eassumption | eapply name_in_fundefs_bound_var_fundefs; eassumption ]. }
      eapply preord_env_P_inj_antimon; [| now eapply occurs_free_Efun_Included ].
      eapply def_funs_inj with (S := occurs_free (Efun fds k0)).
      - intros f t xs1 e1 Hfd. destruct (M.get f σ) as [g |] eqn:Hf.
        + edestruct Hdrop as [xs2 [e2 [HfK [Hg Heqb]]]]; eauto.
          unfold fundef_eqb in Heqb. simpl in Heqb. split_checks.
          exists xs2, (rename_exp σ e2). unfold rn. rewrite Hf. rewrite find_def_rename, HfK. split; eauto.
        + exists xs1, (rename_exp σ e1). unfold rn. rewrite Hf. rewrite find_def_rename, (Hkept _ _ _ _ Hfd Hf). eauto.
      - intros m Hlt f t xs1 e1 xs2 e2' vs1 vs2 rho1' rho2' Hfd1 Hfd2 Hall Hs1 Hs2 Henv'.
        assert (Hfun1 := find_def_correct _ _ _ _ _ Hfd1).
        destruct (ub_fun _ _ _ _ _ Hunf Hfun1) as [Hnd1 Hbv1].
        assert (Hfv1 := occurs_free_in_fun _ _ _ _ _ Hfun1).
        destruct (M.get f σ) as [g |] eqn:Hf.
        + (* [f] is merged into [g] *)
          edestruct Hdrop as [xs2' [e2 [HfK [Hg Heqb]]]]; eauto.
          unfold rn in Hfd2. rewrite Hf in Hfd2. rewrite find_def_rename, HfK in Hfd2. inv Hfd2.
          assert (Hfun2 : fun_in_fundefs fds (g, t, xs2, e2))
            by (eapply find_def_correct; eapply HKsub; eassumption).
          destruct (ub_fun _ _ _ _ _ Hunf Hfun2) as [Hnd2 Hbv2].
          unfold fundef_eqb in Heqb. simpl in Heqb. split_checks.
          match goal with H : length xs1 = length xs2 |- _ => rename H into Hlen end.
          assert (Hsw : forall x, rn σ (if Pos.eqb x f then g else x) = rn σ x).
          { intros x. destruct (Pos.eqb_spec x f); subst; [| reflexivity ].
            unfold rn. rewrite Hf, Hg. reflexivity. }
          eapply alpha_preord_exp with (f1 := f) (f2 := g); [ eassumption | | | ].
          * intros y Hy Hc. eapply Hbv2; [ right; eassumption | eapply DR_names; eassumption ].
          * intros x y Hxy.
            destruct (bind_vars_get _ _ _ _ _ Hlen Hxy) as [[i [Hi1 Hi2]] | [_ Hc]];
              [| rewrite M.gempty in Hc; discriminate ].
            intros Hc. eapply Hbv2; [ left; eapply nth_error_In; eassumption | eapply DR_names; eassumption ].
          * intros x y Hx Hxy. unfold var_eqb in Hxy.
            destruct (M.get x (bind_vars (M.empty _) xs1 xs2)) as [y' |] eqn:Hx1;
              destruct (M.get y (bind_vars (M.empty _) xs2 xs1)) as [x' |] eqn:Hy1;
              simpl in Hxy; try discriminate.
            -- (* parameters *)
               split_checks.
               destruct (bind_vars_get _ _ _ _ _ Hlen Hx1) as [[i [Hi1 Hi2]] | [_ Hc]];
                 [| rewrite M.gempty in Hc; discriminate ].
               edestruct (set_lists_nth xs1 vs1) as [v1 [Hv1 Hg1]]; eauto.
               edestruct (set_lists_nth xs2 vs2) as [v2 [Hv2 Hg2]]; eauto.
               rewrite rn_not_DR.
               ++ intros v Hget. rewrite Hg1 in Hget. inv Hget.
                  eexists. split. eassumption. eapply Forall2_nth; eauto.
               ++ intros Hc. eapply Hbv2; [ left; eapply nth_error_In; eassumption | eapply DR_names; eassumption ].
            -- (* free variables *)
               split_checks.
               assert (Hnx : ~ List.In x xs1) by (eapply bind_vars_None; eauto).
               assert (Hny : ~ List.In (if Pos.eqb x f then g else x) xs2)
                 by (eapply bind_vars_None; [ symmetry; eassumption | eassumption ]).
               rewrite Hsw.
               assert (Hx' : (occurs_free (Efun fds k0) :|: name_in_fundefs fds) x).
               { edestruct (Hfv1 x Hx) as [? Hc | ? [? Hc | ? Hc]];
                   [ contradiction | now right | left; now eapply Free_Efun2 ]. }
               assert (Hrx : ~ List.In (rn σ x) xs2).
               { intros Hc. destruct Hx' as [? Hx' | ? Hx'].
                 - destruct (HS x Hx') as [HDR [_ Hbv]]. rewrite rn_not_DR in Hc; eauto.
                   eapply Hbv. eapply Bound_Efun1. eapply fun_in_fundefs_bound_var_fundefs. eassumption.
                   right. now left.
                 - eapply Hbv2; [ left; eassumption | ].
                   destruct (rn_cases σ x) as [[Heq _] | [_ Hr]].
                   + rewrite Heq. eassumption.
                   + eapply DR_names. now right. }
               intros v Hget. rewrite <- (set_lists_not_In _ _ _ _ _ Hs1 Hnx) in Hget.
               edestruct Henv' as [v' [Hget' Hv']]; [ eassumption | eassumption | ].
               eexists. split; [| eassumption ].
               rewrite <- (set_lists_not_In _ _ _ _ _ Hs2 Hrx). eassumption.
        + (* [f] is kept *)
          unfold rn in Hfd2. rewrite Hf in Hfd2. rewrite find_def_rename, (Hkept _ _ _ _ Hfd1 Hf) in Hfd2. inv Hfd2.
          eapply rename_preord_exp.
          * intros y Hy Hc. eapply Hbv1; [ right; eassumption | eapply DR_names; eassumption ].
          * eapply inj_set_lists; [| eassumption | | eassumption | eassumption ].
            -- eapply preord_env_P_inj_antimon. eassumption.
               intros x [Hx Hnx]. edestruct (Hfv1 x Hx) as [? Hc | ? [? Hc | ? Hc]];
                 [ contradiction | now right | left; now eapply Free_Efun2 ].
            -- intros x Hx Hc. eapply Hbv1; [ left; eassumption | eapply DR_names; eassumption ].
      - intros x Hx Hnx Hc. apply (proj1 (name_in_fundefs_rename σ K)) in Hc.
        rewrite rn_not_DR in Hc; [| eapply HS; eassumption ].
        eapply Hnx.
        edestruct name_in_fundefs_find_def_is_Some as [? [? [? HfK]]]; [ exact Hc |].
        eapply find_def_name_in_fundefs. eapply HKsub. eassumption.
      - intros x Hx. rewrite rn_not_DR; [| eapply HS; eassumption ].
        eapply preord_var_env_monotonic. eapply Henv. eassumption. lia.
    Qed.

  End Merge.

  Lemma NoDup_map_sublist {A B} (h : A -> B) l1 l2 :
    sublist l1 l2 -> NoDup (map h l2) -> NoDup (map h l1).
  Proof.
    induction 1 as [| a l1 l2 Hs IHs | a l1 l2 Hs IHs ]; simpl; intros Hnd.
    - constructor.
    - inv Hnd. constructor; eauto. intros Hc. eapply in_map_iff in Hc. destruct Hc as [x [Heq Hin]].
      match goal with H : ~ List.In _ _ |- _ => eapply H end.
      rewrite <- Heq. eapply in_map. eapply sublist_In; eassumption.
    - inv Hnd. eauto.
  Qed.

  (** One round: [Efun fds k0] becomes [Efun (rename_fds σ K) (rename_exp σ k0)]. *)
  Lemma merge_step fds k0 funs kept σ :
    unique_bindings (Efun fds k0) ->
    Disjoint _ (bound_var (Efun fds k0)) (occurs_free (Efun fds k0)) ->
    merge_list funs (fds_to_list fds) [] (M.empty _) (M.empty _) (M.empty _) = (kept, σ) ->
    unique_bindings (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k0)) /\
    Disjoint _ (bound_var (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k0)))
               (occurs_free (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k0))) /\
    occurs_free (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k0)) \subset occurs_free (Efun fds k0) /\
    bound_var (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k0)) \subset bound_var (Efun fds k0) /\
    (forall k rho1 rho2,
        preord_env_P cenv PG (occurs_free (Efun fds k0)) k rho1 rho2 ->
        preord_exp cenv PG PG k (Efun fds k0, rho1)
                   (Efun (rename_fds σ (list_to_fds kept)) (rename_exp σ k0), rho2)).
  Proof.
    intros Hun Hdis Hm.
    assert (Hunk : unique_bindings k0) by (inv Hun; eauto).
    assert (Hunf : unique_bindings_fundefs fds) by (inv Hun; eauto).
    assert (Hdk : Disjoint _ (bound_var k0) (bound_var_fundefs fds)) by (inv Hun; eauto).
    assert (HL : list_to_fds (fds_to_list fds) = fds) by eapply list_to_fds_fds_to_list.
    remember (fds_to_list fds) as L eqn:HeqL.
    assert (HndL : NoDup (map fundef_name L)) by (subst; eapply ub_NoDup; eassumption).
    assert (Hspec : sublist kept L /\ merged_ok L kept σ /\
                    (forall d, List.In d L -> List.In d kept \/ Dom σ (fundef_name d))).
    { eapply merge_list_spec; [ eassumption | | | | | | | exact Hm ].
      - intros d _. rewrite M.gempty. split; eauto.
      - intros t n d Hin. unfold get_bucket in Hin. rewrite M.gempty in Hin. inv Hin.
      - intros g r Hg. rewrite M.gempty in Hg. discriminate.
      - intros f g Hg. rewrite M.gempty in Hg. discriminate.
      - simpl. eapply sublist_refl.
      - intros d Hd. now left. }
    destruct Hspec as [Hsub [Hok Hcov]].
    assert (HndK : NoDup (map fundef_name kept)) by (eapply NoDup_map_sublist; eassumption).
    destruct (sublist_fds _ _ Hsub) as [HubK HbvK]. rewrite HL in HubK, HbvK.
    set (K := list_to_fds kept) in *.
    assert (HinL : forall f t xs e, find_def f fds = Some (t, xs, e) -> List.In (f, t, xs, e) L)
      by (intros; subst; eapply find_def_In; eassumption).
    assert (HKsub : forall g t xs e, find_def g K = Some (t, xs, e) -> find_def g fds = Some (t, xs, e)).
    { intros g t xs e Hfd. rewrite <- HL. eapply find_def_list_to_fds; [ eassumption | ].
      eapply sublist_In; [ eassumption | ]. eapply fun_in_list_to_fds. eapply find_def_correct. eassumption. }
    assert (HDom : Dom σ \subset name_in_fundefs fds).
    { intros f [g Hg]. edestruct Hok as [_ [d [r [Hd [Hdn _]]]]]; [ eassumption | ].
      subst f. rewrite <- HL. eapply name_in_list_to_fds. eapply in_map. eassumption. }
    assert (Hkept : forall f t xs e, find_def f fds = Some (t, xs, e) -> M.get f σ = None ->
                                     find_def f K = Some (t, xs, e)).
    { intros f t xs e Hfd Hf. destruct (Hcov _ (HinL _ _ _ _ Hfd)) as [Hin | [g Hg]].
      - eapply find_def_list_to_fds; eassumption.
      - simpl in Hg. congruence. }
    assert (Hdrop : forall f g t xs1 e1, find_def f fds = Some (t, xs1, e1) -> M.get f σ = Some g ->
                      exists xs2 e2, find_def g K = Some (t, xs2, e2) /\ M.get g σ = None /\
                                     fundef_eqb (f, t, xs1, e1) (g, t, xs2, e2) = true).
    { intros f g t xs1 e1 Hfd Hf.
      edestruct Hok as [Hnk [d [[[[g' t2] xs2] e2] [Hd [Hdn [Hr [Hrn Heqb]]]]]]]; [ eassumption | ].
      simpl in Hrn. subst g'.
      assert (Hdeq : d = (f, t, xs1, e1)) by (eapply NoDup_names_eq; [ exact HndL | exact Hd | eapply HinL; exact Hfd | exact Hdn ]).
      subst d.
      assert (Ht : t = t2).
      { unfold fundef_eqb in Heqb. simpl in Heqb. apply lazy_and in Heqb. destruct Heqb as [Heqb _].
        apply lazy_and in Heqb. destruct Heqb as [Heqb _]. apply Pos.eqb_eq. eassumption. }
      subst t2. exists xs2, e2. split; [ eapply find_def_list_to_fds; eassumption | split; [| eassumption ] ].
      destruct (M.get g σ) as [h |] eqn:Hg; [| reflexivity ].
      exfalso. edestruct Hok as [Hgk _]; [ exact Hg | ]. eapply Hgk.
      eapply in_map_iff. eexists; split; [| eassumption ]. reflexivity. }
    assert (Hcov' : forall x, name_in_fundefs fds x -> Dom σ x \/ name_in_fundefs K x).
    { intros x Hx. rewrite <- HL in Hx. eapply name_in_list_to_fds in Hx.
      eapply in_map_iff in Hx. destruct Hx as [d [Hdn Hd]]. subst x.
      destruct (Hcov d Hd) as [Hin | Hdom]; [ right | now left ].
      eapply name_in_list_to_fds. eapply in_map. eassumption. }
    assert (HRan : Ran σ \subset name_in_fundefs K).
    { intros y [x Hx]. assert (Hn : name_in_fundefs fds x) by (eapply HDom; eexists; eassumption).
      edestruct name_in_fundefs_find_def_is_Some as [t [xs [e Hfd]]]; [ exact Hn | ].
      edestruct Hdrop as [xs2 [e2 [HfK _]]]; eauto. eapply find_def_name_in_fundefs. eassumption. }
    assert (HKfds : forall d, fun_in_fundefs K d -> fun_in_fundefs fds d).
    { intros d Hd. rewrite <- HL. eapply fun_in_list_to_fds. eapply sublist_In; [ eassumption | ].
      eapply fun_in_list_to_fds. eassumption. }
    destruct (proj1 (rename_syntactic σ) k0) as [Hbvk Hubk].
    destruct (proj2 (rename_syntactic σ) K) as [HbvK' HubK'].
    assert (Hbv : bound_var (Efun (rename_fds σ K) (rename_exp σ k0)) \subset bound_var (Efun fds k0)).
    { repeat normalize_bound_var. eapply Union_Included.
      - eapply Included_trans; [ eassumption | ]. eapply Included_trans; [ eassumption | ]. sets.
      - eapply Included_trans; [ eassumption | ]. sets. }
    assert (Hfv : occurs_free (Efun (rename_fds σ K) (rename_exp σ k0)) \subset occurs_free (Efun fds k0)).
    { intros z Hz. inv Hz.
      - match goal with H : ~ name_in_fundefs _ _ |- _ => rename H into Hnz end.
        match goal with H : occurs_free (rename_exp _ _) _ |- _ => rename H into Hz end.
        destruct (proj1 (rename_occurs_free σ) k0 z Hz) as [[Hz' Hd] | Hr].
        + eapply Free_Efun1; [| eassumption ]. intros Hc.
          destruct (Hcov' z Hc) as [Hc' | Hc']; eauto. eapply Hnz. eapply name_in_fundefs_rename. eassumption.
        + exfalso. eapply Hnz. eapply name_in_fundefs_rename. eapply HRan. eassumption.
      - match goal with H : occurs_free_fundefs _ _ |- _ => rename H into Hz end.
        assert (HnK : ~ name_in_fundefs K z).
        { intros Hc. eapply disj_contra; [ eapply occurs_free_fundefs_name_in_fundefs_Disjoint | | eassumption ].
          eapply name_in_fundefs_rename. eassumption. }
        destruct (proj2 (rename_occurs_free σ) K z Hz) as [[Hz' Hd] | Hr].
        + eapply Free_Efun2. eapply occurs_free_fundefs_sub; [ eassumption | eassumption | ].
          intros Hc. destruct (Hcov' z Hc); eauto.
        + exfalso. eapply HnK. eapply HRan. eassumption. }
    split; [| split; [| split; [| split ] ] ].
    - constructor; eauto.
      eapply Disjoint_Included; [ eassumption | eassumption | ].
      eapply Disjoint_Included_r; [ eassumption | eassumption ].
    - eapply Disjoint_Included; [ eassumption | eassumption | eassumption ].
    - eassumption.
    - eassumption.
    - intros. eapply merge_preord; eauto.
  Qed.

End MergeDupFunsCorrect.
