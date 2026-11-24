(** * MetaRocq's weak call-by-value evaluation and the environment semantics [fuel_sem]

    [wcbv_to_eval_env_fuel]: if a closed λ□ term [e], well formed for
    environment flags without boxes, cofixpoints, lazy/force, primitive arrays
    and constructor parameters, evaluates in MetaRocq's substitution semantics
    [EWcbvEval.eval] (flags [Erasure.final_wcbv_flags]: no case on proofs,
    unguarded fixpoints, constructors as blocks) to [v], then [e] evaluates in
    CertiRocq's environment semantics [fuel_sem.eval_env_fuel] to a value that
    represents [v] ([repr]), for some fuel and trace.

    The simulation is stated for open terms: [e] under an environment [rho]
    whose values represent the closed terms [ts] evaluates as [subst ts 0 e]. *)

From Stdlib Require Import Arith List Lia ssreflect ssrbool.
From Equations Require Import Equations.
From MetaRocq.Utils Require Import utils All_Forall.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EPrimitive EAst EAstUtils EInduction ELiftSubst ECSubst
  EGlobalEnv EWellformed EWcbvEval.
From MetaRocq.ErasurePlugin Require Erasure.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.LambdaANF Require Import algebra.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common fuel_sem.

Import ListNotations.
Open Scope list_scope.

(** The flags of MetaRocq's evaluation for the programs CertiRocq receives
    ([LLVM_endtoend.certirocq_wcbv_flags] is the same constant). *)
Local Notation wfl := Erasure.final_wcbv_flags.

Section Repr.

  Context {efl : EEnvFlags} (Σ : global_declarations).

  (** [repr v t]: the [fuel_sem] value [v] denotes the closed term [t].  A
      closure denotes its body with the environment substituted. *)
  Inductive repr : value -> term -> Prop :=
  | repr_con ind c vs ts :
      Forall2 repr vs ts -> forallb (closedn 0) ts ->
      repr (Con_v (dcon_of_con ind c) vs) (tConstruct ind c ts)
  | repr_clos rho ts na b :
      Forall2 repr rho ts -> forallb (closedn 0) ts ->
      wellformed Σ (S #|rho|) b ->
      repr (Clos_v rho na b) (tLambda na (subst ts 1 b))
  | repr_fix rho ts mfix idx :
      Forall2 repr rho ts -> forallb (closedn 0) ts ->
      forallb (isLambda ∘ dbody) mfix ->
      forallb (test_def (wellformed Σ (#|mfix| + #|rho|))) mfix ->
      repr (ClosFix_v rho mfix idx) (tFix (map (map_def (subst ts #|mfix|)) mfix) idx)
  | repr_prim p pv :
      trans_prim_val p = Some pv ->
      repr (Prim_v pv) (tPrim p).

End Repr.

Section Lemmas.

  Context {efl : EEnvFlags} (Σ : global_declarations).

  Lemma trans_prim_val_closed k p pv :
    trans_prim_val p = Some pv -> closedn k (tPrim p).
  Proof.
    destruct p as [t m]; destruct m; cbn; try discriminate; reflexivity.
  Qed.

  Lemma trans_prim_val_subst s k p pv :
    trans_prim_val p = Some pv -> subst s k (tPrim p) = tPrim p.
  Proof.
    destruct p as [t m]; destruct m; cbn; try discriminate; reflexivity.
  Qed.

  Lemma repr_closed v t : repr Σ v t -> closedn 0 t.
  Proof.
    intros H; destruct H as [ind c vs ts _ Hc|rho ts na b Hr Hc Hwf|rho ts mfix idx Hr Hc _ Hwf|p pv Hp].
    - exact Hc.
    - apply Forall2_length in Hr. cbn.
      change 1 with (0 + 1). rewrite -(closedn_subst_eq ts 0 1 b Hc).
      apply wellformed_closed in Hwf. cbn. rewrite -Hr. exact Hwf.
    - apply Forall2_length in Hr. cbn.
      rewrite forallb_map. eapply forallb_impl; [|exact Hwf].
      intros d _ Hd. unfold test_def in *. cbn.
      rewrite length_map Nat.add_0_r.
      change #|mfix| with (0 + #|mfix|). rewrite -(closedn_subst_eq ts 0 #|mfix| (dbody d) Hc).
      apply wellformed_closed in Hd. rewrite -Hr. cbn. exact Hd.
    - exact (trans_prim_val_closed 0 p pv Hp).
  Qed.

  Lemma repr_all_closed rho ts : Forall2 (repr Σ) rho ts -> forallb (closedn 0) ts.
  Proof.
    induction 1; cbn; [reflexivity|]. rewrite (repr_closed _ _ H) IHForall2. reflexivity.
  Qed.

  Lemma subst_rel_nth ts n t :
    nth_error ts n = Some t -> subst ts 0 (tRel n) = t.
  Proof.
    intros H. cbn. rewrite Nat.sub_0_r H. apply lift0_p.
  Qed.

  Lemma csubst_subst_cons a ts b :
    closedn 0 a ->
    csubst a 0 (subst ts 1 b) = subst (a :: ts) 0 b.
  Proof.
    intros Ha. rewrite closed_subst; [exact Ha|].
    change (a :: ts) with (app [a] ts). rewrite subst_app_simpl. reflexivity.
  Qed.

  Lemma substl_subst_app l ts b :
    forallb (closedn 0) l ->
    substl l (subst ts #|l| b) = subst (app l ts) 0 b.
  Proof.
    intros Hl. rewrite substl_subst; [exact Hl|].
    rewrite subst_app_simpl. reflexivity.
  Qed.

End Lemmas.

Section Values.

  Context {efl : EEnvFlags} (Σ : global_declarations).

  (** A term that a value represents evaluates only to itself. *)
  Lemma repr_eval_self t : forall v t', repr Σ v t -> @eval wfl Σ t t' -> t' = t.
  Proof.
    induction t using term_forall_list_ind; intros v t' Hr Hev; inversion Hr; subst.
    - depelim Hev; try discriminate. reflexivity.
    - depelim Hev; try discriminate.
      + f_equal. clear -X H2 a.
        revert vs X H2. induction a; intros vs X Hvs; [reflexivity|].
        depelim X. rename e into Hx. inversion Hvs as [|v0 vs0 ? ? Hv Hvs']; subst.
        rewrite (Hx _ _ Hv r) (IHa _ X Hvs'). reflexivity.
      + exfalso; destruct args; vm_compute in i; discriminate.
    - depelim Hev; try discriminate. reflexivity.
    - destruct p as [tg m]; destruct m; cbn in H1; try discriminate;
        depelim Hev; try reflexivity; inversion e; reflexivity.
  Qed.

End Values.

Section Aux.

  Context {efl : EEnvFlags} (Σ : global_declarations).

  Lemma mkApps_shape f l :
    (exists x y, mkApps f l = tApp x y) \/ mkApps f l = f.
  Proof.
    induction l as [|a l IH] in f |- *; cbn; [right; reflexivity|].
    destruct (IH (tApp f a)) as [H|H]; left; [exact H|]. rewrite H. eauto.
  Qed.

  Lemma repr_not_mkApps_cofix v mfix idx args : repr Σ v (mkApps (tCoFix mfix idx) args) -> False.
  Proof.
    destruct (mkApps_shape (tCoFix mfix idx) args) as [(x & y & ->)| ->]; intros H; inversion H.
  Qed.

  Lemma find_branch_nth ind brs c names body :
    nth_error brs c = Some (names, body) ->
    find_branch ind c #|names| brs = Some body.
  Proof.
    induction brs as [|[nms b] brs IH] in c |- *; [destruct c; discriminate|].
    destruct c as [|c]; cbn.
    - intros [= -> ->]. destruct (Nat.eqb_spec #|names| #|names|); [reflexivity|congruence].
    - intros H. rewrite Nat.sub_0_r. exact (IH c H).
  Qed.

  Lemma pars_zero (Hwfg : wf_glob Σ) (Hnopars : has_cstr_params = false) ind c b pars cdecl :
    constructor_isprop_pars_decl Σ ind c = Some (b, pars, cdecl) -> pars = 0.
  Proof.
    unfold constructor_isprop_pars_decl, lookup_constructor, lookup_inductive, lookup_minductive.
    destruct (lookup_env Σ (inductive_mind ind)) as [[|mdecl]|] eqn:E; cbn; try discriminate.
    destruct nth_error; cbn; try discriminate.
    destruct nth_error; cbn; try discriminate.
    intros [= _ <- _].
    pose proof (lookup_env_wellformed Hwfg E) as Hw. cbn in Hw.
    unfold wf_minductive in Hw. rewrite Hnopars in Hw. cbn in Hw.
    move/andP: Hw => [Hw _]. now apply/Nat.eqb_spec.
  Qed.

  Lemma glob_body_wf (Hwfg : wf_glob Σ) k decl body :
    declared_constant Σ k decl -> cst_body decl = Some body -> wellformed Σ 0 body.
  Proof.
    unfold declared_constant. intros Hd Hb.
    pose proof (lookup_env_wellformed Hwfg Hd) as Hw. cbn in Hw. rewrite Hb in Hw. exact Hw.
  Qed.

  Lemma prim_trans (HnoArr : has_primarray = false) p :
    has_prim p -> exists pv, trans_prim_val p = Some pv.
  Proof.
    destruct p as [tg m]; destruct m; cbn; eauto.
    rewrite HnoArr. discriminate.
  Qed.

  Lemma make_rec_env_repr rho ts mfix :
    Forall2 (repr Σ) rho ts -> forallb (closedn 0) ts ->
    forallb (isLambda ∘ dbody) mfix ->
    forallb (test_def (wellformed Σ (#|mfix| + #|rho|))) mfix ->
    Forall2 (repr Σ) (make_rec_env mfix rho)
      (fix_subst (map (map_def (subst ts #|mfix|)) mfix) ++ ts).
  Proof.
    intros Hr Hc Hl Hw.
    assert (Hall : forall i, repr Σ (ClosFix_v rho mfix i)
                                 (tFix (map (map_def (subst ts #|mfix|)) mfix) i))
      by (intros; constructor; assumption).
    unfold make_rec_env, fix_subst. rewrite length_map.
    set (mfix' := map _ mfix) in *. clearbody mfix'. clear Hw Hl.
    generalize #|mfix| as n. intros n.
    induction n as [|n IH]; cbn; [exact Hr|].
    constructor; [apply Hall|exact IH].
  Qed.

End Aux.

Section Simulation.

  Context {efl : EEnvFlags} (Σ : global_declarations).
  Context {trace : Type} {Hf : @LambdaBox_resource nat} {Ht : @LambdaBox_resource trace}.

  Hypothesis Hwfg : wf_glob Σ.
  Hypothesis HtRel : has_tRel = true.
  Hypothesis HtApp : has_tApp = true.
  Hypothesis HnoBox : has_tBox = false.
  Hypothesis HnoCoFix : has_tCoFix = false.
  Hypothesis HnoLazy : has_tLazy_Force = false.
  Hypothesis HnoArr : has_primarray = false.
  Hypothesis Hnopars : has_cstr_params = false.

  Local Notation evf := (@eval_env_fuel trace Hf Ht Σ).

  Lemma rel_case rho ts n t :
    Forall2 (repr Σ) rho ts -> wellformed Σ #|rho| (tRel n) -> t = subst ts 0 (tRel n) ->
    exists rv, nth_error rho n = Some rv /\ repr Σ rv t.
  Proof.
    intros Hr Hwf ->. cbn in Hwf. move/andP: Hwf => [_ Hn]. apply Nat.ltb_lt in Hn.
    destruct (nth_error rho n) as [rv|] eqn:E; [|apply nth_error_None in E; lia].
    destruct (Forall2_nth_error_Some_l _ _ _ _ _ _ _ E Hr) as (t' & Ht' & Hrt).
    exists rv. split; [reflexivity|]. rewrite (subst_rel_nth _ _ _ Ht'). exact Hrt.
  Qed.

  Lemma rel_val rho n v f tr : evf rho (tRel n) (Val v) f tr -> nth_error rho n = Some v.
  Proof.
    intros H. inversion H; subst. match goal with H : eval_env_step _ _ _ _ _ _ |- _ => inversion H end.
    congruence.
  Qed.

  Ltac flags_contra := exfalso; match goal with
    | H : @with_constructor_as_block _ = false |- _ => vm_compute in H; discriminate H
    | H : is_true (@with_guarded_fix _) |- _ => vm_compute in H; discriminate H
    | H : is_true (@with_prop_case _) |- _ => vm_compute in H; discriminate H
    end.

  Ltac relc := match goal with
    | Heq : _ = subst0 _ (tRel _), Hr : Forall2 _ _ _, Hwf : is_true (wellformed _ _ _) |- _ =>
        let rv := fresh "rv" in let Hn := fresh "Hn" in let Hrv := fresh "Hrv" in
        destruct (rel_case _ _ _ _ Hr Hwf Heq) as (rv & Hn & Hrv); try solve [inversion Hrv]
    end.

  Ltac atom_solve Hr Hwf := solve [
    match goal with H : ?x = subst0 _ _ |- _ => is_var x; subst x end;
    first
      [ do 3 eexists; split; [eapply eval_step; eapply eval_Rel_fuel; eassumption|eassumption]
      | exfalso; cbn in Hwf; rewrite ?HnoBox ?HnoCoFix ?HnoLazy in Hwf; cbn in Hwf; discriminate Hwf
      | exfalso; match goal with i : is_true (atom _ _) |- _ => cbn in i; discriminate i end
      | (* lambda *)
        cbn in Hwf; move/andP: Hwf => [_ ?];
        do 3 eexists; split; [eapply eval_step; eapply eval_Lam_fuel|];
        cbn; constructor; [eassumption|exact (repr_all_closed _ _ _ Hr)|assumption]
      | (* fixpoint *)
        cbn in Hwf; move/andP: Hwf => [/andP [_ ?] /andP [_ ?]];
        do 3 eexists; split; [eapply eval_step; eapply eval_Fix_fuel|];
        cbn; rewrite Nat.add_0_r; constructor;
        [eassumption|exact (repr_all_closed _ _ _ Hr)|assumption|assumption] ] ].

  Lemma wcbv_sim t v (ev : @eval wfl Σ t v) :
    forall rho ts e, Forall2 (repr Σ) rho ts -> wellformed Σ #|rho| e -> t = subst ts 0 e ->
    exists rv f tr, evf rho e (Val rv) f tr /\ repr Σ rv v.
  Proof.
    induction ev using eval_rect; intros rho ts E Hr Hwf Heq;
      try flags_contra;
      (destruct E; try (cbn in Heq; discriminate Heq);
       try relc);
      try atom_solve Hr Hwf.
    - (* box *)
      cbn in Heq. injection Heq as -> ->. cbn in Hwf. move/andP: Hwf => [/andP [_ Hw1] _].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (? & ? & ? & _ & Hb). inversion Hb.
    - (* beta *)
      cbn in Heq. injection Heq as -> ->. cbn in Hwf. move/andP: Hwf => [/andP [_ Hw1] Hw2].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (rv1 & f1 & t1 & D1 & R1).
      inversion R1 as [| rho' ts' na' b' Hr' Hc' Hwb| |]; subst.
      destruct (IHev2 _ _ _ Hr Hw2 eq_refl) as (rv2 & f2 & t2 & D2 & R2).
      destruct (IHev3 (rv2 :: rho') (a' :: ts') b' (Forall2_cons _ _ R2 Hr') Hwb
                  (csubst_subst_cons _ _ _ (repr_closed _ _ _ R2)))
        as (rv & f3 & t3 & D3 & R3).
      do 3 eexists; split; [eapply eval_step; eapply eval_App_step; eassumption|exact R3].
    - (* zeta *)
      cbn in Heq. injection Heq as -> -> ->. cbn in Hwf. move/andP: Hwf => [/andP [_ Hw1] Hw2].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (rv1 & f1 & t1 & D1 & R1).
      destruct (IHev2 (rv1 :: rho) (b0' :: ts) E2 (Forall2_cons _ _ R1 Hr) Hw2
                  (csubst_subst_cons _ _ _ (repr_closed _ _ _ R1)))
        as (rv & f2 & t2 & D2 & R2).
      do 3 eexists; split; [eapply eval_step; eapply eval_LetIn_step; eassumption|exact R2].
    - (* iota, constructors as blocks *)
      destruct indn as [ind' np]. cbn in Heq. injection Heq as Hi Hp Hd Hb. subst ind' np discr brs.
      cbn in Hwf. move/andP: Hwf => [_ /andP [/andP [_ Hw1] Hw2]].
      pose proof (pars_zero Σ Hwfg Hnopars _ _ _ _ _ e1) as ->.
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (rv1 & f1 & t1 & D1 & R1).
      inversion R1 as [ind1 c1 vs args1 Hvs Hca| | |]; subst.
      rewrite nth_error_map in e2.
      destruct (nth_error brs0 c) as [[nms body]|] eqn:Ebr; cbn in e2; [|discriminate].
      injection e2 as <-. cbn [fst] in e4. rewrite skipn_0 in e4.
      assert (Hlen : #|vs| = #|nms|) by (rewrite (Forall2_length Hvs); exact e4).
      assert (Hwb : wellformed Σ #|List.rev vs ++ rho| body).
      { rewrite length_app List.length_rev Hlen.
        apply nth_error_In in Ebr. exact (proj1 (forallb_forall _ _) Hw2 _ Ebr). }
      assert (Heq2 : iota_red 0 args (nms, subst ts (#|nms| + 0) body) = subst0 (List.rev args ++ ts) body).
      { unfold iota_red. cbn [fst snd]. rewrite skipn_0 Nat.add_0_r -e4 -List.length_rev.
        apply substl_subst_app. rewrite forallb_rev. exact Hca. }
      destruct (IHev2 (List.rev vs ++ rho) (List.rev args ++ ts) body
                  (Forall2_app (Forall2_rev _ _ _ _ _ Hvs) Hr) Hwb Heq2)
        as (rv & f2 & t2 & D2 & R2).
      do 3 eexists; split; [|exact R2].
      eapply eval_step. eapply eval_Case_step; [exact D1|reflexivity| |exact D2].
      rewrite Hlen. apply find_branch_nth. exact Ebr.
    - (* fix, unguarded *)
      cbn in Heq. injection Heq as -> ->. cbn in Hwf. move/andP: Hwf => [/andP [_ Hw1] Hw2].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (rv1 & f1 & t1 & D1 & R1).
      pose proof (repr_closed _ _ _ R1) as Hcl.
      inversion R1 as [| |rho' ts' mfix' idx' Hr' Hc' Hl' Hw'|]; subst.
      destruct (IHev2 _ _ _ Hr Hw2 eq_refl) as (rv2 & f2 & t2 & D2 & R2).
      unfold cunfold_fix in e0. rewrite nth_error_map in e0.
      destruct (nth_error mfix' idx) as [d'|] eqn:Ed; cbn in e0; [|discriminate].
      injection e0 as _ <-.
      pose proof (nth_error_In _ _ Ed) as Hin.
      assert (Hlam := proj1 (forallb_forall _ _) Hl' _ Hin).
      assert (Hwd := proj1 (forallb_forall _ _) Hw' _ Hin). unfold test_def in Hwd.
      cbn in Hlam. revert Hlam Hwd.
      destruct (dbody d') as [| | | |na body'| | | | | | | | | | |] eqn:Eb; intros Hlam Hwd;
        cbn in Hlam; try discriminate.
      cbn in Hwd. move/andP: Hwd => [_ Hwb].
      set (fs := fix_subst (map (map_def (subst ts' #|mfix'|)) mfix')).
      assert (Hfs : forallb (closedn 0) fs).
      { apply closed_fix_subst. exact Hcl. }
      assert (Hlfs : #|fs| = #|mfix'|) by (unfold fs; rewrite fix_subst_length length_map; reflexivity).
      assert (Hfn : substl fs (subst ts' #|mfix'| (tLambda na body'))
                    = tLambda na (subst (fs ++ ts') 1 body')).
      { rewrite substl_subst; [exact Hfs|]. cbn [subst].
        rewrite subst_app_simpl Hlfs. reflexivity. }
      pose proof (make_rec_env_repr Σ rho' ts' mfix' Hr' Hc' Hl' Hw') as Hrec. fold fs in Hrec.
      assert (Hclos : repr Σ (Clos_v (make_rec_env mfix' rho') na body')
                        (tLambda na (subst (fs ++ ts') 1 body'))).
      { constructor; [exact Hrec|exact (repr_all_closed _ _ _ Hrec)|].
        rewrite (Forall2_length Hrec) length_app Hlfs -(Forall2_length Hr'). exact Hwb. }
      destruct (IHev3 [Clos_v (make_rec_env mfix' rho') na body'; rv2]
                  [tLambda na (subst (fs ++ ts') 1 body'); av]
                  (tApp (tRel 0) (tRel 1))
                  (Forall2_cons _ _ Hclos (Forall2_cons _ _ R2 (Forall2_nil _))))
        as (rv & f3 & t3 & D3 & R3).
      { cbn. rewrite HtApp HtRel. reflexivity. }
      { fold fs. rewrite Hfn.
        match goal with |- _ = subst0 [?x; ?y] _ =>
          change (subst0 [x; y] (tApp (tRel 0) (tRel 1))) with (tApp (lift0 0 x) (lift0 0 y)) end.
        rewrite !lift0_p. reflexivity. }
      inversion D3 as [|? ? ? ? ? Dstep]; subst.
      inversion Dstep as [| | |e1' e2' body'' v2' r' na'' rho0 rho'' f1' f2' f3' t1' t2' t3' Da Db Dc
                          | | |e1' e2' body'' rho0 rho1 rho2 idx2 na'' mfix2 v2' r' f1' f2' f3' t1' t2' t3' Da _ _ Db Dc
                          | | | | | | | | | |]; subst.
      + apply rel_val in Da. apply rel_val in Db. cbn in Da, Db.
        injection Da as <- <- <-. injection Db as <-.
        do 3 eexists; split; [|exact R3].
        eapply eval_step. eapply eval_FixApp_step; [exact D1| |reflexivity|exact D2|exact Dc].
        unfold fix_body. rewrite Ed Eb. reflexivity.
      + apply rel_val in Da. discriminate Da.
    - (* cofix case *)
      destruct indn as [ind' np]. cbn in Heq. injection Heq as Hi Hd Hb. subst.
      cbn in Hwf. move/andP: Hwf => [_ /andP [/andP [_ Hw1] _]].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (? & ? & ? & _ & Hb').
      exfalso. exact (repr_not_mkApps_cofix _ _ _ _ _ Hb').
    - (* cofix proj *)
      cbn in Heq. injection Heq as -> ->. cbn in Hwf. move/andP: Hwf => [_ Hw1].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (? & ? & ? & _ & Hb').
      exfalso. exact (repr_not_mkApps_cofix _ _ _ _ _ Hb').
    - (* delta *)
      cbn in Heq. injection Heq as <-.
      destruct (IHev [] [] body (Forall2_nil _) (glob_body_wf Σ Hwfg _ _ _ isdecl e)
                  (eq_sym (subst_empty 0 body)))
        as (rv & f1 & t1 & D1 & R1).
      do 3 eexists; split; [eapply eval_step; eapply eval_Const_step; eassumption|exact R1].
    - (* projection, constructors as blocks *)
      cbn in Heq. injection Heq as -> ->. cbn in Hwf. move/andP: Hwf => [_ Hw1].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (rv1 & f1 & t1 & D1 & R1).
      inversion R1 as [ind1 c1 vs args1 Hvs Hca| | |]; subst.
      pose proof (pars_zero Σ Hwfg Hnopars _ _ _ _ _ e1) as Hp0.
      rewrite Hp0 in e3. cbn in e3.
      destruct (Forall2_nth_error_Some_r _ _ _ _ _ _ _ e3 Hvs) as (va & Hva & Rva).
      pose proof (repr_eval_self Σ _ _ _ Rva ev2) as ->.
      do 3 eexists; split; [eapply eval_step; eapply eval_Proj_step; eassumption|exact Rva].
    - (* constructor block, variable *)
      pose proof (repr_eval_self Σ _ _ _ Hrv (eval_construct_block _ _ _ _ _ _ _ _ e e0 e1 a)) as Hv.
      rewrite Hv. do 3 eexists; split; [eapply eval_step; eapply eval_Rel_fuel; exact Hn|exact Hrv].
    - (* constructor block *)
      cbn in Heq. injection Heq as -> -> Hargs.
      assert (Hwa : forallb (wellformed Σ #|rho|) args0).
      { cbn in Hwf. move/andP: Hwf => [_ Hw]. destruct cstr_as_blocks.
        - move/andP: Hw => [_ Hw]. exact Hw.
        - destruct args0; [reflexivity|discriminate]. }
      assert (Hmany : exists vs fs trs, eval_fuel_many Σ rho args0 vs fs trs /\ Forall2 (repr Σ) vs args').
      { clear -Hr Hwa Hargs iha. revert args0 Hargs Hwa iha. induction a as [|x y l l' r a IHa]; intros args0 Hargs Hwa iha.
        - destruct args0; [|discriminate]. do 3 eexists; split; [constructor|constructor].
        - destruct args0 as [|x0 xs]; [discriminate|]. cbn in Hargs. injection Hargs as Hx Hl.
          cbn in Hwa. move/andP: Hwa => [Hwx Hwl].
          destruct iha as [Hx' Htl].
          destruct (Hx' _ _ _ Hr Hwx Hx) as (v1 & f1 & t1 & D1 & R1).
          destruct (IHa xs Hl Hwl Htl) as (vs & fs & trs & Dm & Rm).
          do 3 eexists; split; [eapply eval_many_cons; eassumption|constructor; assumption]. }
      destruct Hmany as (vs & fs & trs & Dm & Rm).
      do 3 eexists; split; [eapply eval_step; eapply eval_Construct_step; [reflexivity|exact Dm]|].
      constructor; [exact Rm|exact (repr_all_closed _ _ _ Rm)].
    - (* application congruence: impossible *)
      cbn in Heq. injection Heq as -> ->. cbn in Hwf. move/andP: Hwf => [/andP [_ Hw1] _].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (? & ? & ? & _ & Hb).
      exfalso. inversion Hb; subst; vm_compute in i; discriminate i.
    - (* primitive, variable *)
      pose proof (repr_eval_self Σ _ _ _ Hrv (eval_prim _ _ _ ev)) as Hv.
      rewrite Hv. do 3 eexists; split; [eapply eval_step; eapply eval_Rel_fuel; exact Hn|exact Hrv].
    - (* primitive *)
      cbn in Hwf. move/andP: Hwf => [Hp _].
      destruct (prim_trans HnoArr prim Hp) as (pv & Hpv).
      rewrite (trans_prim_val_subst ts 0 prim pv Hpv) in Heq. injection Heq as ->.
      pose proof (repr_eval_self Σ _ _ _ (repr_prim Σ _ _ Hpv) (eval_prim _ _ _ ev)) as ->.
      do 3 eexists; split; [eapply eval_step; eapply eval_Prim_step; exact Hpv|constructor; exact Hpv].
    - (* force: impossible *)
      cbn in Heq. injection Heq as ->. cbn in Hwf. move/andP: Hwf => [_ Hw1].
      destruct (IHev1 _ _ _ Hr Hw1 eq_refl) as (? & ? & ? & _ & Hb). inversion Hb.
    - (* atom: a constructor without block is not an atom *)
      exfalso. subst t. destruct args; vm_compute in i; discriminate i.
  Qed.

End Simulation.

(** The simulation for closed terms, with the conditions as explicit hypotheses. *)
Theorem wcbv_to_eval_env_fuel {efl : EEnvFlags} (Σ : global_declarations)
        {trace : Type} {Hf : @LambdaBox_resource nat} {Ht : @LambdaBox_resource trace} :
  wf_glob Σ ->
  has_tRel = true -> has_tApp = true ->
  has_tBox = false -> has_tCoFix = false -> has_tLazy_Force = false ->
  has_primarray = false -> has_cstr_params = false ->
  forall e v, @eval wfl Σ e v -> wellformed Σ 0 e ->
  exists rv f tr, @eval_env_fuel trace Hf Ht Σ [] e (Val rv) f tr /\ repr Σ rv v.
Proof.
  intros Hwfg HtRel HtApp HnoBox HnoCoFix HnoLazy HnoArr Hnopars e v ev Hwf.
  exact (wcbv_sim Σ Hwfg HtRel HtApp HnoBox HnoCoFix HnoLazy HnoArr Hnopars e v ev [] [] e
           (Forall2_nil _) Hwf (eq_sym (subst_empty 0 e))).
Qed.

(** * Flags with variables and applications allowed

    Allowing [tRel] and [tApp] in the flags keeps every well-formed term well
    formed; the simulation uses the term [tApp (tRel 0) (tRel 1)] in the case
    of a fixpoint, so it is run under [with_rel_app efl]. *)

Definition with_rel_app (efl : EEnvFlags) : EEnvFlags :=
  {| has_axioms := @has_axioms efl;
     has_cstr_params := @has_cstr_params efl;
     term_switches :=
       {| has_tBox := @has_tBox (@term_switches efl);
          has_tRel := true;
          has_tVar := @has_tVar (@term_switches efl);
          has_tEvar := @has_tEvar (@term_switches efl);
          has_tLambda := @has_tLambda (@term_switches efl);
          has_tLetIn := @has_tLetIn (@term_switches efl);
          has_tApp := true;
          has_tConst := @has_tConst (@term_switches efl);
          has_tConstruct := @has_tConstruct (@term_switches efl);
          has_tCase := @has_tCase (@term_switches efl);
          has_tProj := @has_tProj (@term_switches efl);
          has_tFix := @has_tFix (@term_switches efl);
          has_tCoFix := @has_tCoFix (@term_switches efl);
          has_tPrim := @has_tPrim (@term_switches efl);
          has_tLazy_Force := @has_tLazy_Force (@term_switches efl) |};
     cstr_as_blocks := @cstr_as_blocks efl |}.

Lemma wellformed_with_rel_app {efl : EEnvFlags} (Σ : global_declarations) k t :
  @wellformed efl Σ k t -> @wellformed (with_rel_app efl) Σ k t.
Proof.
  induction t in k |- * using term_forall_list_ind; cbn; intros H; rtoProp; intuition auto.
  all: try solve [solve_all].
  all: try solve [destruct cstr_as_blocks; [|assumption]; rtoProp; split; [assumption|solve_all]].
  all: try solve [unfold wf_fix_gen in *; rtoProp; split; [assumption|solve_all]].
  all: try solve [destruct p as [? []]; cbn in *; rtoProp; intuition auto; solve_all].
Qed.

Lemma wf_glob_with_rel_app {efl : EEnvFlags} (Σ : global_declarations) :
  @wf_glob efl Σ -> @wf_glob (with_rel_app efl) Σ.
Proof.
  induction 1 as [|kn d Σ HΣ IH Hd Hf]; constructor; [exact IH| |exact Hf].
  destruct d as [cb|mib]; cbn in *.
  - destruct (cst_body cb); cbn in *; [exact (wellformed_with_rel_app _ _ _ Hd)|exact Hd].
  - exact Hd.
Qed.

(** The simulation for closed terms, under the flag conditions [has_tBox = false]
    and [has_cstr_params = false] and those of [anf_source_ok]. *)
Theorem wcbv_to_eval_env_fuel' {efl : EEnvFlags} (Σ : global_declarations)
        {trace : Type} {Hf : @LambdaBox_resource nat} {Ht : @LambdaBox_resource trace} :
  wf_glob Σ ->
  has_tBox = false -> has_tCoFix = false -> has_tLazy_Force = false ->
  has_primarray = false -> has_cstr_params = false ->
  forall e v, @eval wfl Σ e v -> wellformed Σ 0 e ->
  exists rv f tr, @eval_env_fuel trace Hf Ht Σ [] e (Val rv) f tr /\
                  @repr (with_rel_app efl) Σ rv v.
Proof.
  intros Hwfg HnoBox HnoCoFix HnoLazy HnoArr Hnopars e v ev Hwf.
  exact (@wcbv_to_eval_env_fuel (with_rel_app efl) Σ trace Hf Ht (wf_glob_with_rel_app Σ Hwfg)
           eq_refl eq_refl HnoBox HnoCoFix HnoLazy HnoArr Hnopars e v ev
           (wellformed_with_rel_app Σ 0 e Hwf)).
Qed.
