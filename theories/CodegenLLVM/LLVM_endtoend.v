(** * End-to-end correctness of the LLVM path, from λ□ to the emitted module

    [LambdaBox_to_LLVM_correct] composes three theorems of CertiRocq:
    - [anf_toplevel.convert_top_anf_correct]: λ□ -> LambdaANF, for the
      environment semantics with fuel [fuel_sem.eval_env_fuel] of λ□ and the
      value relation [anf_toplevel.value_ref];
    - [toplevel_theorems.anf_pipeline_whole_program_correct]: the λANF
      passes ([toplevel.anf_pipeline], run by [toplevel.run_anf_pipeline]),
      with the value relation [rel_comp.value_ref_cc];
    - [LLVM_sim_exp.LambdaANF_to_LLVM_correct], through its first-order
      form [LLVM_corollaries.LLVM_correct_first_order].

    The three stages are those Peregrine's [llvm_pipeline] runs when no
    constant is remapped to a primitive ([llvm_stages]; [llvm_stages_run]
    shows that the monadic pipeline [llvm_pipeline] returns the same module).
    Besides CertiRocq's conditions on the source program and the runtime
    contract [runtime_correct], the theorem asks for [llvm_checks], a boolean
    test of the intermediate programs: the program after λ□ -> LambdaANF is
    closed with unique bindings, the constructor environment after the λANF
    passes extends that of the source inductives, and the final program is in
    the fragment of the LLVM theorem ([llvm_fragmentb]).

    The source semantics is [fuel_sem.eval_env_fuel], the semantics that
    CertiRocq's λ□ -> LambdaANF theorem is stated for.  [LambdaBox_to_LLVM_correct_wcbv]
    states the same for MetaRocq's [EWcbvEval.eval] under the named
    hypothesis [wcbv_fuel_sem_link] relating the two semantics.

    [NegbTrue] at the end is a non-vacuity instance ([negb true]). *)

From Stdlib Require Import ZArith NArith List Lia String.
From ITree Require Import ITree Eq.Eqit.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.Libraries Semantics.InterpretationStack Semantics.TopLevel
  Handlers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_corollaries
  LLVM_fragment LLVM_restricted_check.
From CertiRocq.CodegenLLVM Require toplevel.
From MetaRocq.Erasure Require Import EAst EWellformed EGlobalEnv EWcbvEval.
From MetaRocq.Common Require Import Kernames BasicAst.
From CertiRocq.Common Require Import AstCommon compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import term term_util eval algebra identifiers set_util
  shrink_cps_correct rel_comp toplevel_theorems.
From CertiRocq.LambdaANF Require toplevel.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common fuel_sem anf_convert_env anf_correct.
From CertiRocq.LambdaBox_to_LambdaANF Require anf anf_toplevel.

Import ListNotations.
Unset Implicit Arguments.

Module AT := CertiRocq.LambdaANF.toplevel.
Module LT := CertiRocq.CodegenLLVM.toplevel.

(* ------------------------------------------------------------------ *)
(** ** Links between the semantics of LambdaANF *)

(** [cenv'] has every constructor of [cenv], with the same inductive,
    arity and ordinal. *)
Definition cenv_extends (cenv cenv' : ctor_env) : Prop :=
  forall t i, M.get t cenv = Some i ->
    exists i', M.get t cenv' = Some i' /\
      ctor_ind_tag i' = ctor_ind_tag i /\ ctor_arity i' = ctor_arity i /\
      ctor_ordinal i' = ctor_ordinal i.

Lemma caseConsistent_extends cenv cenv' cl t :
  cenv_extends cenv cenv' -> caseConsistent cenv cl t -> caseConsistent cenv' cl t.
Proof.
  intros Hext H. induction H as [t|info info' l t t' e Ht Ht' Hind _ IH].
  - constructor.
  - destruct (Hext _ _ Ht) as (i1 & G1 & E1 & _).
    destruct (Hext _ _ Ht') as (i2 & G2 & E2 & _).
    econstructor; [exact G1|exact G2| |exact IH]. congruence.
Qed.

Section Transfer.
  Context {fuel1 : Type} {Hf1 : @fuel_resource fuel1} {trace1 : Type} {Ht1 : @trace_resource trace1}.
  Context {fuel2 : Type} {Hf2 : @fuel_resource fuel2} {trace2 : Type} {Ht2 : @trace_resource trace2}.
  Variables (cenv cenv' : ctor_env).
  Hypothesis Hext : cenv_extends cenv cenv'.

  (** A terminating run in one fuel/trace instance, under [cenv], is a
      terminating run in any other instance, under any extension [cenv']. *)
  Lemma bstep_fuel_transfer rho e c v t :
    @bstep_fuel cenv fuel1 Hf1 trace1 Ht1 rho e c (Res v) t ->
    exists c' t', @bstep_fuel cenv' fuel2 Hf2 trace2 Ht2 rho e c' (Res v) t'.
  Proof.
    intros H. remember (Res v) as r eqn:Er. revert v Er.
    induction H using bstep_fuel_ind' with
      (P := fun rho e c r t => forall v, r = Res v ->
              exists c' t', @bstep cenv' fuel2 Hf2 trace2 Ht2 rho e c' (Res v) t');
      intros; subst; try discriminate;
      repeat match goal with H : Res _ = Res _ |- _ => inversion H; subst; clear H end;
      repeat match goal with
             | IH : forall v, Res ?w = Res v -> exists _ _, _ |- _ =>
                 destruct (IH w eq_refl) as (? & ? & ?); clear IH
             end;
      do 2 eexists; econstructor; eauto using caseConsistent_extends.
  Qed.
End Transfer.

Section ToBstepE.
  Context {fuel : Type} {Hf : @fuel_resource fuel} {trace : Type} {Ht : @trace_resource trace}.
  Variables (pfs : prims) (cenv : ctor_env).

  (** A terminating run of the fuel semantics is a run of [bstep_e]. *)
  Lemma bstep_fuel_bstep_e rho e c v t :
    bstep_fuel cenv rho e c (Res v) t -> exists n, bstep_e pfs cenv rho e v n.
  Proof.
    intros H. remember (Res v) as r eqn:Er. revert v Er.
    induction H using bstep_fuel_ind' with
      (P := fun rho e c r t => forall v, r = Res v -> exists n, bstep_e pfs cenv rho e v n);
      intros; subst; try discriminate;
      repeat match goal with H : Res _ = Res _ |- _ => inversion H; subst; clear H end;
      repeat match goal with
             | IH : forall v, Res ?w = Res v -> exists _, _ |- _ =>
                 destruct (IH w eq_refl) as (? & ?); clear IH
             end;
      repeat match goal with
             | H : find_tag_nth ?cl ?t ?e ?n |- _ =>
                 assert (findtag cl t = Some e) by (apply find_tag_nth_findtag; eauto); clear H
             end;
      eexists;
      first [ eassumption | solve [eapply BStep_constr; eauto] | solve [eapply BStep_proj; eauto]
            | solve [eapply BStep_case; eauto] | solve [eapply BStep_app; eauto]
            | solve [eapply BStep_letapp; eauto] | solve [eapply BStep_fun; eauto]
            | solve [eapply BStep_prim_val; eauto] | solve [eapply BStep_halt; eauto] ].
  Qed.
End ToBstepE.

(* ------------------------------------------------------------------ *)
(** ** First-order values across the three theorems *)

(** First-order λ□ values: trees of constructors whose leaves are
    constructors without fields or primitive integers. *)
Inductive src_first_order : fuel_sem.value -> Prop :=
| SFO_con c vs : Forall src_first_order vs -> src_first_order (fuel_sem.Con_v c vs)
| SFO_int n : src_first_order (fuel_sem.Prim_v (existT _ primInt n)).

(** The LambdaANF value of a first-order λ□ value: every constructor [c]
    becomes its tag in [tgm]. *)
Inductive fo_translate (tgm : conId_map) : fuel_sem.value -> term.val -> Prop :=
| FT_con c t vs ws :
    dcon_to_tag c tgm = Some t -> Forall2 (fo_translate tgm) vs ws ->
    fo_translate tgm (fuel_sem.Con_v c vs) (Vconstr t ws)
| FT_int n :
    fo_translate tgm (fuel_sem.Prim_v (existT _ primInt n)) (Vprim (existT _ primInt n)).

Lemma value_ref_fo tgm v1 :
  src_first_order v1 -> forall v2, anf_toplevel.value_ref tgm v1 v2 ->
  fo_translate tgm v1 v2 /\ first_order v2.
Proof.
  induction v1 as [dc vs IH | vs na e IH | vs defs n IH | pv] using fuel_sem.value_ind';
    intros Hfo v2 Hr; inversion Hfo; subst.
  - destruct v2 as [t ws| | | ]; cbn in Hr; try contradiction. destruct Hr as [Ht Hf].
    match goal with H : Forall src_first_order vs |- _ => rename H into Hsf end.
    assert (Hfs : Forall2 (fo_translate tgm) vs ws /\ Forall first_order ws).
    { clear Ht Hfo. revert IH Hsf ws Hf. induction vs as [|a vs IHvs]; intros IH Hsf ws Hf.
      - inversion Hf; subst. split; constructor.
      - inversion Hf as [|? b ? ws' Hab Hrest]; subst.
        inversion IH as [|? ? IHa IHrest]; subst.
        inversion Hsf as [|? ? Hfa Hfrest]; subst.
        destruct (IHa Hfa b (proj1 (anf_toplevel.value_ref_eq tgm a b) Hab)) as [T1 F1].
        destruct (IHvs IHrest Hfrest ws' Hrest) as [T2 F2].
        split; constructor; assumption. }
    destruct Hfs as [Hfs1 Hfs2]. split; econstructor; eassumption.
  - destruct v2; cbn in Hr; try contradiction. subst. split; constructor.
Qed.

Lemma value_ref_cc_fo v1 :
  first_order v1 -> forall v2, rel_comp.value_ref_cc v1 v2 -> v2 = v1.
Proof.
  induction v1 as [t|t v l IHv IHl| | p | z] using val_ind'; intros Hfo v2 Hr.
  - destruct v2; cbn in Hr; try contradiction. destruct Hr as [-> Hf]. inversion Hf. reflexivity.
  - destruct v2 as [t' ws| | | ]; cbn in Hr; try contradiction. destruct Hr as [<- Hf].
    inversion Hf as [|? w ? ws' Hvw Hrest]; subst.
    inversion Hfo as [? ? Hall|]; subst. inversion Hall as [|? ? Hfv Hfl]; subst.
    assert (w = v) by (apply IHv; [assumption| apply value_ref_cc_eq; assumption]).
    assert (Vconstr t ws' = Vconstr t l)
      by (apply IHl; [constructor; assumption | cbn; split; [reflexivity|assumption]]).
    congruence.
  - inversion Hfo.
  - destruct v2; cbn in Hr; try contradiction. congruence.
  - inversion Hfo.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Inductive environment of the source and the stages of the pipeline *)

(** The source's inductive environment, the tag map of its constructors and
    the constructor environment computed from them by CertiRocq's front end. *)
Definition src_ienv (p : AT.LambdaBoxEAstTerm) : ienv := inductive_env_east (fst p).
Definition src_tgm (p : AT.LambdaBoxEAstTerm) : conId_map :=
  snd (convert_env AT.default_ctor_tag AT.default_ind_tag (src_ienv p)).
Definition src_cenv (p : AT.LambdaBoxEAstTerm) : ctor_env :=
  anf_toplevel.top_cenv AT.default_ctor_tag AT.default_ind_tag (src_ienv p).

(** λ□ -> LambdaANF as [AT.compile_LambdaANF_ANF next_id []] runs it. *)
Definition anf_stage (next_id : positive) (p : AT.LambdaBoxEAstTerm)
  : error AT.LambdaANF_FullTerm :=
  let prims : list (primitive * positive) := [] in
  let prim_env := AT.make_prim_env prims in
  let ie := inductive_env_east (fst p) in
  let '(_, _, _, _, dcm) := convert_env AT.default_ctor_tag AT.default_ind_tag ie in
  match anf.convert_top_anf AT.fun_fun_tag AT.default_ctor_tag prim_env AT.default_ind_tag
          next_id dcm prims (fun _ => None) ie (List.rev (fst p)) (snd p) with
  | (compM.Ret e, data) =>
      let (_, ctag, itag, ftag, cenv, fenv, nenv, _, _) := data in
      Ret (M.empty _, prim_env, cenv, ctag, itag, nenv, fenv, M.empty _, e)
  | (compM.Err s, _) => Err s
  end.

(** The three stages Peregrine's [llvm_pipeline] runs (with the direct, ANF,
    front end and no remapped constants): λ□ -> LambdaANF, the λANF passes,
    the LLVM emitter.  The result holds the two intermediate programs and the
    module. *)
Definition llvm_stages (next_id : positive) (o : Options) (p : AT.LambdaBoxEAstTerm)
  : error (AT.LambdaANF_FullTerm * AT.LambdaANF_FullTerm * LLprog) :=
  match anf_stage next_id p with
  | Err s => Err s
  | Ret t0 =>
      match fst (AT.run_anf_pipeline next_id (AT.make_anf_options o) t0) with
      | Err s => Err s
      | Ret t1 =>
          match fst (LT.LambdaANF_to_LLVM_Wrapper [] (c_args o) t1) with
          | Err s => Err s
          | Ret m => Ret (t0, t1, m)
          end
      end
  end.

(** The constructor environment of an intermediate program. *)
Definition full_cenv (t : AT.LambdaANF_FullTerm) : ctor_env :=
  let '(_, _, cenv, _, _, _, _, _, _) := t in cenv.

(** Unique bindings of an arbitrary program ([LLVM_fragment.ub] rejects
    nested [Efun]): [ub_all e s] returns [s] plus the variables [e] binds,
    or [None] if one of them is bound twice or is in [s]. *)
Fixpoint ub_all (e : exp) (s : PS.t) {struct e} : option PS.t :=
  match e with
  | Econstr x _ _ e' | Eproj x _ _ _ e' | Eletapp x _ _ _ e'
  | Eprim_val x _ e' | Eprim x _ _ e' =>
      match LLVM_fragment.add_fresh x s with
      | Some s1 => ub_all e' s1
      | None => None
      end
  | Ecase _ bs =>
      (fix go (bs : list (ctor_tag * exp)) (s : PS.t) : option PS.t :=
         match bs with
         | [] => Some s
         | (_, e') :: bs' =>
             match ub_all e' s with
             | Some s1 => go bs' s1
             | None => None
             end
         end) bs s
  | Efun fds e' =>
      match ub_all_fundefs fds s with
      | Some s1 => ub_all e' s1
      | None => None
      end
  | Eapp _ _ _ | Ehalt _ => Some s
  end
with ub_all_fundefs (fds : fundefs) (s : PS.t) {struct fds} : option PS.t :=
  match fds with
  | Fcons f _ ys e fds' =>
      match LLVM_fragment.add_fresh f s with
      | None => None
      | Some s1 =>
          match LLVM_fragment.add_list ys s1 with
          | None => None
          | Some s2 =>
              match ub_all e s2 with
              | None => None
              | Some s3 => ub_all_fundefs fds' s3
              end
          end
      end
  | Fnil => Some s
  end.

Lemma ub_all_spec e s s' :
  ub_all e s = Some s' ->
  unique_bindings e /\ (forall x, bound_var e x -> ~ PS.In x s) /\
  (forall y, PS.In y s' <-> PS.In y s \/ bound_var e y).
Proof.
  revert e s s'.
  apply (exp_mut
    (fun e => forall s s', ub_all e s = Some s' ->
       unique_bindings e /\ (forall x, bound_var e x -> ~ PS.In x s) /\
       (forall y, PS.In y s' <-> PS.In y s \/ bound_var e y))
    (fun fds => forall s s', ub_all_fundefs fds s = Some s' ->
       unique_bindings_fundefs fds /\ (forall x, bound_var_fundefs fds x -> ~ PS.In x s) /\
       (forall y, PS.In y s' <-> PS.In y s \/ bound_var_fundefs fds y))).
  - intros v t l e IHe s s' H; simpl in H. ub_binder IHe H v s.
  - intros v s s' H; simpl in H. inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb; subst. contradiction.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy; subst; contradiction]].
  - intros v l c e IHe IHe0 s s' H; simpl in H.
    destruct (ub_all e s) as [s1|] eqn:He; [|discriminate].
    destruct (IHe _ _ He) as (Hu & Hd & Hm).
    destruct (IHe0 s1 s' H) as (Hu' & Hd' & Hm').
    split; [|split].
    + constructor; [exact Hu'|exact Hu|].
      constructor. intros y Hc. destruct Hc as [y H1 H2].
      apply (Hd' _ H2). apply Hm. auto.
    + intros x Hb. apply bound_case_cons in Hb as [Hb|Hb]; [exact (Hd _ Hb)|].
      intros Hc. apply (Hd' _ Hb). apply Hm. auto.
    + intros y. rewrite Hm', Hm, bound_case_cons. tauto.
  - intros v t n v0 e IHe s s' H; simpl in H. ub_binder IHe H v s.
  - intros x f ft ys e IHe s s' H; simpl in H. ub_binder IHe H x s.
  - intros f2 IHf e IHe s s' H; simpl in H.
    destruct (ub_all_fundefs f2 s) as [s1|] eqn:Hf; [|discriminate].
    destruct (IHf _ _ Hf) as (Hu & Hd & Hm).
    destruct (IHe _ _ H) as (Hu' & Hd' & Hm').
    split; [|split].
    + constructor; [exact Hu'|exact Hu|].
      constructor. intros y Hc. destruct Hc as [y H1 H2].
      apply (Hd' _ H1). apply Hm. right. exact H2.
    + intros x Hb. destruct (proj1 (bound_var_Efun f2 e) x Hb) as [x Hb'|x Hb'].
      * exact (Hd _ Hb').
      * intros Hc. apply (Hd' _ Hb'). apply Hm. left. exact Hc.
    + intros y. rewrite Hm', Hm. split.
      * intros [[Hy|Hy]|Hy]; [left; exact Hy| |];
          right; apply (proj2 (bound_var_Efun f2 e)); [left|right]; exact Hy.
      * intros [Hy|Hy]; [left; left; exact Hy|].
        destruct (proj1 (bound_var_Efun f2 e) y Hy) as [y Hy'|y Hy'];
          [left; right|right]; exact Hy'.
  - intros v t l s s' H; simpl in H. inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy]].
  - intros v p e IHe s s' H; simpl in H. ub_binder IHe H v s.
  - intros v p l e IHe s s' H; simpl in H. ub_binder IHe H v s.
  - intros v s s' H; simpl in H. inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy]].
  - intros f t ys e IHe fds IH s s' H; simpl in H.
    destruct (LLVM_fragment.add_fresh f s) as [s1|] eqn:Ha; [|discriminate].
    destruct (LLVM_fragment.add_list ys s1) as [s2|] eqn:Hl; [|discriminate].
    destruct (ub_all e s2) as [s3|] eqn:He; [|discriminate].
    destruct (LLVM_restricted_check.add_fresh_spec _ _ _ Ha) as [Hn Hs].
    destruct (LLVM_restricted_check.add_list_spec _ _ _ Hl) as (Hnd & Hdl & Hml).
    destruct (IHe _ _ He) as (Hu & Hd & Hm).
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
  - intros s s' H; simpl in H. inversion H; subst. split; [constructor|split].
    + intros x Hb. inversion Hb.
    + intros y. split; [auto|intros [Hy|Hy]; [exact Hy|inversion Hy]].
Qed.

(** Boolean version of [cenv_extends]. *)
Definition cenv_extendsb (cenv cenv' : ctor_env) : bool :=
  forallb (fun ti =>
             match M.get (fst ti) cenv' with
             | Some i' =>
                 Pos.eqb (ctor_ind_tag i') (ctor_ind_tag (snd ti)) &&
                 N.eqb (ctor_arity i') (ctor_arity (snd ti)) &&
                 N.eqb (ctor_ordinal i') (ctor_ordinal (snd ti))
             | None => false
             end) (M.elements cenv).

Lemma cenv_extendsb_sound cenv cenv' :
  cenv_extendsb cenv cenv' = true -> cenv_extends cenv cenv'.
Proof.
  unfold cenv_extendsb. intros H t i Ht.
  apply M.elements_correct in Ht. rewrite forallb_forall in H.
  specialize (H _ Ht). cbn in H.
  destruct (M.get t cenv') as [i'|]; [|discriminate].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  apply Pos.eqb_eq in H1. apply N.eqb_eq in H2, H3. eauto.
Qed.

(** The checks on the intermediate programs [t0] (after λ□ -> LambdaANF)
    and [t1] (after the λANF passes):
    - [t0] is closed and has unique bindings (what the λANF passes'
      theorem asks of its input);
    - the constructor environment of [t1] extends the one of the source's
      inductives ([src_cenv]) with the same inductive, arity and ordinal for
      every constructor;
    - [t1] is in the fragment of the LLVM theorem ([llvm_fragmentb], whose
      soundness is [llvm_fragmentb_sound]). *)
Definition llvm_checks (p : AT.LambdaBoxEAstTerm) (t0 t1 : AT.LambdaANF_FullTerm) : bool :=
  llvm_closedb (snd t0) &&
  (match ub_all (snd t0) PS.empty with Some _ => true | None => false end) &&
  cenv_extendsb (src_cenv p) (full_cenv t1) &&
  llvm_fragmentb (full_cenv t1) (snd t1).

(* ------------------------------------------------------------------ *)
(** ** Inversion of the stages *)

Lemma anf_stage_inv next_id p t0 :
  anf_stage next_id p = Ret t0 ->
  exists data,
    anf.convert_top_anf AT.fun_fun_tag AT.default_ctor_tag (AT.make_prim_env []) AT.default_ind_tag
      next_id (src_tgm p) [] (fun _ => None) (src_ienv p) (List.rev (fst p)) (snd p)
    = (compM.Ret (snd t0), data).
Proof.
  unfold anf_stage, src_tgm, src_ienv.
  destruct (convert_env _ _ _) as [[[[a1 a2] a3] a4] dcm]. cbn [snd].
  match goal with
  | |- context [anf.convert_top_anf ?a ?b ?c ?d ?e ?f ?g ?h ?i ?j ?k] =>
      destruct (anf.convert_top_anf a b c d e f g h i j k) as [[s|e0] data]
  end; intros H; try discriminate.
  destruct data. injection H as <-. eexists; reflexivity.
Qed.

Lemma run_anf_pipeline_inv next_id opts t0 t1 log :
  AT.run_anf_pipeline next_id opts t0 = (Ret t1, log) ->
  exists c c',
    (identifiers.max_var (snd t0) 1 < state.next_var c)%positive /\
    AT.anf_pipeline next_id opts (snd t0) c = (compM.Ret (snd t1), c').
Proof.
  destruct t0 as [[[[[[[[a b] cenv] ctag] itag] nenv] fenv] rho] e0].
  unfold AT.run_anf_pipeline.
  match goal with
  | |- context [AT.anf_pipeline ?x ?y ?z ?w] =>
      destruct (AT.anf_pipeline x y z w) as [r c'] eqn:E
  end.
  destruct r as [s|e1]; intros H; [discriminate|].
  destruct c'. injection H as <- _.
  do 2 eexists. split; [|exact E]. cbn. lia.
Qed.

Lemma wrapper_inv args t1 m :
  fst (LT.LambdaANF_to_LLVM_Wrapper [] args t1) = Ret m ->
  m = emitted (full_cenv t1) (LT.prim_of []) (snd t1).
Proof.
  destruct t1 as [[[[[[[[a b] cenv] ctag] itag] nenv] fenv] rho] e1].
  unfold LT.LambdaANF_to_LLVM_Wrapper.
  destruct (llvm_buildable _ _ _); cbn; intros H; [|discriminate].
  injection H as <-. reflexivity.
Qed.

(** A program not of the form [Efun fds main] is treated as [Efun Fnil e]. *)
Lemma prog_parts_norm cenv po e :
  let fds := fst (prog_parts e) in let main := snd (prog_parts e) in
  emitted cenv po e = emitted cenv po (Efun fds main) /\
  llvm_fragmentb cenv e = llvm_fragmentb cenv (Efun fds main) /\
  (forall pfs rho v n, bstep_e pfs cenv rho e v n -> bstep_e pfs cenv rho (Efun fds main) v n).
Proof.
  destruct e; cbn [prog_parts fst snd];
    (split; [reflexivity|split; [reflexivity|]]); intros; try assumption;
    constructor; cbn; assumption.
Qed.

Section RefinesRun.
  Context {fuel1 : Type} {Hf1 : @fuel_resource fuel1} {trace1 : Type} {Ht1 : @trace_resource trace1}.
  Context {fuel2 : Type} {Hf2 : @fuel_resource fuel2} {trace2 : Type} {Ht2 : @trace_resource trace2}.

  Lemma refines_run cenv0 cenv1 vref e e' v1 c t :
    @rel_comp.refines fuel2 trace2 Hf2 Ht2 cenv1 vref e e' ->
    cenv_extends cenv0 cenv1 ->
    @bstep_fuel cenv0 fuel1 Hf1 trace1 Ht1 (M.empty _) e c (Res v1) t ->
    exists v2 c2 t2,
      @bstep_fuel cenv1 fuel2 Hf2 trace2 Ht2 (M.empty _) e' c2 (Res v2) t2 /\ vref v1 v2.
  Proof.
    intros [Hterm _] Hext H.
    destruct (@bstep_fuel_transfer fuel1 Hf1 trace1 Ht1 fuel2 Hf2 trace2 Ht2 cenv0 cenv1 Hext _ _ _ _ _ H)
      as (c' & t' & H').
    exact (Hterm v1 c' t' H').
  Qed.
End RefinesRun.

(* ------------------------------------------------------------------ *)
(** ** The end-to-end theorem *)

(** What CertiRocq's λ□ -> LambdaANF theorem ([convert_top_anf_correct])
    asks of the source program [p], for the environment flags [efl]: no
    axioms, variables, existential variables, cofixpoints, lazy/force or
    primitive arrays; constructors applied as blocks; a well-formed global
    environment and main term; and every global constant has a well-formed
    body that evaluates, with fuel 0, to a value. *)
Definition anf_source_ok {efl : EEnvFlags} (p : AT.LambdaBoxEAstTerm) : Prop :=
  has_axioms = false /\ has_tVar = false /\ has_tEvar = false /\ has_tCoFix = false /\
  has_tLazy_Force = false /\ cstr_as_blocks = true /\ has_primarray = false /\
  wf_glob (fst p) /\ wellformed (fst p) 0%nat (snd p) = true /\
  (forall k decl body,
      declared_constant (fst p) k decl -> cst_body decl = Some body ->
      exists src_v f t, @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
                          (fst p) [] body (Val src_v) f t) /\
  (forall k decl body src_v f t,
      declared_constant (fst p) k decl -> cst_body decl = Some body ->
      @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
        (fst p) [] body (Val src_v) f t -> f = 0%nat) /\
  (forall k decl body,
      declared_constant (fst p) k decl -> cst_body decl = Some body ->
      wellformed (fst p) 0%nat body = true).

(** If the λ□ program [p] evaluates to a first-order value [v], and the
    pipeline compiles it to the module [m] with the checks passing, then
    [m], run with a runtime that meets [runtime_correct], runs out of memory
    or returns a word [z] that represents the translation [w] of [v]
    ([fo_translate]: constructors renamed to their tags) in the final memory
    [st] ([fo_word]). *)
Theorem LambdaBox_to_LLVM_correct {efl : EEnvFlags} (next_id : positive) (o : Options)
        (p : AT.LambdaBoxEAstTerm) (t0 t1 : AT.LambdaANF_FullTerm) (m : LLprog)
        (heap_inv : Memory.state -> ptr -> Prop)
        (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
        (v : fuel_sem.value) (f tr : nat) :
  (forall cenv fds, runtime_correct cenv fds heap_inv gc make_tinfo) ->
  anf_source_ok p ->
  llvm_stages next_id o p = Ret (t0, t1, m) ->
  llvm_checks p t0 t1 = true ->
  @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
    (fst p) [] (snd p) (Val v) f tr ->
  src_first_order v ->
  ends_in_oom (run_program gc make_tinfo m)
  \/ exists st ls genv z,
      returns (run_program gc make_tinfo m) ((st, (ls, genv)), I64 z) /\
      exists w, fo_translate (src_tgm p) v w /\ fo_word (full_cenv t1) st w z.
Proof.
  intros Hrt (HnoAx & HnoVar & HnoEvar & HnoCoFix & HnoLazy & Hblocks & HnoArray &
              Hwfg & Hwf & Hgt & Hgz & Hgw) Hst Hchk Hev Hfo.
  unfold llvm_stages in Hst.
  destruct (anf_stage next_id p) as [s|t0'] eqn:E0; [discriminate|].
  destruct (AT.run_anf_pipeline next_id (AT.make_anf_options o) t0') as [r1 log] eqn:E1.
  destruct r1 as [s|t1']; cbn [fst] in Hst; [discriminate|].
  destruct (fst (LT.LambdaANF_to_LLVM_Wrapper [] (c_args o) t1')) as [s|m'] eqn:E2;
    [discriminate|].
  injection Hst as -> -> ->.
  (* λ□ -> LambdaANF *)
  assert (Hie : wf_env_east (src_ienv p)) by (apply wf_env_inductive; exact Hwfg).
  assert (Hcoh : cenv_tgm_coherence (src_cenv p) (src_tgm p)).
  { pose proof (cenv_tgm_coh AT.default_ctor_tag AT.default_ind_tag _ Hie) as Hc.
    revert Hc. unfold src_cenv, src_tgm, anf_toplevel.top_cenv.
    destruct (convert_env _ _ _) as [[[[? ?] ?] ?] ?]. exact (fun Hc => Hc). }
  destruct (anf_stage_inv _ _ _ E0) as [data Ecvt].
  destruct (@anf_toplevel.convert_top_anf_correct AT.fun_fun_tag AT.kon_fun_tag
              AT.default_ctor_tag AT.default_ind_tag (src_tgm p) (fst p) efl HnoAx
              (convert_env_inj _ _ _ Hie) (convert_env_reg _ _ _) Hgt Hgz Hgw
              (AT.make_prim_env []) [] Hwfg HnoVar HnoEvar HnoCoFix HnoLazy Hblocks HnoArray
              (fun _ => eq_refl) (src_ienv p) Hcoh next_id (snd p) (snd t0) data Hwf Ecvt)
    as [M Href].
  destruct (Href v f tr Hev) as (v1 & c1 & Hrun1 & _ & Hvr).
  destruct (value_ref_fo _ _ Hfo _ Hvr) as [Htr Hfo1].
  (* the checks *)
  unfold llvm_checks in Hchk.
  apply andb_true_iff in Hchk as [Hchk Hfrag]. apply andb_true_iff in Hchk as [Hchk Hext].
  apply andb_true_iff in Hchk as [Hc Hu].
  pose proof (llvm_closedb_sound _ Hc) as Hc'.
  destruct (ub_all (snd t0) PS.empty) as [s|] eqn:Eub; [|discriminate].
  destruct (ub_all_spec _ _ _ Eub) as (Huniq & _ & _).
  apply cenv_extendsb_sound in Hext.
  assert (Hclosed : closed_exp (snd t0)).
  { split; intros x Hx; [exfalso; apply Hc'; eauto | inversion Hx]. }
  assert (Hws : well_scoped (snd t0)).
  { split; [exact Huniq|]. constructor. intros x Hx. inversion Hx; subst. apply Hc'. eauto. }
  (* λANF passes *)
  destruct (run_anf_pipeline_inv _ _ _ _ _ E1) as (c & c' & Hfresh & Ep).
  destruct (anf_pipeline_whole_program_correct (full_cenv t1) next_id (AT.make_anf_options o)
              (snd t0) c Hclosed Hws Hfresh) as (e' & c'' & Ep' & Href2).
  rewrite Ep in Ep'. injection Ep' as <- _.
  destruct (refines_run _ _ _ _ _ _ _ _ Href2 Hext Hrun1) as (v2 & c2 & t2 & Hrun2 & Hv2).
  apply value_ref_cc_fo in Hv2; [|exact Hfo1]. subst v2.
  destruct (bstep_fuel_bstep_e (M.empty _) _ _ _ _ _ _ Hrun2) as (n & Hbe).
  (* LambdaANF -> LLVM *)
  apply wrapper_inv in E2. subst m.
  destruct (prog_parts_norm (full_cenv t1) (LT.prim_of []) (snd t1)) as (Hem & Hfr & Hbs).
  rewrite Hem.
  pose proof (llvm_fragmentb_sound _ _ _ (eq_trans (eq_sym Hfr) Hfrag)) as Hres.
  destruct (@LLVM_correct_first_order (full_cenv t1) (M.empty _) (LT.prim_of [])
              heap_inv gc make_tinfo _ _ (Hrt _ _) Hres v1 n Hfo1 (Hbs _ _ _ _ Hbe))
    as [Ho|(st & ls & genv & z & Hr & Hw)].
  - left. exact Ho.
  - right. exists st, ls, genv, z. split; [exact Hr|]. exists v1. split; assumption.
Qed.

(** A λ□ program whose value is a constructor [c] without fields returns
    the word [2 * ord + 1], where [ord] is the ordinal of [c]'s tag in the
    constructor environment of the source's inductives. *)
Corollary LambdaBox_to_LLVM_correct_nullary {efl : EEnvFlags} (next_id : positive) (o : Options)
        (p : AT.LambdaBoxEAstTerm) (t0 t1 : AT.LambdaANF_FullTerm) (m : LLprog)
        (heap_inv : Memory.state -> ptr -> Prop)
        (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
        (c : dcon) (t : ctor_tag) (f tr : nat) :
  (forall cenv fds, runtime_correct cenv fds heap_inv gc make_tinfo) ->
  anf_source_ok p ->
  llvm_stages next_id o p = Ret (t0, t1, m) ->
  llvm_checks p t0 t1 = true ->
  @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
    (fst p) [] (snd p) (Val (fuel_sem.Con_v c [])) f tr ->
  dcon_to_tag c (src_tgm p) = Some t ->
  ends_in_oom (run_program gc make_tinfo m)
  \/ exists st ls genv,
      returns (run_program gc make_tinfo m)
              ((st, (ls, genv)), I64 (2 * Z.of_N (ord_of (src_cenv p) t) + 1)).
Proof.
  intros Hrt Hsrc Hst Hchk Hev Ht.
  pose proof Hsrc as (_ & _ & _ & _ & _ & _ & _ & Hwfg & _).
  pose proof Hchk as Hchk'. unfold llvm_checks in Hchk'.
  apply andb_true_iff in Hchk' as [Hchk' _]. apply andb_true_iff in Hchk' as [_ Hext].
  apply cenv_extendsb_sound in Hext.
  destruct (@LambdaBox_to_LLVM_correct efl next_id o p t0 t1 m heap_inv gc make_tinfo _ f tr
              Hrt Hsrc Hst Hchk Hev (@SFO_con c [] (Forall_nil _)))
    as [Ho|(st & ls & genv & z & Hr & w & Hw & Hz)].
  - left. exact Ho.
  - right. exists st, ls, genv.
    inversion Hw as [c' t' vs ws Ht' Hf|]; subst. inversion Hf; subst.
    rewrite Ht in Ht'. injection Ht' as <-.
    cbn [fo_word] in Hz. subst z.
    assert (Hie : wf_env_east (src_ienv p)) by (apply wf_env_inductive; exact Hwfg).
    assert (Hcoh : cenv_tgm_coherence (src_cenv p) (src_tgm p)).
    { pose proof (cenv_tgm_coh AT.default_ctor_tag AT.default_ind_tag _ Hie) as Hc.
      revert Hc. unfold src_cenv, src_tgm, anf_toplevel.top_cenv.
      destruct (convert_env _ _ _) as [[[[? ?] ?] ?] ?]. exact (fun Hc => Hc). }
    destruct c as [ind n]. destruct (Hcoh ind n n t t Ht Ht) as (i & _ & Hi & _ & _).
    destruct (Hext _ _ Hi) as (i' & Hi' & _ & _ & Hord).
    replace (ord_of (src_cenv p) t) with (ord_of (full_cenv t1) t); [exact Hr|].
    unfold ord_of. rewrite Hi, Hi', Hord. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The same for MetaRocq's weak call-by-value semantics *)

(** First-order λ□ values as MetaRocq terms: trees of constructors applied
    as blocks. *)
Inductive term_value : fuel_sem.value -> EAst.term -> Prop :=
| TV_con ind n vs ts :
    Forall2 term_value vs ts ->
    term_value (fuel_sem.Con_v (dcon_of_con ind n) vs) (tConstruct ind n ts).

Lemma term_value_fo v t : term_value v t -> src_first_order v.
Proof.
  revert t. induction v as [dc vs IH | | | ] using fuel_sem.value_ind'; intros t Htv;
    inversion Htv; subst.
  constructor.
  match goal with HF : Forall2 term_value vs _ |- _ => clear Htv; revert IH; induction HF end;
    intros IH; constructor; inversion IH; subst; eauto.
Qed.

(** The flags of MetaRocq's weak call-by-value evaluation for the erased
    programs CertiRocq's front end receives ([Erasure.final_wcbv_flags]: no
    case on proofs, unguarded fixpoints, constructors as blocks). *)
Definition certirocq_wcbv_flags : EWcbvEval.WcbvFlags := Erasure.final_wcbv_flags.

(** Named hypothesis: for the program [p], a MetaRocq evaluation to a
    constructor tree [t] is matched by a run of [fuel_sem.eval_env_fuel] to
    the value [t] denotes.  The two semantics of λ□ are not related by a
    theorem in CertiRocq. *)
Definition wcbv_fuel_sem_link (p : AT.LambdaBoxEAstTerm) : Prop :=
  forall t, @EWcbvEval.eval certirocq_wcbv_flags (fst p) (snd p) t ->
    (exists v0, term_value v0 t) ->
    exists v f tr,
      @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
        (fst p) [] (snd p) (Val v) f tr /\ term_value v t.

(** [LambdaBox_to_LLVM_correct] for MetaRocq's evaluation, under
    [wcbv_fuel_sem_link]. *)
Theorem LambdaBox_to_LLVM_correct_wcbv {efl : EEnvFlags} (next_id : positive) (o : Options)
        (p : AT.LambdaBoxEAstTerm) (t0 t1 : AT.LambdaANF_FullTerm) (m : LLprog)
        (heap_inv : Memory.state -> ptr -> Prop)
        (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
        (t : EAst.term) :
  wcbv_fuel_sem_link p ->
  (forall cenv fds, runtime_correct cenv fds heap_inv gc make_tinfo) ->
  anf_source_ok p ->
  llvm_stages next_id o p = Ret (t0, t1, m) ->
  llvm_checks p t0 t1 = true ->
  @EWcbvEval.eval certirocq_wcbv_flags (fst p) (snd p) t ->
  (exists v0, term_value v0 t) ->
  ends_in_oom (run_program gc make_tinfo m)
  \/ exists st ls genv z,
      returns (run_program gc make_tinfo m) ((st, (ls, genv)), I64 z) /\
      exists v w, term_value v t /\ fo_translate (src_tgm p) v w /\ fo_word (full_cenv t1) st w z.
Proof.
  intros Hlink Hrt Hsrc Hst Hchk Hev Hfo.
  destruct (Hlink t Hev Hfo) as (v & f & tr & Hev' & Htv).
  destruct (@LambdaBox_to_LLVM_correct efl next_id o p t0 t1 m heap_inv gc make_tinfo v f tr
              Hrt Hsrc Hst Hchk Hev' (term_value_fo v t Htv))
    as [Ho|(st & ls & genv & z & Hr & w & Hw & Hz)].
  - left. exact Ho.
  - right. exists st, ls, genv, z. split; [exact Hr|]. exists v, w. auto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [llvm_stages] is what CertiRocq's monadic pipeline computes *)

From ExtLib Require Import Structures.Monads.
Import MonadNotation.

(** The pipeline as Peregrine composes it, in CertiRocq's pipeline monad. *)
Definition llvm_pipeline (next_id : positive) : CertiRocqTrans AT.LambdaBoxEAstTerm LLprog :=
  fun p =>
    p1 <- AT.compile_LambdaANF_ANF next_id [] p ;;
    p2 <- AT.compile_LambdaANF next_id p1 ;;
    LT.compile_LambdaANF_to_LLVM [] p2.


Local Transparent bind ret.

Lemma bind_run {A B} (m : pipelineM A) (f : A -> pipelineM B) o w :
  runState (bind m f) o w =
  let (a, w') := runState m o w in
  match a with Ret x => runState (f x) o w' | Err s => (Err s, w') end.
Proof. destruct m as [m]. cbn. destruct (m o w) as [[s|x] w']; reflexivity. Qed.

Lemma anf_stage_run next_id p o w :
  fst (runState (AT.compile_LambdaANF_ANF next_id [] p) o w) = anf_stage next_id p.
Proof.
  unfold AT.compile_LambdaANF_ANF, LiftErrorCertiRocqTrans, debug_msg, get_options, timePhase_opt.
  rewrite bind_run. destruct w. cbn. destruct (debug o), (time o); reflexivity.
Qed.

Lemma anf_passes_run next_id t o w :
  fst (runState (AT.compile_LambdaANF next_id t) o w) =
  fst (AT.run_anf_pipeline next_id (AT.make_anf_options o) t).
Proof.
  unfold AT.compile_LambdaANF, LiftErrorLogCertiRocqTrans, debug_msg, get_options, timePhase_opt.
  rewrite bind_run. destruct w. cbn. destruct (debug o), (time o); cbn;
    destruct (AT.run_anf_pipeline _ _ _) as [[] ?]; reflexivity.
Qed.

Lemma llvm_emit_run t o w :
  fst (runState (LT.compile_LambdaANF_to_LLVM [] t) o w) =
  fst (LT.LambdaANF_to_LLVM_Wrapper [] (c_args o) t).
Proof.
  unfold LT.compile_LambdaANF_to_LLVM, LiftErrorLogCertiRocqTrans, debug_msg, get_options, timePhase_opt.
  rewrite bind_run. destruct w. cbn. destruct (debug o), (time o); cbn;
    destruct (LT.LambdaANF_to_LLVM_Wrapper _ _ _) as [[] ?]; reflexivity.
Qed.

(** When [llvm_stages] returns a module, the monadic pipeline returns the same module. *)
Lemma llvm_stages_run next_id o p t0 t1 m :
  llvm_stages next_id o p = Ret (t0, t1, m) ->
  fst (run_pipeline _ _ o p (llvm_pipeline next_id)) = Ret m.
Proof.
  unfold llvm_stages, run_pipeline, llvm_pipeline. intros H.
  generalize (Build_CompInfo [] [] []) as w. intros w.
  rewrite bind_run.
  pose proof (anf_stage_run next_id p o w) as E0.
  destruct (runState (AT.compile_LambdaANF_ANF next_id [] p) o w) as [a w1].
  cbn [fst] in E0. subst a.
  destruct (anf_stage next_id p) as [s|t0']; [discriminate|].
  rewrite bind_run.
  pose proof (anf_passes_run next_id t0' o w1) as E1.
  destruct (runState (AT.compile_LambdaANF next_id t0') o w1) as [a1 w2].
  cbn [fst] in E1. subst a1.
  destruct (fst (AT.run_anf_pipeline next_id (AT.make_anf_options o) t0')) as [s|t1'];
    [discriminate|].
  pose proof (llvm_emit_run t1' o w2) as E2.
  destruct (runState (LT.compile_LambdaANF_to_LLVM [] t1') o w2) as [a2 w3].
  cbn [fst] in E2. subst a2.
  destruct (fst (LT.LambdaANF_to_LLVM_Wrapper [] (c_args o) t1')) as [s|m']; [discriminate|].
  injection H as _ _ ->. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity: [negb true]

    The λ□ program [(fun b => match b with true => false | false => true end) true]
    ([negb true] with [negb] unfolded, so the global environment holds only
    the inductive [bool]).  Every hypothesis of [LambdaBox_to_LLVM_correct_nullary]
    holds for it with the witness runtime of [LLVM_nonvacuity]
    ([negb_true_hypotheses]): the source conditions, the pipeline's result
    and checks (computed in Rocq), the evaluation to [false], and
    [runtime_correct]; so do the MetaRocq evaluation to [false] and the
    hypothesis [wcbv_fuel_sem_link] of [LambdaBox_to_LLVM_correct_wcbv].  The theorem then says that the compiled module runs
    out of memory or returns [3 = 2 * 1 + 1], the unboxed word of [false]
    ([negb_true_correct]). *)

From CertiRocq.CodegenLLVM Require Import LLVM_nonvacuity.
From MetaRocq.Utils Require Import bytestring.

Module NegbTrue.
  Local Open Scope bs_scope.

  Definition bool_kn : kername := (MPfile ["Datatypes"; "Init"; "Corelib"], "bool").
  Definition bool_ind : inductive := {| inductive_mind := bool_kn; inductive_ind := 0%nat |}.
  Definition bool_body : one_inductive_body :=
    {| ind_name := "bool"; ind_propositional := false; ind_kelim := Universes.IntoAny;
       ind_ctors := [mkConstructor "true" 0%nat; mkConstructor "false" 0%nat];
       ind_projs := [] |}.
  Definition bool_decl : mutual_inductive_body :=
    {| ind_finite := Finite; ind_npars := 0%nat; ind_bodies := [bool_body] |}.

  Definition prog : AT.LambdaBoxEAstTerm :=
    ([(bool_kn, InductiveDecl bool_decl)],
     tApp (tLambda (nNamed "b")
             (tCase (bool_ind, 0%nat) (tRel 0%nat)
                [([], tConstruct bool_ind 1%nat []); ([], tConstruct bool_ind 0%nat [])]))
          (tConstruct bool_ind 0%nat [])).

  (** Environment flags: only the term formers [prog] uses. *)
  Definition flags : EEnvFlags :=
    {| has_axioms := false; has_cstr_params := false;
       term_switches :=
         {| has_tBox := false; has_tRel := true; has_tVar := false; has_tEvar := false;
            has_tLambda := true; has_tLetIn := false; has_tApp := true; has_tConst := false;
            has_tConstruct := true; has_tCase := true; has_tProj := false; has_tFix := false;
            has_tCoFix := false;
            has_tPrim := {| has_primint := false; has_primfloat := false;
                            has_primstring := false; has_primarray := false |};
            has_tLazy_Force := false |};
       cstr_as_blocks := true |}.

  (** The options of Peregrine's [default_llvm_config] ([mk_opts]). *)
  Definition opts : Options :=
    {| erasure_config := Erasure.default_erasure_config; inductives_mapping := [];
       direct := true; c_args := 5%nat; anf_variant := 0%nat; show_anf := false;
       o_level := 1%nat; time := false; time_anf := false; debug := false;
       body_name := "body"; Pipeline_utils.prims := [] |}.

  (** Peregrine's [next_id]. *)
  Definition next_id : positive := 100%positive.

  Lemma source_ok : @anf_source_ok flags prog.
  Proof.
    unfold anf_source_ok.
    repeat split; try reflexivity.
    - constructor; [constructor|reflexivity|constructor].
    - intros k decl body Hd. exfalso. unfold declared_constant in Hd. cbn in Hd.
      match type of Hd with context [if ?b then _ else _] => destruct b end; discriminate.
    - intros k decl body src_v f t Hd. exfalso. unfold declared_constant in Hd. cbn in Hd.
      match type of Hd with context [if ?b then _ else _] => destruct b end; discriminate.
    - intros k decl body Hd. exfalso. unfold declared_constant in Hd. cbn in Hd.
      match type of Hd with context [if ?b then _ else _] => destruct b end; discriminate.
  Qed.

  Definition stages_result := Eval vm_compute in llvm_stages next_id opts prog.

  Lemma stages_eq : llvm_stages next_id opts prog = stages_result.
  Proof. vm_compute. reflexivity. Qed.

  Lemma stages :
    exists t0 t1 m, llvm_stages next_id opts prog = Ret (t0, t1, m) /\
                    llvm_checks prog t0 t1 = true.
  Proof.
    pose proof stages_eq as E. unfold stages_result in E.
    do 3 eexists. split; [exact E|]. vm_compute. reflexivity.
  Qed.

  Lemma eval :
    exists f tr, @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
                   (fst prog) [] (snd prog) (Val (fuel_sem.Con_v (dcon_of_con bool_ind 1) [])) f tr.
  Proof.
    do 2 eexists. cbn [fst snd prog].
    eapply eval_step. eapply eval_App_step.
    - eapply eval_step. eapply eval_Lam_fuel.
    - eapply eval_step. eapply eval_Construct_step; [reflexivity|eapply eval_many_nil].
    - eapply eval_step. eapply eval_Case_step.
      + eapply eval_step. eapply eval_Rel_fuel. reflexivity.
      + reflexivity.
      + reflexivity.
      + eapply eval_step. eapply eval_Construct_step; [reflexivity|eapply eval_many_nil].
  Qed.

  Definition false_tag : ctor_tag :=
    Eval vm_compute in
      match dcon_to_tag (dcon_of_con bool_ind 1) (src_tgm prog) with
      | Some t => t | None => 1%positive end.

  Lemma false_tag_eq : dcon_to_tag (dcon_of_con bool_ind 1) (src_tgm prog) = Some false_tag.
  Proof. vm_compute. reflexivity. Qed.

  Lemma false_ord : ord_of (src_cenv prog) false_tag = 1%N.
  Proof. vm_compute. reflexivity. Qed.

  Lemma wcbv_eval : @EWcbvEval.eval certirocq_wcbv_flags (fst prog) (snd prog) (tConstruct bool_ind 1%nat []).
  Proof.
    cbn [fst snd prog].
    eapply EWcbvEval.eval_beta.
    - apply EWcbvEval.eval_atom. reflexivity.
    - eapply EWcbvEval.eval_construct_block with (mdecl := bool_decl) (idecl := bool_body) (cdecl := mkConstructor "true" 0%nat);
        [reflexivity|vm_compute; reflexivity|reflexivity|constructor].
    - cbn. eapply EWcbvEval.eval_iota_block with (c := 0%nat) (args := []) (cdecl := mkConstructor "true" 0%nat);
        [reflexivity| |vm_compute; reflexivity|reflexivity|reflexivity|reflexivity|].
      + eapply EWcbvEval.eval_construct_block with (mdecl := bool_decl) (idecl := bool_body) (cdecl := mkConstructor "true" 0%nat);
        [reflexivity|vm_compute; reflexivity|reflexivity|constructor].
      + cbn. eapply EWcbvEval.eval_construct_block with (mdecl := bool_decl) (idecl := bool_body) (cdecl := mkConstructor "false" 0%nat);
        [reflexivity|vm_compute; reflexivity|reflexivity|constructor].
  Defined.

  Lemma wcbv_link : wcbv_fuel_sem_link prog.
  Proof.
    intros t Hev _.
    pose proof (EWcbvEval.eval_deterministic Hev wcbv_eval) as ->.
    destruct eval as (f & tr & H).
    exists (fuel_sem.Con_v (dcon_of_con bool_ind 1) []), f, tr. split; [exact H|].
    constructor. constructor.
  Qed.
  (** Every hypothesis of [LambdaBox_to_LLVM_correct_nullary], for [prog],
      [false] and the witness runtime. *)
  Theorem negb_true_hypotheses :
    (forall cenv fds, runtime_correct cenv fds nv_heap_inv nv_gc nv_make_tinfo) /\
    @anf_source_ok flags prog /\
    (exists t0 t1 m, llvm_stages next_id opts prog = Ret (t0, t1, m) /\
                     llvm_checks prog t0 t1 = true) /\
    (exists f tr, @eval_env_fuel nat LambdaBox_resource_fuel LambdaBox_resource_trace
                    (fst prog) [] (snd prog) (Val (fuel_sem.Con_v (dcon_of_con bool_ind 1) [])) f tr) /\
    dcon_to_tag (dcon_of_con bool_ind 1) (src_tgm prog) = Some false_tag /\
    wcbv_fuel_sem_link prog /\
    inhabited (@EWcbvEval.eval certirocq_wcbv_flags (fst prog) (snd prog) (tConstruct bool_ind 1%nat [])).
  Proof.
    split; [exact nv_runtime_correct|].
    split; [exact source_ok|]. split; [exact stages|]. split; [exact eval|].
    split; [exact false_tag_eq|]. split; [exact wcbv_link|]. exact (inhabits wcbv_eval).
  Qed.

  (** The compiled [negb true] runs out of memory or returns [3]. *)
  Theorem negb_true_correct :
    exists t0 t1 m, llvm_stages next_id opts prog = Ret (t0, t1, m) /\
      (ends_in_oom (run_program nv_gc nv_make_tinfo m)
       \/ exists st ls genv,
           returns (run_program nv_gc nv_make_tinfo m) ((st, (ls, genv)), I64 3)).
  Proof.
    destruct stages as (t0 & t1 & m & Hst & Hchk).
    destruct eval as (f & tr & Hev).
    exists t0, t1, m. split; [exact Hst|].
    destruct (@LambdaBox_to_LLVM_correct_nullary flags next_id opts prog t0 t1 m
                nv_heap_inv nv_gc nv_make_tinfo _ false_tag f tr
                nv_runtime_correct source_ok Hst Hchk Hev false_tag_eq)
      as [Ho|(st & ls & genv & Hr)].
    - left. exact Ho.
    - right. exists st, ls, genv. rewrite false_ord in Hr. exact Hr.
  Qed.
End NegbTrue.
