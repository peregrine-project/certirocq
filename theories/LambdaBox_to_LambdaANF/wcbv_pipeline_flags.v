(** * The environment flags of CertiRocq's MetaRocq pipeline

    [pipeline_flags] is [correctness.certirocq_flags correctness.env_flags]
    (checked by [Compiler/wcbv_pipeline_flags_check.v]), restated here so that
    files that load Vellvm, whose universes are inconsistent with those of
    [Compiler/correctness.v], can use it. *)

From Stdlib Require Import List.
From MetaRocq.Utils Require Import utils.
From MetaRocq.Common Require Import BasicAst Kernames.
From MetaRocq.Erasure Require Import EAst EGlobalEnv EWellformed EWcbvEval EImplementBox
  EImplementLazyForce.
From MetaRocq.ErasurePlugin Require Import ETransform.
From MetaRocq.Erasure Require EConstructorsAsBlocks EInlineProjections ERemoveParams.

Definition pipeline_env_flags :=
  let efl := EConstructorsAsBlocks.switch_cstr_as_blocks
    (EInlineProjections.disable_projections_env_flag
      (ERemoveParams.switch_no_params EWellformed.all_env_flags)) in
  let efl' := efl_coind_to_ind efl in
  switch_off_thunk (switch_off_box efl').

Definition pipeline_flags (efl : EEnvFlags) :=
  {| has_axioms := false;
     has_cstr_params := efl.(has_cstr_params);
     term_switches :=
       {| has_tBox := efl.(term_switches).(has_tBox)
        ; has_tRel := efl.(term_switches).(has_tRel)
        ; has_tVar := efl.(term_switches).(has_tVar)
        ; has_tEvar := efl.(term_switches).(has_tEvar)
        ; has_tLambda := efl.(term_switches).(has_tLambda)
        ; has_tLetIn := efl.(term_switches).(has_tLetIn)
        ; has_tApp := efl.(term_switches).(has_tApp)
        ; has_tConst := efl.(term_switches).(has_tConst)
        ; has_tConstruct := efl.(term_switches).(has_tConstruct)
        ; has_tCase := efl.(term_switches).(has_tCase)
        ; has_tProj := efl.(term_switches).(has_tProj)
        ; has_tFix := efl.(term_switches).(has_tFix)
        ; has_tCoFix := efl.(term_switches).(has_tCoFix)
        ; has_tPrim := {| has_primint := true; has_primfloat := true;
                          has_primstring := true; has_primarray := false |}
        ; has_tLazy_Force := efl.(term_switches).(has_tLazy_Force) |};
     cstr_as_blocks := efl.(cstr_as_blocks) |}.

(** The flags of the programs the pipeline hands to the λ□ -> LambdaANF stage. *)
Definition certirocq_pipeline_flags : EEnvFlags := pipeline_flags pipeline_env_flags.

Lemma certirocq_pipeline_flags_values :
  @has_axioms certirocq_pipeline_flags = false /\
  @has_cstr_params certirocq_pipeline_flags = false /\
  @has_tBox (@term_switches certirocq_pipeline_flags) = false /\
  @has_tVar (@term_switches certirocq_pipeline_flags) = false /\
  @has_tEvar (@term_switches certirocq_pipeline_flags) = false /\
  @has_tCoFix (@term_switches certirocq_pipeline_flags) = false /\
  @has_tLazy_Force (@term_switches certirocq_pipeline_flags) = false /\
  @cstr_as_blocks certirocq_pipeline_flags = true /\
  @has_primarray (@has_tPrim (@term_switches certirocq_pipeline_flags)) = false.
Proof. vm_compute. repeat split. Qed.

Lemma lambda_glob_body (Σ : global_declarations) k decl body :
  lambda_glob Σ -> declared_constant Σ k decl -> cst_body decl = Some body ->
  exists na b, body = tLambda na b.
Proof.
  unfold declared_constant. intros Hl. revert k decl body.
  induction Hl as [|kn d Σ Hl IH Hd]; intros k decl body Hk Hb; cbn in Hk; [discriminate|].
  destruct (eqb_spec k kn).
  - injection Hk as ->. destruct decl as [b']. cbn in Hb. subst b'. cbn in Hd.
    destruct Hd as (na & b & ->). eauto.
  - exact (IH _ _ _ Hk Hb).
Qed.
