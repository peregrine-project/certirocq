(** * The conditions of [LambdaBox_to_LLVM_correct_wcbv'] for the output of the MetaRocq pipeline

    CertiRocq's MetaRocq pipeline ([metarocq_pipeline.certirocq_post_metarocq_pipeline])
    ends with a program [p] whose global constants are λ-abstractions
    ([EWcbvEval.lambda_glob], part of its post-condition) and, in
    [correctness.metarocq_to_anf_correct], is asked to be well formed for the
    flags [certirocq_flags env_flags] (no axioms, no primitive arrays), here
    [certirocq_pipeline_flags] ([Compiler/wcbv_pipeline_flags_check.v]: the
    two are equal; [Compiler/correctness.v] and Vellvm cannot be loaded together).  For
    such a program, [pipeline_conditions] proves [anf_source_ok] and
    [wcbv_link_flags]; [LambdaBox_to_LLVM_correct_metarocq] is then the LLVM
    theorem from MetaRocq's evaluation with only those two hypotheses on [p]. *)

From Stdlib Require Import ZArith NArith List Lia String.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.Libraries Semantics.InterpretationStack Semantics.TopLevel
  Handlers.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement LLVM_corollaries
  LLVM_fragment LLVM_restricted_check LLVM_endtoend LLVM_wcbv_link.
From MetaRocq.Erasure Require Import EAst EWellformed EGlobalEnv EWcbvEval EProgram.
From MetaRocq.Common Require Import Kernames BasicAst.
From CertiRocq.Common Require Import AstCommon compM Pipeline_utils.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common fuel_sem anf_correct wcbv_pipeline_flags.

Import ListNotations.
Unset Implicit Arguments.

Notation pipeline_flags := certirocq_pipeline_flags.

(** [anf_source_ok] and [wcbv_link_flags] for a program well formed for the
    pipeline's flags whose global constants are λ-abstractions. *)
Theorem pipeline_conditions (p : eprogram) :
  wf_eprogram pipeline_flags p -> lambda_glob (fst p) ->
  @anf_source_ok pipeline_flags p /\ wcbv_link_flags pipeline_flags.
Proof.
  intros [Hwfg Hwf] Hl.
  destruct certirocq_pipeline_flags_values
    as (HnoAx & Hnopars & HnoBox & HnoVar & HnoEvar & HnoCoFix & HnoLazy & Hblocks & HnoArr).
  split; [|split; assumption].
  unfold anf_source_ok.
  split; [exact HnoAx|]. split; [exact HnoVar|]. split; [exact HnoEvar|].
  split; [exact HnoCoFix|]. split; [exact HnoLazy|]. split; [exact Hblocks|].
  split; [exact HnoArr|]. split; [exact Hwfg|]. split; [exact Hwf|].
  split; [|split].
  - intros k decl body Hd Hb.
    destruct (lambda_glob_body _ _ _ _ Hl Hd Hb) as (na & b & ->).
    do 3 eexists. eapply eval_step. eapply eval_Lam_fuel.
  - intros k decl body src_v f t Hd Hb Hev.
    destruct (lambda_glob_body _ _ _ _ Hl Hd Hb) as (na & b & ->).
    inversion Hev; subst.
    match goal with H : eval_env_step _ _ _ _ _ _ |- _ => inversion H; subst end.
    reflexivity.
  - intros k decl body Hd Hb.
    pose proof (@lookup_env_wellformed pipeline_flags _ _ _ Hwfg Hd) as Hw.
    cbn in Hw. rewrite Hb in Hw. exact Hw.
Qed.

(** The LLVM theorem from MetaRocq's evaluation for the output of the
    MetaRocq pipeline: no hypothesis on the source semantics, and only
    [wf_eprogram pipeline_flags p] and [lambda_glob (fst p)] on [p]. *)
Theorem LambdaBox_to_LLVM_correct_metarocq (next_id : positive) (o : Options)
        (p : eprogram) (t0 t1 : AT.LambdaANF_FullTerm) (m : LLprog)
        (heap_inv : Memory.state -> ptr -> Prop)
        (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
        (t : EAst.term) :
  wf_eprogram pipeline_flags p -> lambda_glob (fst p) ->
  (forall cenv fds, runtime_correct cenv fds heap_inv gc make_tinfo) ->
  llvm_stages next_id o p = Ret (t0, t1, m) ->
  llvm_checks p t0 t1 = true ->
  @EWcbvEval.eval certirocq_wcbv_flags (fst p) (snd p) t ->
  (exists v0, term_value v0 t) ->
  ends_in_oom (run_program gc make_tinfo m)
  \/ exists st ls genv z,
      returns (run_program gc make_tinfo m) ((st, (ls, genv)), I64 z) /\
      exists v w, term_value v t /\ fo_translate (src_tgm p) v w /\ fo_word (full_cenv t1) st w z.
Proof.
  intros Hwf Hl Hrt.
  destruct (pipeline_conditions p Hwf Hl) as [Hsrc Hfl].
  exact (@LambdaBox_to_LLVM_correct_wcbv' pipeline_flags next_id o p t0 t1 m heap_inv gc make_tinfo t
           Hfl Hrt Hsrc).
Qed.
