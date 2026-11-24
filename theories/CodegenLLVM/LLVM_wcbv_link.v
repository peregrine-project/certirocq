(** * The LLVM theorem for MetaRocq's weak call-by-value evaluation, without a link hypothesis

    [wcbv_fuel_sem_link_holds] proves the hypothesis [wcbv_fuel_sem_link] of
    [LLVM_endtoend.LambdaBox_to_LLVM_correct_wcbv] from [anf_source_ok] and two
    decidable conditions on the environment flags [efl] of the source program:
    [has_tBox = false] and [has_cstr_params = false] ([wcbv_link_flags]).  The
    proof is the simulation [wcbv_fuel_sem.wcbv_to_eval_env_fuel'] of MetaRocq's
    [EWcbvEval.eval] by [fuel_sem.eval_env_fuel].

    [LambdaBox_to_LLVM_correct_wcbv'] is the end-to-end theorem from
    [EWcbvEval.eval] without the hypothesis, and [NegbTrue'] re-obtains the
    [negb true] instance from MetaRocq's evaluation. *)

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
  LLVM_fragment LLVM_restricted_check LLVM_endtoend.
From MetaRocq.Erasure Require Import EAst EWellformed EGlobalEnv EWcbvEval EInduction.
From MetaRocq.Common Require Import Kernames BasicAst.
From CertiRocq.Common Require Import AstCommon compM Pipeline_utils.
From CertiRocq.LambdaANF Require Import term eval.
From CertiRocq.LambdaBox_to_LambdaANF Require Import common fuel_sem anf_correct wcbv_fuel_sem.

Import ListNotations.
Unset Implicit Arguments.

(** A value that represents a constructor tree is the [term_value] of it. *)
Lemma repr_term_value {efl : EEnvFlags} (Σ : global_declarations) t :
  forall v0 rv, term_value v0 t -> repr Σ rv t -> term_value rv t.
Proof.
  induction t using term_forall_list_ind; intros v0 rv Htv Hr; inversion Htv; subst.
  inversion Hr; subst. constructor.
  match goal with
  | H1 : Forall2 term_value ?vs0 ?l, H2 : Forall2 (repr Σ) ?vs ?l |- Forall2 term_value ?vs ?l =>
      clear Htv Hr; repeat match goal with H : is_true (forallb _ _) |- _ => clear H end;
      revert vs0 vs H1 H2; induction X; intros vs0 vs H1 H2;
        inversion H1; subst; inversion H2; subst; constructor; eauto
  end.
Qed.

(** The conditions on the environment flags, besides those of [anf_source_ok]. *)
Definition wcbv_link_flags (efl : EEnvFlags) : Prop :=
  has_tBox = false /\ has_cstr_params = false.

Definition wcbv_link_flagsb (efl : EEnvFlags) : bool :=
  negb has_tBox && negb has_cstr_params.

Lemma wcbv_link_flagsb_sound efl : wcbv_link_flagsb efl = true -> wcbv_link_flags efl.
Proof.
  unfold wcbv_link_flagsb, wcbv_link_flags.
  destruct has_tBox, has_cstr_params; cbn; intros H; try discriminate.
  split; reflexivity.
Qed.

(** [wcbv_fuel_sem_link] holds for every program that meets
    [anf_source_ok] under flags that meet [wcbv_link_flags]. *)
Theorem wcbv_fuel_sem_link_holds {efl : EEnvFlags} (p : AT.LambdaBoxEAstTerm) :
  anf_source_ok p -> wcbv_link_flags efl -> wcbv_fuel_sem_link p.
Proof.
  intros (_ & _ & _ & HnoCoFix & HnoLazy & _ & HnoArr & Hwfg & Hwf & _)
         (HnoBox & Hnopars) t Hev (v0 & Htv).
  destruct (@wcbv_to_eval_env_fuel' efl (fst p) nat LambdaBox_resource_fuel LambdaBox_resource_trace
              Hwfg HnoBox HnoCoFix HnoLazy HnoArr Hnopars (snd p) t Hev Hwf)
    as (rv & f & tr & D & R).
  exists rv, f, tr. split; [exact D|]. exact (repr_term_value _ _ _ _ Htv R).
Qed.

(** [LambdaBox_to_LLVM_correct_wcbv] without the hypothesis [wcbv_fuel_sem_link]. *)
Theorem LambdaBox_to_LLVM_correct_wcbv' {efl : EEnvFlags} (next_id : positive) (o : Options)
        (p : AT.LambdaBoxEAstTerm) (t0 t1 : AT.LambdaANF_FullTerm) (m : LLprog)
        (heap_inv : Memory.state -> ptr -> Prop)
        (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
        (t : EAst.term) :
  wcbv_link_flags efl ->
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
  intros Hfl Hrt Hsrc.
  exact (@LambdaBox_to_LLVM_correct_wcbv efl next_id o p t0 t1 m heap_inv gc make_tinfo t
           (wcbv_fuel_sem_link_holds p Hsrc Hfl) Hrt Hsrc).
Qed.

(** A program that evaluates, in MetaRocq's semantics, to a constructor
    [ind, n] without fields returns the word [2 * ord + 1]. *)
Corollary LambdaBox_to_LLVM_correct_nullary_wcbv {efl : EEnvFlags} (next_id : positive) (o : Options)
        (p : AT.LambdaBoxEAstTerm) (t0 t1 : AT.LambdaANF_FullTerm) (m : LLprog)
        (heap_inv : Memory.state -> ptr -> Prop)
        (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
        (ind : inductive) (n : nat) (tg : ctor_tag) :
  wcbv_link_flags efl ->
  (forall cenv fds, runtime_correct cenv fds heap_inv gc make_tinfo) ->
  anf_source_ok p ->
  llvm_stages next_id o p = Ret (t0, t1, m) ->
  llvm_checks p t0 t1 = true ->
  @EWcbvEval.eval certirocq_wcbv_flags (fst p) (snd p) (tConstruct ind n []) ->
  dcon_to_tag (dcon_of_con ind n) (src_tgm p) = Some tg ->
  ends_in_oom (run_program gc make_tinfo m)
  \/ exists st ls genv,
      returns (run_program gc make_tinfo m)
              ((st, (ls, genv)), I64 (2 * Z.of_N (ord_of (src_cenv p) tg) + 1)).
Proof.
  intros Hfl Hrt Hsrc Hst Hchk Hev Htg.
  destruct (wcbv_fuel_sem_link_holds p Hsrc Hfl _ Hev
              (ex_intro _ (fuel_sem.Con_v (dcon_of_con ind n) []) (TV_con ind n [] [] (Forall2_nil _))))
    as (v & f & tr & D & Htv).
  inversion Htv; subst.
  match goal with H : Forall2 term_value _ [] |- _ => inversion H; subst end.
  exact (@LambdaBox_to_LLVM_correct_nullary efl next_id o p t0 t1 m heap_inv gc make_tinfo
           (dcon_of_con ind n) tg f tr Hrt Hsrc Hst Hchk D Htg).
Qed.

(* ------------------------------------------------------------------ *)
(** ** Non-vacuity: [negb true] from MetaRocq's evaluation *)

From CertiRocq.CodegenLLVM Require Import LLVM_nonvacuity.

Module NegbTrue'.
  Import NegbTrue.

  Lemma flags_ok : wcbv_link_flags flags.
  Proof. repeat split. Qed.

  (** The compiled [negb true] runs out of memory or returns [3]; the source
      premise is MetaRocq's evaluation [wcbv_eval], not [eval_env_fuel]. *)
  Theorem negb_true_correct_wcbv :
    exists t0 t1 m, llvm_stages next_id opts prog = Ret (t0, t1, m) /\
      (ends_in_oom (run_program nv_gc nv_make_tinfo m)
       \/ exists st ls genv,
           returns (run_program nv_gc nv_make_tinfo m) ((st, (ls, genv)), I64 3)).
  Proof.
    destruct stages as (t0 & t1 & m & Hst & Hchk).
    exists t0, t1, m. split; [exact Hst|].
    destruct (@LambdaBox_to_LLVM_correct_nullary_wcbv flags next_id opts prog t0 t1 m
                nv_heap_inv nv_gc nv_make_tinfo bool_ind 1%nat false_tag
                flags_ok nv_runtime_correct source_ok Hst Hchk wcbv_eval false_tag_eq)
      as [Ho|(st & ls & genv & Hr)].
    - left. exact Ho.
    - right. exists st, ls, genv. rewrite false_ord in Hr. exact Hr.
  Qed.
End NegbTrue'.
