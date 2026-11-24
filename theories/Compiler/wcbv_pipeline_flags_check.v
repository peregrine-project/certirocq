(** [wcbv_pipeline_flags.certirocq_pipeline_flags] is the flag record
    [certirocq_flags env_flags] of [Compiler/correctness.v]. *)

From CertiRocq.Compiler Require correctness.
From CertiRocq.LambdaBox_to_LambdaANF Require wcbv_pipeline_flags.

Lemma certirocq_pipeline_flags_eq :
  wcbv_pipeline_flags.certirocq_pipeline_flags = correctness.certirocq_flags correctness.env_flags.
Proof. reflexivity. Qed.
