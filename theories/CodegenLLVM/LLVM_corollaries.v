(** * First-order corollaries of [LambdaANF_to_LLVM_correct]

    The conclusion of [LambdaANF_to_LLVM_correct_statement] relates the
    returned word to the source value by [repr_val].  For values without
    functions the relation can be stated directly, and for values without
    fields without reference to the memory:

    - [LLVM_correct_nullary]: if the program's value is a constructor without
      fields, the module runs out of memory or returns the word
      [2 * ord_of cenv t + 1];
    - [LLVM_correct_int]: if it is a primitive integer [n], the module runs
      out of memory or returns the word [2 * Uint63.to_Z n + 1];
    - [LLVM_correct_first_order]: if it is a tree of constructors and
      primitive integers ([first_order]), the module runs out of memory or
      returns a word [z] with [fo_word cenv st v z], where [st] is Vellvm's
      final memory state.  [fo_word] is a structural recursion on the value
      that spells out the layout of [gc_stack.h]/[values.h]. *)

From Stdlib Require Import ZArith NArith List Lia String.
From ITree Require Import ITree Eq.Eqit.
From CertiRocq.LambdaANF Require Import term eval.
From CertiRocq.Common Require Import AstCommon.
From CertiRocq.CodegenLLVM Require Import LambdaANF_to_LLVM_statement.
From CertiRocq.CodegenLLVM Require LLVM_sim_exp.
From Vellvm Require Import
  Utils Syntax Params
  Interfaces.Memory Implementations.Memory
  Implementations.ParamsV Implementations.IPtrFinite
  Semantics.DynamicValues Semantics.LLVMEvents Semantics.Denotation
  Semantics.Libraries Semantics.InterpretationStack Semantics.TopLevel
  Handlers.

Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** First-order values and their words *)

(** Trees of constructors whose leaves are nullary constructors or
    primitive integers. *)
Inductive first_order : term.val -> Prop :=
| FO_constr t vs : Forall first_order vs -> first_order (Vconstr t vs)
| FO_int n : first_order (Vprim (existT _ primInt n)).

(** The fields of a block at [p]: field [i] is the word at [p + off + 8 i],
    related to the [i]-th value by [P]. *)
Definition fields_at (P : term.val -> Z -> Prop) (st : state) (p : ptr) :
  list term.val -> Z -> Prop :=
  fix fields (vs : list term.val) (off : Z) : Prop :=
    match vs with
    | [] => True
    | v :: vs' =>
        (exists q w, ptr_off p off q /\ reads_word st q w /\ P v w) /\
        fields vs' (off + 8)
    end.

(** [fo_word cenv st v z]: the word [z] represents the first-order value [v]
    in the memory [st]:
    - a constructor [t] without fields: [z = 2 * ord + 1] (unboxed);
    - a constructor [t] with fields [v_0 ... v_(k-1)]: [z] is the address of
      a word-aligned pointer [p]; the word at [p - 8] is the header
      [k * 1024 + ord]; the word at [p + 8 i] represents [v_i];
    - a primitive integer [n]: [z = 2 * Uint63.to_Z n + 1] (unboxed);
    - any other value: no word.
    Here [ord = ord_of cenv t], the ordinal of [t] in its inductive. *)
Fixpoint fo_word (cenv : ctor_env) (st : state) (v : term.val) (z : Z) {struct v} : Prop :=
  match v with
  | Vconstr t [] => z = 2 * Z.of_N (ord_of cenv t) + 1
  | Vconstr t vs =>
      exists p ph,
        z = ptr_to_int p /\ ptr_to_int p mod 8 = 0 /\
        ptr_off p (-8) ph /\
        reads_word st ph (Z.of_nat (length vs) * 1024 + Z.of_N (ord_of cenv t)) /\
        (fix fields (vs : list term.val) (off : Z) : Prop :=
           match vs with
           | [] => True
           | v :: vs' =>
               (exists q w, ptr_off p off q /\ reads_word st q w /\ fo_word cenv st v w) /\
               fields vs' (off + 8)
           end) vs 0
  | Vprim (existT primInt n) => z = 2 * Uint63.to_Z n + 1
  | _ => False
  end.

Lemma fo_word_constr cenv st t v vs z :
  fo_word cenv st (Vconstr t (v :: vs)) z <->
  exists p ph,
    z = ptr_to_int p /\ ptr_to_int p mod 8 = 0 /\
    ptr_off p (-8) ph /\
    reads_word st ph (Z.of_nat (length (v :: vs)) * 1024 + Z.of_N (ord_of cenv t)) /\
    fields_at (fo_word cenv st) st p (v :: vs) 0.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(** ** [repr_val] on first-order values *)

Scheme repr_val_mind := Induction for repr_val Sort Prop
  with repr_fields_mind := Induction for repr_fields Sort Prop.

Lemma repr_val_fo_word cenv fds genv st v z :
  repr_val cenv fds genv st v z -> first_order v -> fo_word cenv st v z.
Proof.
  intros Hr.
  induction Hr using repr_val_mind with
    (P0 := fun vs p off _ => Forall first_order vs -> fields_at (fo_word cenv st) st p vs off).
  - intros _. cbn [fo_word]. lia.
  - intros Hfo. inversion Hfo; subst.
    destruct vs as [|v vs]; [congruence|].
    apply fo_word_constr. do 2 eexists.
    split; [reflexivity|]. split; [eassumption|]. split; [eassumption|]. split.
    + match goal with
      | H : arity_of _ _ = _, R : reads_word _ _ _ |- _ => rewrite H, nat_N_Z in R; exact R
      end.
    + match goal with
      | IH : Forall _ _ -> fields_at _ _ _ _ _ |- _ => apply IH; assumption
      end.
  - intros _. cbn [fo_word]. lia.
  - intros Hfo. inversion Hfo.
  - intros _. exact I.
  - intros Hfo. inversion Hfo; subst. cbn [fields_at]. split.
    + do 2 eexists. split; [eassumption|]. split; [eassumption|].
      match goal with
      | IH : first_order ?v -> fo_word _ _ ?v _ |- fo_word _ _ ?v _ => apply IH; assumption
      end.
    + match goal with
      | IH : Forall _ ?vs -> fields_at _ _ _ ?vs _ |- fields_at _ _ _ ?vs _ => apply IH; assumption
      end.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The corollaries *)

Section Corollaries.
  Variables (cenv : ctor_env) (pfs : prims) (prim_of : positive -> option (string * bool))
            (heap_inv : state -> ptr -> Prop)
            (gc : list dvalue -> MCFGtop (exc + dvalue)) (make_tinfo : MCFGtop dvalue)
            (fds : fundefs) (main : term.exp).

  Hypothesis Hrt : runtime_correct cenv fds heap_inv gc make_tinfo.
  Hypothesis Hprog : llvm_restricted cenv fds main.

  Let run := run_program gc make_tinfo (emitted cenv prim_of (Efun fds main)).

  (** A program whose value is a constructor [t] without fields returns the
      word [2 * ord_of cenv t + 1], or runs out of memory. *)
  Theorem LLVM_correct_nullary t n :
    bstep_e pfs cenv (M.empty _) (Efun fds main) (Vconstr t []) n ->
    ends_in_oom run
    \/ exists st ls genv,
        returns run ((st, (ls, genv)), I64 (2 * Z.of_N (ord_of cenv t) + 1)).
  Proof.
    intros Hev.
    destruct (LLVM_sim_exp.LambdaANF_to_LLVM_correct cenv pfs prim_of heap_inv gc make_tinfo
                fds main _ n Hrt Hprog Hev) as [Ho|(st & ls & genv & z & Hr & Hrep)].
    - left. exact Ho.
    - right. exists st, ls, genv.
      pose proof (@repr_val_fo_word _ _ _ _ _ _ Hrep (@FO_constr t [] (Forall_nil _))) as Hz.
      cbn [fo_word] in Hz. subst z. exact Hr.
  Qed.

  (** A program whose value is the primitive integer [i] returns the word
      [2 * Uint63.to_Z i + 1], or runs out of memory. *)
  Theorem LLVM_correct_int i n :
    bstep_e pfs cenv (M.empty _) (Efun fds main) (Vprim (existT _ primInt i)) n ->
    ends_in_oom run
    \/ exists st ls genv,
        returns run ((st, (ls, genv)), I64 (2 * Uint63.to_Z i + 1)).
  Proof.
    intros Hev.
    destruct (LLVM_sim_exp.LambdaANF_to_LLVM_correct cenv pfs prim_of heap_inv gc make_tinfo
                fds main _ n Hrt Hprog Hev) as [Ho|(st & ls & genv & z & Hr & Hrep)].
    - left. exact Ho.
    - right. exists st, ls, genv.
      pose proof (@repr_val_fo_word _ _ _ _ _ _ Hrep (@FO_int i)) as Hz.
      cbn [fo_word] in Hz. subst z. exact Hr.
  Qed.

  (** A program whose value [v] is first-order returns a word [z] that
      represents [v] in the final memory [st] in the sense of [fo_word], or
      runs out of memory. *)
  Theorem LLVM_correct_first_order v n :
    first_order v ->
    bstep_e pfs cenv (M.empty _) (Efun fds main) v n ->
    ends_in_oom run
    \/ exists st ls genv z,
        returns run ((st, (ls, genv)), I64 z) /\ fo_word cenv st v z.
  Proof.
    intros Hfo Hev.
    destruct (LLVM_sim_exp.LambdaANF_to_LLVM_correct cenv pfs prim_of heap_inv gc make_tinfo
                fds main _ n Hrt Hprog Hev) as [Ho|(st & ls & genv & z & Hr & Hrep)].
    - left. exact Ho.
    - right. exists st, ls, genv, z. split; [exact Hr|].
      eapply repr_val_fo_word; eassumption.
  Qed.
End Corollaries.
