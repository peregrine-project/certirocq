(** * CertiGC_Contract: the contract of CertiGC's collector, in generic form

    CertiGC (Wang, Cao, Mohan, Hobor et al.) verifies in VST the generational
    copying collector [gc_stack.c] that the LLVM backend links.  This file
    states its contract over abstract memories, addresses, roots and value
    representations: called with the roots registered through [tinfo->fp] and
    [tinfo->nalloc = n], the collector frees at least [n] words, updates the
    roots to their relocated addresses, and preserves the representation of
    every root up to the relocation.

    [LambdaANF_to_LLVM_correct] does not use this file.  Its hypothesis on the
    collector is [runtime_correct] in [LambdaANF_to_LLVM_statement.v], stated
    over Vellvm's memory.  No proof derives [runtime_correct] from CertiGC's
    theorem; that would need a relation between CompCert's memory model and
    Vellvm's. *)

From Stdlib Require Import List. Import ListNotations.

Section CertiGC_Contract.

  Variable Mem  : Type.                 (* Vellvm [memory_stack] *)
  Variable Addr : Type.                 (* Vellvm [addr] *)
  Variable Val  : Type.                 (* source value: [term.val] *)

  (* the shadow-stack roots live in [m], enumerated through [tinfo->fp] *)
  Variable roots_registered : Mem -> Addr (* tinfo *) -> list Addr -> Prop.
  (* [tinfo->nalloc = n] *)
  Variable nalloc_set       : Mem -> Addr -> nat -> Prop.
  (* the collector ran and returned, taking [m] to [m'] *)
  Variable gc_runs          : Mem -> Addr -> Mem -> Prop.
  (* at least [n] words are free after collection *)
  Variable words_free       : Mem -> Addr -> nat -> Prop.
  (* value representation of a source value at an address in a memory *)
  Variable ReprVal          : Mem -> Val -> Addr -> Prop.

  (** The precondition the mutator (our generated code + shadow stack) must
      establish before calling [garbage_collect]. *)
  Definition gc_pre (m : Mem) (tinfo : Addr) (roots : list Addr) (n : nat) : Prop :=
    roots_registered m tinfo roots /\ nalloc_set m tinfo n.

  (** CertiGC's proven contract, adopted as an FFI assumption.  [reloc] is the
      relocation CertiGC's copying phase computes; it is the identity on
      already-tenured objects and moves nursery survivors. *)
  Definition CertiGC_spec : Prop :=
    forall (m : Mem) (tinfo : Addr) (roots : list Addr) (n : nat),
      gc_pre m tinfo roots n ->
      exists (m' : Mem) (reloc : Addr -> Addr),
        gc_runs m tinfo m'
        /\ words_free m' tinfo n
        /\ (* roots are updated to their relocated addresses *)
           (forall r, In r roots -> roots_registered m' tinfo (map reloc roots))
        /\ (* THE fact [Econstr_case] consumes: value-representation of every
              live root is preserved, up to relocation *)
           (forall (v : Val) (r : Addr),
              In r roots -> ReprVal m v r -> ReprVal m' v (reloc r)).

End CertiGC_Contract.
