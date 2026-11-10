(** * CodegenLLVM.LLVM_fragment: the programs the LLVM backend accepts

    The checks on a LambdaANF program that [toplevel.v] runs before the emitter.
    This file is separate from [toplevel.v] so that [LLVM_restricted_check.v] can
    state their soundness next to the correctness statement. *)

From Stdlib Require Import ZArith List Bool.
Require Import LambdaANF.term.
Require Import Common.AstCommon.
Require Import CodegenLLVM.LambdaANF_to_LLVM.
Import ListNotations.

Local Open Scope bool_scope.

(** ctor-env projections: recover a constructor's ordinal / arity from [cenv]. *)
Definition ord_of   (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_ordinal info | None => 0%N end.
Definition arity_of (cenv : ctor_env) (t : ctor_tag) : N :=
  match M.get t cenv with Some info => ctor_arity info | None => 0%N end.

(** [fragment] decides the conditions on a function body of [body_ok] in
    [LambdaANF_to_LLVM_statement.v], with a stronger bound on allocation chunks;
    [LLVM_restricted_check.v] proves it sound.  [buildable] is weaker: it holds
    of every program outside the following three known failures, which it
    turns into compile-time errors.
    - A boxed constructor with an ordinal of 251 or more: [gc_stack.c] does not
      scan objects whose tag byte is at least [No_scan_tag = 251].
    - An allocation chunk larger than the nursery ([max_chunk] words, with
      [LOG_NURSERY_SIZE = 16] in [gc_stack.c]): the collector exits.
    - An allocating primitive: the emitter registers no roots around the call.
    Both functions return the allocation chunk of the expression as well, so
    that each is linear in the size of the program. *)
Definition max_chunk : N := 65536.

Definition tag_okb (cenv : ctor_env) (t : ctor_tag) : bool :=
  match M.get t cenv with
  | Some _ => N.ltb (ord_of cenv t) 251 && N.ltb (arity_of cenv t) (N.pow 2 54)
  | None => false
  end.

Definition is_int_val (p : AstCommon.primitive_value) : bool :=
  match projT1 p with AstCommon.primInt => true | _ => false end.

Definition constr_chunk (ys : list var) (c : N) : N :=
  match ys with
  | [] => c
  | _ => (1 + N.of_nat (List.length ys) + c)%N
  end.

Fixpoint fragment (cenv : ctor_env) (e : exp) : bool * N :=
  match e with
  | Econstr _ t ys e' =>
      let r := fragment cenv e' in
      let c := constr_chunk ys (snd r) in
      (fst r && tag_okb cenv t && N.eqb (arity_of cenv t) (N.of_nat (List.length ys))
       && N.leb c max_chunk, c)
  | Ecase _ bs =>
      ((fix go (bs : list (ctor_tag * exp)) : bool :=
          match bs with
          | [] => true
          | (t, e') :: bs' => tag_okb cenv t && fst (fragment cenv e') && go bs'
          end) bs, 0%N)
  | Eproj _ t n _ e' =>
      let r := fragment cenv e' in (N.ltb n (arity_of cenv t) && fst r, snd r)
  | Eletapp _ _ _ _ e' => (fst (fragment cenv e'), 0%N)
  | Efun _ e' => (false, snd (fragment cenv e'))
  | Eapp _ _ _ => (true, 0%N)
  | Eprim_val _ p e' =>
      let r := fragment cenv e' in (is_int_val p && fst r, snd r)
  | Eprim _ _ _ e' => (false, 0%N)
  | Ehalt _ => (true, 0%N)
  end.

Fixpoint buildable (cenv : ctor_env) (allocating : prim -> bool) (e : exp) : bool * N :=
  match e with
  | Econstr _ t ys e' =>
      let r := buildable cenv allocating e' in
      let c := constr_chunk ys (snd r) in
      (fst r && N.leb c max_chunk
       && match ys with [] => true | _ => N.ltb (ord_of cenv t) 251 end, c)
  | Ecase _ bs =>
      ((fix go (bs : list (ctor_tag * exp)) : bool :=
          match bs with
          | [] => true
          | (_, e') :: bs' => fst (buildable cenv allocating e') && go bs'
          end) bs, 0%N)
  | Eproj _ _ _ _ e' => buildable cenv allocating e'
  | Eletapp _ _ _ _ e' => (fst (buildable cenv allocating e'), 0%N)
  | Efun _ e' => buildable cenv allocating e'
  | Eapp _ _ _ => (true, 0%N)
  | Eprim_val _ _ e' => buildable cenv allocating e'
  | Eprim _ p _ e' => (negb (allocating p) && fst (buildable cenv allocating e'), 0%N)
  | Ehalt _ => (true, 0%N)
  end.

Fixpoint fundefs_all (f : exp -> bool) (fds : fundefs) : bool :=
  match fds with
  | Fcons _ _ _ e fds' => f e && fundefs_all f fds'
  | Fnil => true
  end.

(** Quadratic in the number of constructors of the program. *)
Definition cenv_pair_okb (p q : ctor_tag * ctor_ty_info) : bool :=
  Pos.eqb (fst p) (fst q)
  || negb (Pos.eqb (ctor_ind_tag (snd p)) (ctor_ind_tag (snd q)))
  || negb (N.eqb (ctor_ordinal (snd p)) (ctor_ordinal (snd q)))
  || Bool.eqb (N.eqb (ctor_arity (snd p)) 0) (negb (N.eqb (ctor_arity (snd q)) 0)).

Definition cenv_okb (cenv : ctor_env) : bool :=
  let l := M.elements cenv in
  forallb (fun p => forallb (cenv_pair_okb p) l) l.

(** [compile_prog] treats a program without an outer [Efun] as a main body. *)
Definition prog_parts (e : exp) : fundefs * exp :=
  match e with
  | Efun fds main => (fds, main)
  | _ => (Fnil, e)
  end.

Definition llvm_fragmentb (cenv : ctor_env) (e : exp) : bool :=
  let '(fds, main) := prog_parts e in
  fundefs_all (fun b => fst (fragment cenv b)) fds && fst (fragment cenv main) && cenv_okb cenv.

Definition llvm_buildable (cenv : ctor_env) (allocating : prim -> bool) (e : exp) : bool :=
  let '(fds, main) := prog_parts e in
  fundefs_all (fun b => fst (buildable cenv allocating b)) fds
  && fst (buildable cenv allocating main).

