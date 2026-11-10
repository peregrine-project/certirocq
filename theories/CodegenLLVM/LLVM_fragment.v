(** * CodegenLLVM.LLVM_fragment: the programs the LLVM backend accepts

    The checks on a LambdaANF program that [toplevel.v] runs before the emitter.
    This file is separate from [toplevel.v] so that [LLVM_restricted_check.v] can
    state their soundness next to the correctness statement. *)

From Stdlib Require Import ZArith List Bool.
Require Import LambdaANF.term LambdaANF.identifiers LambdaANF.set_util.
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

(** ** Closedness and unique bindings

    [ub e s] walks [e] with the set [s] of binders seen so far, and fails on a
    repeated binder or a nested [Efun], which [fragment] excludes as well.  Each
    binder costs one set operation, so the check is [O(n log n)]. *)
Definition add_fresh (x : var) (s : PS.t) : option PS.t :=
  if PS.mem x s then None else Some (PS.add x s).

Fixpoint add_list (ys : list var) (s : PS.t) : option PS.t :=
  match ys with
  | [] => Some s
  | y :: ys' =>
      match add_fresh y s with
      | Some s1 => add_list ys' s1
      | None => None
      end
  end.

Fixpoint ub (e : exp) (s : PS.t) : option PS.t :=
  match e with
  | Econstr x _ _ e' | Eproj x _ _ _ e' | Eletapp x _ _ _ e'
  | Eprim_val x _ e' | Eprim x _ _ e' =>
      match add_fresh x s with
      | Some s1 => ub e' s1
      | None => None
      end
  | Ecase _ bs =>
      (fix go (bs : list (ctor_tag * exp)) (s : PS.t) : option PS.t :=
         match bs with
         | [] => Some s
         | (_, e') :: bs' =>
             match ub e' s with
             | Some s1 => go bs' s1
             | None => None
             end
         end) bs s
  | Efun _ _ => None
  | Eapp _ _ _ | Ehalt _ => Some s
  end.

Fixpoint ub_fundefs (fds : fundefs) (s : PS.t) : option PS.t :=
  match fds with
  | Fcons f _ ys e fds' =>
      match add_fresh f s with
      | None => None
      | Some s1 =>
          match add_list ys s1 with
          | None => None
          | Some s2 =>
              match ub e s2 with
              | None => None
              | Some s3 => ub_fundefs fds' s3
              end
          end
      end
  | Fnil => Some s
  end.

Definition llvm_uniqueb (fds : fundefs) (main : exp) : bool :=
  match ub_fundefs fds PS.empty with
  | Some s => match ub main s with Some _ => true | None => false end
  | None => false
  end.

Definition llvm_closedb (e : exp) : bool := PS.is_empty (exp_fv e).

Definition llvm_fragmentb (cenv : ctor_env) (e : exp) : bool :=
  let '(fds, main) := prog_parts e in
  fundefs_all (fun b => fst (fragment cenv b)) fds && fst (fragment cenv main) && cenv_okb cenv
  && llvm_closedb (Efun fds main) && llvm_uniqueb fds main.

Definition llvm_buildable (cenv : ctor_env) (allocating : prim -> bool) (e : exp) : bool :=
  let '(fds, main) := prog_parts e in
  fundefs_all (fun b => fst (buildable cenv allocating b)) fds
  && fst (buildable cenv allocating main).

