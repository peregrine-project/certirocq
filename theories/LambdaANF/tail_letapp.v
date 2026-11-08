From Stdlib Require Import Lists.List PArith.BinPos.
Require Import LambdaANF.term.

(** In direct style, [Eletapp x f ft ys (Ehalt x)] calls [f] and returns its result:
    it is the tail call [Eapp f ft ys].  The conversion from λ□ produces this shape for
    every [match] ([Efun f_case [s] (Ecase s ..)] followed by such a call), and [shrink]
    inlines a function used once only when the use is a tail call.  This pass turns the
    shape into a tail call, so that [shrink] then inlines [f_case] again. *)

Fixpoint tail_letapp (e : exp) : exp :=
  match e with
  | Econstr x c ys k => Econstr x c ys (tail_letapp k)
  | Ecase x bs => Ecase x (List.map (fun b => (fst b, tail_letapp (snd b))) bs)
  | Eproj x c n y k => Eproj x c n y (tail_letapp k)
  | Eletapp x f ft ys (Ehalt x') =>
    if Pos.eqb x x' then Eapp f ft ys else Eletapp x f ft ys (Ehalt x')
  | Eletapp x f ft ys k => Eletapp x f ft ys (tail_letapp k)
  | Efun fds k => Efun (tail_letapp_fds fds) (tail_letapp k)
  | Eapp f ft ys => Eapp f ft ys
  | Eprim_val x p k => Eprim_val x p (tail_letapp k)
  | Eprim x p ys k => Eprim x p ys (tail_letapp k)
  | Ehalt x => Ehalt x
  end
with tail_letapp_fds (fds : fundefs) : fundefs :=
  match fds with
  | Fcons f ft xs e fds' => Fcons f ft xs (tail_letapp e) (tail_letapp_fds fds')
  | Fnil => Fnil
  end.
