Require Import Coq.Numbers.BinNums.
Require Import Coq.Lists.List.
Open Scope list_scope.

Inductive value : Type -> Type :=
| VInt : Z -> value Z
| VList : forall a, list (value a) -> value (list a)
.

Implicit Arguments VList [a].

Inductive trace : Type :=
| TConst : forall a, value a -> trace
| TSingleton : trace -> trace
| TUnion : trace -> trace -> trace                         
.

Inductive expr : Type -> Type :=
| EConst : forall a, value a -> expr a
| ESingleton : forall a, expr a -> expr (list a)
| EUnion : forall a, expr (list a) -> expr (list a) -> expr (list a)
.

Implicit Arguments EConst [a].
Implicit Arguments ESingleton [a].
Implicit Arguments EUnion [a].

Fixpoint un_value {a : Type} (v : value a) : a :=
  match v with
  | VInt i => i
  | VList l => map un_value l
  end.

(* Fixpoint un_vlist {a : Type} (v : value (list a)) : list (value a) := *)
(*   match v return list (value a) with *)
(*   | VInt _ => nil (* This can't happen... *) *)
(*   | VList l => l *)
(*   end. *)

Fixpoint eval {a : Type} (e : expr a) : value a :=
  match e with
  | EConst v => v
  | ESingleton e => VList (eval e :: nil)
  | EUnion e1 e2 =>
    let l1 := un_value (eval e1) in
    let l2 := un_value (eval e2) in
    VList (l1 ++ l2)
  end.

Fixpoint tracedEval (e : expr) : trace :=
  match e with
  | EConst v => TConst v
  | ESingleton e => TSingleton (tracedEval e)
  end.
