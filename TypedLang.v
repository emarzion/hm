Require Import List.
Import ListNotations.
Require Import Lia.

Require Import HM.Util.Fin.
Require Import HM.Util.Vec.

Inductive Ty : nat -> Type :=
  | var_Ty : forall {n}, Fin n -> Ty n
  | arrow_Ty : forall {n}, Ty n -> Ty n -> Ty n
  | prod_Ty : forall {n}, Ty n -> Ty n -> Ty n
  | sum_Ty : forall {n}, Ty n -> Ty n -> Ty n
  | list_Ty : forall {n}, Ty n -> Ty n
  | unit_Ty : forall {n}, Ty n
  | bool_Ty : forall {n}, Ty n
  | nat_Ty : forall {n}, Ty n.

Declare Scope ty_scope.

Infix "~>" := arrow_Ty (right associativity, at level 11) : ty_scope.
Infix ".*" := prod_Ty (right associativity, at level 9) : ty_scope.
Infix ".+" := sum_Ty (right associativity, at level 7) : ty_scope.

Open Scope ty_scope.

Fixpoint Ty_subst{m n}(t : Ty m) : Vec m (Ty n) -> Ty n :=
  match t with
  | var_Ty i => proj i
  | arrow_Ty t1 t2 => fun un =>
      arrow_Ty (Ty_subst t1 un) (Ty_subst t2 un)
  | prod_Ty t1 t2 => fun un =>
      prod_Ty (Ty_subst t1 un) (Ty_subst t2 un)
  | sum_Ty t1 t2 => fun un =>
      sum_Ty (Ty_subst t1 un) (Ty_subst t2 un)
  | list_Ty t' => fun un =>
      list_Ty (Ty_subst t' un)
  | unit_Ty => fun _ => unit_Ty
  | bool_Ty => fun _ => bool_Ty
  | nat_Ty => fun _ => nat_Ty
  end.

Inductive Exp : forall {n}, list (Ty n) -> Ty n -> Type :=
  | Var : forall {n}(ts : list (Ty n))(i : Fin (length ts)),
      Exp ts (Fin_lookup ts i)
  | Lam : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp (t1 :: ts) t2 -> Exp ts (t1 ~> t2)
  | App : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp ts (t1 ~> t2) -> Exp ts t1 -> Exp ts t2
  | Let : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp ts t1 -> Exp (t1::ts) t2 -> Exp ts t2
  | Pair : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp ts t1 -> Exp ts t2 -> Exp ts (t1 .* t2)
  | Prod_Iter : forall {n}(ts : list (Ty n))(t1 t2 t3 : Ty n),
      Exp ts (t1 .* t2) -> Exp (t2::t1::ts) t3 -> Exp ts t3
  | Inl : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp ts t1 -> Exp ts (t1 .+ t2)
  | Inr : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp ts t2 -> Exp ts (t1 .+ t2)
  | Sum_Iter : forall {n}(ts : list (Ty n))(t1 t2 t3 : Ty n),
      Exp ts (t1 .+ t2) -> Exp (t1::ts) t3 -> Exp (t2::ts) t3 -> Exp ts t3
  | Nil : forall {n}(ts : list (Ty n))(t : Ty n),
      Exp ts (list_Ty t)
  | Cons : forall {n}(ts : list (Ty n))(t : Ty n),
      Exp ts t -> Exp ts (list_Ty t) -> Exp ts (list_Ty t)
  | List_Iter : forall {n}(ts : list (Ty n))(t1 t2 : Ty n),
      Exp ts (list_Ty t1) -> Exp ts t2 -> Exp (t2::t1::ts) t2 -> Exp ts t2
  | Tt : forall {n}(ts : list (Ty n)),
      Exp ts unit_Ty
  | Unit_Iter : forall {n}(ts : list (Ty n))(t : Ty n),
      Exp ts unit_Ty -> Exp ts t -> Exp ts t
  | EFalse : forall {n}(ts : list (Ty n)),
      Exp ts bool_Ty
  | ETrue : forall {n}(ts : list (Ty n)),
      Exp ts bool_Ty
  | Bool_Iter : forall {n}(ts : list (Ty n))(t : Ty n),
      Exp ts bool_Ty -> Exp ts t -> Exp ts t -> Exp ts t
  | Zero : forall {n}(ts : list (Ty n)),
      Exp ts nat_Ty
  | Succ : forall {n}(ts : list (Ty n)),
      Exp ts nat_Ty -> Exp ts nat_Ty
  | Nat_Iter : forall {n}(ts : list (Ty n))(t : Ty n),
      Exp ts nat_Ty -> Exp ts t -> Exp (t::ts) t -> Exp ts t
  | Specialize : forall {m n}(ts : list (Ty m))(t : Ty m)(un : Vec m (Ty n)),
      Exp ts t -> Exp (map (fun t' => Ty_subst t' un) ts) (Ty_subst t un).
