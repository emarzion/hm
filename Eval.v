Require Import List.

Import ListNotations.

Require Import HM.TypedLang.
Require Import HM.Util.Fin.
Require Import HM.Util.Vec.

Fixpoint eval_Ty{n}(t : Ty n) : Vec n Type -> Type :=
  match t with
  | var_Ty i => proj i
  | arrow_Ty t1 t2 => fun v => eval_Ty t1 v -> eval_Ty t2 v
  | prod_Ty t1 t2 => fun v => (eval_Ty t1 v * eval_Ty t2 v)%type
  | sum_Ty t1 t2 => fun v => (eval_Ty t1 v + eval_Ty t2 v)%type
  | list_Ty t => fun v => list (eval_Ty t v)
  | unit_Ty => fun _ => unit
  | bool_Ty => fun _ => bool
  | nat_Ty => fun _ => nat
  end.

Definition tupleize{n}(v : Vec n Type)(ts : list (Ty n)) : Type :=
  List.fold_right prod unit (List.map (fun t => eval_Ty t v) ts).

Fixpoint tup_proj{n}(v : Vec n Type)(ts : list (Ty n)) : forall i, tupleize v ts -> eval_Ty (Fin_lookup ts i) v :=
  match ts with
  | [] => fun e => match e with end
  | t :: ts' => fun i xs =>
    match i with
    | inl _ => fst xs
    | inr j => tup_proj v ts' j (snd xs)
    end
  end.

Definition apply_un{m n}(un : Vec m (Ty n))(v : Vec n Type) : Vec m Type :=
  vmap (fun t => eval_Ty t v) un.

Lemma eval_subst{m n}(un : Vec m (Ty n))(v : Vec n Type)(t : Ty m) : eval_Ty (Ty_subst t un) v = eval_Ty t (vmap
        (fun t' => eval_Ty t' v) un).
Proof.
  induction t; simpl; try reflexivity.
  - rewrite proj_vmap; reflexivity.
  - rewrite IHt1,IHt2; reflexivity.
  - rewrite IHt1,IHt2; reflexivity.
  - rewrite IHt1,IHt2; reflexivity.
  - rewrite IHt; reflexivity.
Defined.

Fixpoint apply_un_tup{m n}(un : Vec m (Ty n))(ts : list (Ty m))(v : Vec n Type){struct ts} : tupleize v (map (fun t' => Ty_subst t' un) ts) -> tupleize (apply_un un v) ts :=
  match ts with
  | [] => fun _ => tt
  | t::ts' => fun tup => 
    ((eq_rect _ (fun X => X) (fst tup) _ (eval_subst un v t)) ,
     apply_un_tup _ _ _ (snd tup))
  end.

Lemma eval_apply{m n}(un : Vec m (Ty n)){t}(v : Vec n Type) :
  eval_Ty t (apply_un un v) = eval_Ty (Ty_subst t un) v.
Proof.
  intros.
  induction t; simpl.
  - simpl.
    unfold apply_un.
    rewrite proj_vmap.
    reflexivity.
  - congruence.
  - rewrite IHt1.
    rewrite IHt2.
    reflexivity.
  - congruence.
  - rewrite IHt.
    reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Defined.

Definition eval_apply_transport{m n}(un : Vec m (Ty n)){t}(v : Vec n Type) :
  eval_Ty t (apply_un un v) -> eval_Ty (Ty_subst t un) v :=
  @eq_rect Type (eval_Ty t (apply_un un v)) (fun X => eval_Ty t (apply_un un v) -> X) (fun x => x) _ (eval_apply un v).

Fixpoint eval_Exp{n}{ts : list (Ty n)}{t}(e : Exp ts t){struct e} : forall (v : Vec n Type),
  tupleize v ts -> eval_Ty t v :=
  match e in (@Exp n' ts' t') return
    forall (e' : Exp ts' t'), e = e' -> forall (v : Vec n' Type),
           tupleize v ts' -> eval_Ty t' v  with
  | Var _ i => fun _ _ v => tup_proj v _ i
  | Lam ts t1 t2 e0 => fun _ _ v tup => fun x => eval_Exp e0 v (x,tup)
  | App ts t1 t2 e1 e2 => fun _ _ v tup => eval_Exp e1 v tup (eval_Exp e2 v tup)
  | Let ts t1 t2 e1 e2 => fun _ _ v tup =>
      let x := eval_Exp e1 v tup in eval_Exp e2 v (x,tup)
  | Pair ts t1 t2 e1 e2 => fun _ _ v tup => (eval_Exp e1 v tup, eval_Exp e2 v tup)
  | Prod_Iter ts t1 t2 t3 e1 e2 => fun _ _ v tup =>
      match eval_Exp e1 v tup with
      | (x,y) => eval_Exp e2 v (y,(x,tup))
      end
  | Inl ts t1 t2 e0 => fun _ _ v tup => inl (eval_Exp e0 v tup)
  | Inr ts t1 t2 e0 => fun _ _ v tup => inr (eval_Exp e0 v tup)
  | Sum_Iter ts t1 t2 t3 e1 e2 e3 => fun _ _ v tup =>
      match eval_Exp e1 v tup with
      | inl x => eval_Exp e2 v (x,tup)
      | inr y => eval_Exp e3 v (y,tup)
      end
  | Nil ts t => fun _ _ v tup => []
  | Cons ts t e1 e2 => fun _ _ v tup => eval_Exp e1 v tup :: eval_Exp e2 v tup
  | List_Iter ts t1 t2 e1 e2 e3 => fun _ _ v tup =>
      List.fold_right (fun x y => eval_Exp e3 v (y,(x,tup))) (eval_Exp e2 v tup) (eval_Exp e1 v tup)
  | Tt ts => fun _ _ _ _ => tt
  | Unit_Iter ts t e1 e2 => fun _ _ v tup =>
      match eval_Exp e1 v tup with
      | tt => eval_Exp e2 v tup
      end
  | EFalse ts => fun _ _ _ _ => false
  | ETrue ts => fun _ _ _ _ => true
  | Bool_Iter ts t e1 e2 e3 => fun _ _ v tup =>
      match eval_Exp e1 v tup with
      | false => eval_Exp e2 v tup
      | true => eval_Exp e3 v tup
      end
  | Zero ts => fun _ _ _ _ => O
  | Succ ts e0 => fun _ _ v tup => S (eval_Exp e0 v tup)
  | Nat_Iter ts t e1 e2 e3 => fun _ _ v tup =>
      Nat.iter (eval_Exp e1 v tup) (fun x => eval_Exp e3 v (x,tup)) (eval_Exp e2 v tup)
  | Specialize ts t un e0 => fun _ _ v tup => eval_apply_transport _ _
      (eval_Exp e0 (apply_un un v) (apply_un_tup un _ v tup))
  end e eq_refl.

Definition eval_closed_Exp{n}{t}(e : Exp [] t)(v : Vec n Type) : eval_Ty t v :=
  eval_Exp e v tt.

Fixpoint univ_closure{n} : (Vec n Type -> Type) -> Type :=
  match n with
  | 0 => fun F => F tt
  | S m => fun F => forall X, univ_closure (fun v => F (X,v))
  end.

Definition fully_eval_Ty{n} : Ty n -> Type :=
  fun t => univ_closure (eval_Ty t).

Fixpoint univ_closed_eval{n} : forall (F : Vec n Type -> Type), (forall v, F v) ->
  univ_closure F :=
  match n with
  | 0 => fun F eval => eval tt
  | S m => fun F eval => fun X => univ_closed_eval (fun v => F (X,v)) (fun v => eval (X,v))
  end.

Definition fully_eval_closed_Exp{n}{t : Ty n}(e : Exp [] t) : fully_eval_Ty t :=
  univ_closed_eval _ (fun v => eval_closed_Exp e v).

Section Tests.

Definition test_add{ts} : @Exp 0 ts (nat_Ty ~> nat_Ty ~> nat_Ty).
Proof.
  apply Lam.
  apply Lam.
  apply Nat_Iter.
  - exact (Var (_ :: _ :: _) (inr (inl tt))).
  - exact (Var (_ :: _ :: _) (inl tt)).
  - apply Succ.
    exact (Var (_ :: _ :: _ :: _) (inl tt)).
Defined.

Definition test_mult{ts} : @Exp 0 ts (nat_Ty ~> nat_Ty ~> nat_Ty).
Proof.
  apply Lam.
  apply Lam.
  apply Nat_Iter.
  - exact (Var (_ :: _ :: _) (inr (inl tt))).
  - exact (Zero _).
  - apply (App _ nat_Ty).
    + apply (App _ nat_Ty).
      * exact test_add.
      * exact (Var (_ :: _ :: _ :: _) (inr (inl tt))).
    + exact (Var (_ :: _ :: _ :: _) (inl tt)).
Defined.

Definition zero : Fin 2 :=  inl tt.
Definition one : Fin 2 := inr (inl tt).

Definition test_map{ts} : @Exp 2 ts ((var_Ty zero ~> var_Ty one) ~> list_Ty (var_Ty zero) ~> list_Ty (var_Ty one)).
Proof.
  apply Lam.
  apply Lam.
  eapply List_Iter.
  - exact (Var (_ :: _) (inl tt)).
  - apply Nil.
  - apply Cons.
    + eapply App.
      * exact (Var (_ :: _ :: _ :: _ ::  _) (inr (inr (inr (inl tt))))).
      * exact (Var (_ :: _ :: _) (inr (inl tt))).
    + exact (Var (_ :: _) (inl tt)).
Defined.

End Tests.