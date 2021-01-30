Require Import HM.Util.Fin.

Fixpoint Vec n X : Type :=
  match n with
  | 0 => unit
  | S m => X * Vec m X
  end.

Fixpoint proj{X n} : Fin n -> Vec n X -> X :=
  match n with
  | 0 => fun e => match e with end
  | S m => fun i v =>
    match i with
    | inl _ => fst v
    | inr j => proj j (snd v)
    end
  end.

Fixpoint vmap{X Y n}(f : X -> Y) : Vec n X -> Vec n Y :=
  match n with
  | 0 => fun _ => tt
  | S m => fun v => (f (fst v), vmap f (snd v))
  end.

Lemma proj_vmap{X Y n}(f : X -> Y) : forall (v : Vec n X)(i : Fin n),
  proj i (vmap f v) = f (proj i v).
Proof.
  induction n; simpl; intros.
  - destruct i.
  - destruct i as [[]|j].
    + reflexivity.
    + apply IHn.
Defined.
