Require Import Lia.
Require Import List.
Require Import PeanoNat.

Import ListNotations.

Fixpoint Fin n : Type :=
  match n with
  | 0 => Empty_set
  | S m => unit + Fin m
  end.

Fixpoint Fin_lookup{X}(xs : list X) : Fin (length xs) -> X :=
  match xs with
  | [] => fun e =>
    match e with
    end
  | x :: ys => fun i =>
    match i with
    | inl _ => x
    | inr j => Fin_lookup ys j
    end
  end.

Fixpoint Fin_map_transport{X Y}(f : X -> Y)(xs : list X) : Fin (length xs) -> Fin (length (map f xs)) :=
  match xs with
  | [] => fun e => match e with end
  | _ :: ys => fun i =>
    match i with
    | inl _ => inl tt
    | inr j => inr (Fin_map_transport f ys j)
    end
  end.

Lemma map_lookup{X Y} : forall (f : X -> Y)(xs : list X)(i : Fin (length xs)), Fin_lookup (map f xs) (Fin_map_transport f xs i) = f (Fin_lookup xs i).
Proof.
  intro f.
  induction xs.
  - intros [].
  - intros [[]|j].
    + reflexivity.
    + apply IHxs.
Defined.
