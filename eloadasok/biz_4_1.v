Require Import Arith.

Inductive Ari : Set :=
  | zero : Ari
  | succ : Ari -> Ari.


Fixpoint addA (n m : Ari) {struct n} : Ari :=
match n with
  | zero => m
  | succ n' => succ (addA n' m)
  end
.

Fixpoint Ari_eq (n m : Ari) : Prop :=
  match n, m with
  | zero, zero => True
  | succ n', succ m' => Ari_eq n' m'
  | _, _ => False
  end.

Lemma Ari_eq_then_eq : forall (n m : Ari), Ari_eq n m -> n = m.
Proof.
   induction n; destruct m; intro H; try inversion H; auto.
  rewrite (IHn m H). reflexivity.
Qed.












