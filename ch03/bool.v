(* Set Implicit Arguments. *)

Inductive term : Set :=
  | tm_true : term
  | tm_false : term
  | tm_if : term -> term -> term -> term.

Reserved Notation "t --> t'" (at level 50).

Inductive s_step : term -> term -> Prop :=
  | E_IfTrue : forall t2 t3, tm_if tm_true t2 t3 --> t2
  | E_IfFalse : forall t2 t3, tm_if tm_false t2 t3 --> t3
  | E_If : forall t1 t1' t2 t3, t1 --> t1' -> tm_if t1 t2 t3 --> tm_if t1' t2 t3
  where "t --> t'" := (s_step t t').

Definition s : term := tm_if tm_true tm_false tm_false.
Definition t : term := tm_if s tm_true tm_true.
Definition u : term := tm_if tm_false tm_true tm_true.

Example p36_ex_step :
  tm_if t tm_false tm_false --> tm_if u tm_false tm_false.
Proof.
  apply E_If. 
  apply E_If.
  apply E_IfTrue.
Qed.

Theorem theo3_5_4 :
  forall t t' t'' : term, t --> t' /\ t --> t'' -> t' = t''.
Proof.
  intros t t' t'' H1.
  destruct H1 as [e1 e2].

  generalize dependent t''.
  induction e1.

  (* E_IfTrue *)
  intros. inversion e2. reflexivity. inversion H3.
  (* E_IfFalse *)
  intros. inversion e2. reflexivity. inversion H3.
  (* E_If *)
  intros. inversion e2.
    rewrite <- H0 in e1. inversion e1.
    rewrite <- H0 in e1. inversion e1.
    rewrite (IHe1 t1'0 H3). reflexivity.
Qed.
