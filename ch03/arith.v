Require Import Nat.
Require Import Arith.
Require Import List.
Require Import ListSet.
Import ListNotations.

Set Implicit Arguments.

Inductive term : Set :=
  | tm_true : term
  | tm_false : term
  | tm_if : term -> term -> term -> term
  | tm_zero : term
  | tm_succ : term -> term
  | tm_pred : term -> term
  | tm_iszero : term -> term.

Definition T := set term.

Definition term_eq : forall x y: term, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Module TermSetNotations.
Notation "{{ }}" := (empty_set term) (format "{{ }}").
Notation "{{ x }}" := (set_add term_eq x (empty_set term)).
Notation "{{ x ; y ; .. ; z }}" := (set_add term_eq x (set_add term_eq y .. (set_add term_eq z (empty_set term)) ..)).
End TermSetNotations.

Import TermSetNotations.

Definition maximum l :=
  match l with
  | nil     => 0 (* ??? *)
  | x :: xs => fold_left max xs x
  end.

Fixpoint consts (t: term) : T :=
  match t with
  | tm_true => {{tm_true}}
  | tm_false => {{tm_false}}
  | tm_zero => {{tm_zero}}
  | tm_succ t1 => consts t1
  | tm_pred t1 => consts t1
  | tm_iszero t1 => consts t1
  | tm_if t1 t2 t3 => set_union term_eq (set_union term_eq (consts t1) (consts t2)) (consts t3)
  end.

Fixpoint size (t : term) : nat :=
  match t with
    | tm_true => 1
    | tm_false => 1
    | tm_zero => 1
    | tm_succ t1 => size t1 + 1
    | tm_pred t1 => size t1 + 1
    | tm_iszero t1 => size t1 + 1
    | tm_if t1 t2 t3 => size t1 + size t2 + size t3 + 1
  end.

Fixpoint depth (t : term) : nat :=
  match t with
    | tm_true => 1
    | tm_false => 1
    | tm_zero => 1
    | tm_succ t1 => depth t1 + 1
    | tm_pred t1 => depth t1 + 1
    | tm_iszero t1 => depth t1 + 1
    | tm_if t1 t2 t3 => maximum [size t1; size t2; size t3] + 1
  end.

Lemma lemm3_3_3 :
  forall t : term, length (consts t) <= size t.
Proof.
  intro t.
  induction t; auto.
  2:{
    simpl. rewrite Nat.add_1_r. apply le_S. assumption.
  }
  2:{
    simpl. rewrite Nat.add_1_r. apply le_S. assumption.
  }
  2:{
    simpl. rewrite Nat.add_1_r. apply le_S. assumption.
  }
Abort.
