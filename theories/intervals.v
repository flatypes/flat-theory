From stdpp Require Import numbers.

(** * Natural Numbers with Infinity *)

Inductive inf_nat : Type :=
  | fin : nat → inf_nat
  | inf : inf_nat
  .
Coercion fin : nat >-> inf_nat.
Notation "∞" := inf.

Declare Scope inf_nat_scope.
Delimit Scope inf_nat_scope with inf_nat.

Definition inf_nat_le (a b : inf_nat) : Prop :=
  match a, b with
  | fin m, fin n => m ≤ n
  | inf, fin _ => False
  | _, _ => True
  end.
Infix "≤" := inf_nat_le : inf_nat_scope.

Global Instance inf_nat_le_dec a b : Decision ((a ≤ b)%inf_nat).
Proof.
  destruct a, b; simpl; [ apply le_dec | apply True_dec | apply False_dec | apply True_dec ].
Qed.

Definition inf_nat_min (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m `min` n
  | inf, fin _ => b
  | _, _ => a
  end.
Infix "`min`" := inf_nat_min : inf_nat_scope.

Definition inf_nat_max (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m `max` n
  | inf, fin _ => a
  | _, _ => b
  end.
Infix "`max`" := inf_nat_max : inf_nat_scope.

Definition inf_nat_plus (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m + n
  | _, _ => ∞
  end.
Infix "+" := inf_nat_plus : inf_nat_scope.

Definition inf_nat_minus (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m - n
  | inf, fin _ => ∞
  | _, _ => 0
  end.
Infix "-" := inf_nat_minus : inf_nat_scope.

Definition inf_nat_div (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m / n
  | inf, fin _ => ∞
  | _, _ => 0
  end.
Infix "/" := inf_nat_div : inf_nat_scope.

(** * Intervals *)

(** An interval encodes a subset of [nat] where the elements are in between (both inclusive)
    a lower and a upper bound that is potentially [∞]. *)
Inductive interval : Type :=
  | mk_interval : nat → inf_nat → interval.
Notation "a `to` b" := (mk_interval a b) (at level 35, no associativity).

Global Instance interval_empty : Empty interval := 1 `to` 0.
Global Instance interval_singleton : Singleton nat interval := λ n, n `to` n.
Global Instance elem_of_interval : ElemOf nat interval := λ n '(a `to` b), a ≤ n ∧ (n ≤ b)%inf_nat.
Global Instance interval_join : Join interval :=
  λ '(a1 `to` b1) '(a2 `to` b2), (a1 `min` a2) `to` (b1 `max` b2)%inf_nat.

Global Instance elem_of_interval_dec (n : nat) (I : interval) : Decision (n ∈ I).
Proof.
  destruct I as [a b]. by refine (cast_if (decide (a ≤ n ∧ (n ≤ b)%inf_nat))).
Qed.

Declare Scope interval_scope.
Delimit Scope interval_scope with interval.

Definition interval_plus (I J : interval) : interval := 
  let '(a1 `to` b1) := I in
  let '(a2 `to` b2) := J in
  (a1 + a2) `to` (b1 + b2)%inf_nat.
Infix "+" := interval_plus : interval_scope.

Definition interval_to_nat (I : interval) : option nat :=
  match I with
  | m `to` fin n => if bool_decide (m = n) then Some m else None
  | _ => None
  end.

Definition interval_minus_nat (I : interval) (n : nat) : interval :=
  let '(a `to` b) := I in
  (a - n) `to` (b - n)%inf_nat.
Infix "-ₙ" := interval_minus_nat (at level 50, left associativity) : interval_scope.

Definition nat_ceil_div (m n : nat) : nat :=
  if bool_decide (m `mod` n = 0) then m / n else m / n + 1.
Infix "`ceil_div`" := nat_ceil_div (at level 35, no associativity).

Definition interval_div_nat (I : interval) (n : nat) : interval :=
  let '(a `to` b) := I in
  (a `ceil_div` n) `to` (b / n)%inf_nat.
Infix "/ₙ" := interval_div_nat (at level 40, left associativity) : interval_scope.

Section interval_ops_properties.

  Implicit Type (I J : interval) (m n : nat).

  Lemma elem_of_interval_singleton m n :
    m ∈ interval_singleton n → m = n.
  Proof. cbv. lia. Qed.

  Lemma elem_of_interval_join n I J :
    n ∈ I ∨ n ∈ J →
    n ∈ I ⊔ J.
  Proof.
    destruct I as [? [?|]], J as [? [?|]]; intros [[??]|[??]].
    all: split; simpl in *; lia.
  Qed.

  Lemma elem_of_interval_plus m n I J :
    m ∈ I →
    n ∈ J →
    m + n ∈ (I + J)%interval.
  Proof.
    destruct I as [? [?|]], J as [? [?|]]; intros [??] [??].
    all: split; simpl in *; lia.
  Qed.

  Lemma interval_to_nat_spec I n m :
    interval_to_nat I = Some n →
    m ∈ I →
    m = n.
  Proof.
    unfold interval_to_nat. destruct I as [? [?|]]; [|done].
    case_bool_decide; [|done]. inv 1. intros [??]. simpl in *. lia.
  Qed.

  Lemma elem_of_interval_minus_nat m n I :
    m ∈ I →
    m - n ∈ (I -ₙ n)%interval.
  Proof.
    destruct I as [? [?|]]; intros [??].
    all: split; simpl in *; lia.
  Qed.

  Lemma nat_ceil_div_le_upper_bound m n k :
    m ≤ n * k →
    m `ceil_div` n ≤ k.
  Proof.
    intros H. unfold nat_ceil_div. case_bool_decide.
    - by apply Nat.Div0.div_le_upper_bound.
    - rewrite (Nat.div_mod_eq m n) in H. nia.
  Qed.

  Lemma elem_of_interval_div_nat n m I :
    n ≠ 0 →
    n * m ∈ I →
    m ∈ (I /ₙ n)%interval.
  Proof.
    destruct I as [? [?|]]; intros ? [??].
    all: split; simpl in *.
    - by apply nat_ceil_div_le_upper_bound.
    - by apply Nat.div_le_lower_bound.
    - by apply nat_ceil_div_le_upper_bound.
    - done.
  Qed.

End interval_ops_properties.
