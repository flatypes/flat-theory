From stdpp Require Import numbers.

Inductive inf_nat : Type :=
  | fin : nat → inf_nat
  | inf : inf_nat
  .

Coercion fin : nat >-> inf_nat.

Definition inf_nat_add (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m + n
  | _, _ => inf
  end.

Definition inf_nat_sub (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m - n
  | inf, _ => inf
  | _, inf => 0
  end.

Definition inf_nat_le (a b : inf_nat) : Prop :=
  match a, b with
  | fin m, fin n => m ≤ n
  | inf, fin _ => False
  | fin _, inf => True
  | inf, inf => True
  end.

Definition inf_nat_min (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m `min` n
  | inf, fin n => n
  | fin n, inf => n
  | _, _ => inf
  end.

Definition inf_nat_max (a b : inf_nat) : inf_nat :=
  match a, b with
  | fin m, fin n => m `max` n
  | _, _ => inf
  end.

Declare Scope inf_nat_scope.
Infix "+" := inf_nat_add : inf_nat_scope.
Infix "-" := inf_nat_sub : inf_nat_scope.
Infix "≤" := inf_nat_le : inf_nat_scope.
Notation "a ≤ b ≤ c" := (inf_nat_le a b ∧ inf_nat_le b c) : inf_nat_scope.
Infix "`min`" := inf_nat_min (at level 35) : inf_nat_scope.
Infix "`max`" := inf_nat_max (at level 35) : inf_nat_scope.

Section inf_nat_properties.

  Local Open Scope inf_nat_scope.

  Set Printing Coercions.

  (* Global Instance inf_nat_le_refl : Reflexive inf_nat_le. *)
  (* Proof. *)
    (* intros a. destruct a; simpl; [lia|done]. *)
  (* Qed. *)

  Lemma inf_nat_min_le a b x :
    a `min` b ≤ x → (a ≤ x ∧ a ≤ b) ∨ (b ≤ x ∧ b ≤ a).
  Admitted.

  Lemma inf_nat_max_ge a b x :
    x ≤ a `max` b → x ≤ a ∨ x ≤ b.
  Admitted.

End inf_nat_properties.

Definition range : Type := (inf_nat * inf_nat).

Local Open Scope inf_nat_scope.

Global Instance range_empty : Empty range := (inf, fin 0).
Global Instance range_singleton : Singleton nat range := λ a, (fin a, fin a).
Global Instance elem_of_range : ElemOf nat range := λ a R, R.1 ≤ a ≤ R.2.
Global Instance range_join : Join range := λ Q R, (Q.1 `min` R.1, Q.2 `max` R.2).

Definition range_add (Q R : range) : range := (Q.1 + R.1, Q.2 + R.2).
Definition range_sub (Q R : range) : range := (Q.1 - R.2, Q.2 - R.1).

Declare Scope range_scope.
Infix "+" := range_add : range_scope.
Infix "-" := range_sub : range_scope.

Section range_lemmas.

  Local Open Scope range_scope.

  Implicit Type (m n : nat) (Q R : range).

  Lemma elem_of_range_add m n Q R :
    m ∈ Q →
    n ∈ R →
    (m + n)%nat ∈ Q + R.
  Proof.
    destruct Q as [a b]. destruct R as [c d]. intros [??] [??].
    split; destruct a, b, c, d; simpl in *; lia.
  Qed.

  Lemma elem_of_range_sub m n Q R :
    m ∈ Q →
    n ∈ R →
    (m - n)%nat ∈ Q - R.
  Proof.
    destruct Q as [a b]. destruct R as [c d]. intros [??] [??].
    split; destruct a, b, c, d; simpl in *; lia.
  Qed.

  Lemma elem_of_range_join n Q R :
    n ∈ Q ∨ n ∈ R →
    n ∈ Q ⊔ R.
  Proof.
    destruct Q as [a b]. destruct R as [c d].
    intros [[??]|[??]]; destruct a, b, c, d, n; split; simpl in *; lia.
  Qed.

  Definition range_is_singleton (R : range) : bool :=
    match R with
    | (fin m, fin n) => m =? n
    | _ => false
    end.

  Global Instance elem_of_range_dec (n : nat) (R : range) : Decision (n ∈ R).
  Admitted.

End range_lemmas.
