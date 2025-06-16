From stdpp Require Import listset.

Definition char : Type := nat.

Definition charset : Type := listset char.

Definition charset_delete (C : charset) (c : char) : charset :=
  let l := listset_car C in
  {| listset_car := filter (λ x, x ≠ c) l |}.

Notation "C #- c" := (charset_delete C c) (at level 60).

Lemma elem_of_charset_delete c C c' :
  c ∈ C →
  c ≠ c' →
  c ∈ C #- c'.
Proof.
  intros. by apply elem_of_list_filter.
Qed.

(** * Strings *)

Definition str : Type := list char.

Definition ε : str := [].

Local Open Scope Z_scope.

(** Char at: the singleton string containing a character at the given position;
    or empty string when position is out of range. *)
Definition str_at (s : str) (i : Z) : str :=
  if bool_decide (0 ≤ i) then
    match s !! (Z.to_nat i) with
    | Some c => [c]
    | None => ε
    end
  else ε.

Coercion Z.of_nat : nat >-> Z.

Lemma str_at_in_range s i :
  0 ≤ i < length s →
  ∃ c, s !! (Z.to_nat i) = Some c ∧ str_at s i = [c].
Proof.
  intros ?.
  assert (Z.to_nat i < length s)%nat as Hi by lia.
  apply lookup_lt_is_Some in Hi as [c Hc].
  exists c; split; [done|].
  unfold str_at. rewrite bool_decide_true by lia.
  by setoid_rewrite Hc.
Qed.

Lemma str_at_out_of_range s i :
  ¬ 0 ≤ i < length s →
  str_at s i = ε.
Proof.
  intros ?.
  unfold str_at. case_bool_decide; [|done].
  assert (length s ≤ Z.to_nat i)%nat as Hi by lia.
  apply lookup_ge_None in Hi. by setoid_rewrite Hi.
Qed.

Definition str_substr_begin (s : str) (i : Z) : str :=
  if bool_decide (0 ≤ i < length s) then drop (Z.to_nat i) s else ε.

Definition str_substr_until (s : str) (j : Z) : str :=
  take (Z.to_nat j) s.

(* Substring: evaluates to the longest substring of `s` of length at most `j - i` starting at `i`.
   It evaluates to the empty string if `j - i` is negative or `i` is out of range. *)
Definition str_substr (s : str) (i j : Z) : str :=
  str_substr_until (str_substr_begin s i) (j - i).

Fixpoint str_find (s : str) (c : char) : option nat :=
  match s with
  | [] => None
  | c' :: s' => if bool_decide (c' = c) then Some O else S <$> (str_find s' c)
  end.

Lemma str_find_None s c :
  str_find s c = None → c ∉ s.
Proof.
  induction s as [|c' s']; simpl.
  - intros. apply not_elem_of_nil.
  - case_bool_decide; [inversion 1|].
    rewrite fmap_None. intros. apply not_elem_of_cons. auto.
Qed.

Lemma str_find_Some s c i :
  str_find s c = Some i →
  s !! i = Some c ∧ c ∉ (take i s).
Proof.
  revert i. induction s as [|c' s'] => i; simpl; [inversion 1|].
  case_bool_decide.
  - inversion 1. subst. simpl. split; [done | apply not_elem_of_nil].
  - rewrite fmap_Some. intros [j [? ->]].
    setoid_rewrite lookup_cons. rewrite firstn_cons, not_elem_of_cons. naive_solver.
Qed.

(** Index of the first occurrence of `c` in `s`. Otherwise, it is -1. *)
Definition str_index_of (s : str) (c : char) : Z :=
  match str_find s c with
  | Some n => Z.of_nat n
  | None => -1
  end.

Lemma str_index_of_ge_0 s c :
  let i := str_index_of s c in
  0 ≤ i → str_find s c = Some (Z.to_nat i).
Proof.
  unfold str_index_of. destruct (str_find s c); [|lia].
  intros. f_equal. lia.
Qed.

Lemma str_index_of_lt_0 s c :
  str_index_of s c < 0 → str_find s c = None.
Proof.
  unfold str_index_of. destruct (str_find s c); [lia|done].
Qed.