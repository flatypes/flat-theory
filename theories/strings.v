From stdpp Require Import listset.

(** * Unicode Characters *)

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

Definition str_take (i : Z) (s : str) : str := take (Z.to_nat i) s.

Definition str_drop (i : Z) (s : str) : str :=
  if bool_decide (0 ≤ i)%Z then drop (Z.to_nat i) s else [].

Definition str_substr (i j : Z) (s : str) : str := str_take (j - i) (str_drop i s).

Coercion Z.of_nat : nat >-> Z.

Lemma str_substr_alt i j s :
  str_substr i j s = str_drop i (str_take j s).
Proof.
  intros. unfold str_substr, str_take, str_drop. case_bool_decide; [|by rewrite take_nil].
  rewrite take_drop_commute. destruct (Z.le_gt_cases i j) as [?|?].
  - by replace (Z.to_nat i + Z.to_nat (j - i)) with (Z.to_nat j) by lia.
  - replace (Z.to_nat (j - i)) with 0 by lia. rewrite Nat.add_0_r.
    rewrite skipn_firstn_comm, Nat.sub_diag, take_0.
    symmetry. apply nil_length_inv. rewrite length_drop, length_take. lia.
Qed.

Lemma str_substr_nil i j s :
  (i < 0 ∨ j ≤ i)%Z → str_substr i j s = [].
Proof.
  intro. unfold str_substr, str_drop, str_take. case_bool_decide.
  - assert (Z.to_nat (j - i) = 0) as -> by lia. apply take_0.
  - apply take_nil.
Qed.

Fact str_substr_nil_cond_alt i j :
  ¬ (0 ≤ i < j)%Z ↔ (i < 0 ∨ j ≤ i)%Z.
Proof. lia. Qed.

(** Char at: the singleton string containing a character at the given position;
    or empty string when position is out of range. *)
Definition str_at (i : Z) (s : str) : str :=
  if bool_decide (0 ≤ i)%Z then
    match s !! (Z.to_nat i) with
    | Some c => [c] 
    | None => [] 
    end
  else [].

(* Lemma str_at_in_range s i :
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
*)

Definition str_index_of (c : char) (s : str) : Z :=
  match list_find (λ x, x = c) s with
  | Some (i, _) => i
  | None => -1
  end.

Lemma str_index_of_nonneg c s (i : nat) :
  str_index_of c s = i ↔ s !! i = Some c ∧ c ∉ take i s.
Proof.
  trans (list_find (λ x, x = c) s = Some (i, c)).
  + unfold str_index_of. case_match eqn:Heq.
    - case_match. apply list_find_Some in Heq. naive_solver.
    - split; [lia|done].
  + rewrite list_find_Some. apply and_iff_compat_l.
    rewrite elem_of_take. naive_solver.
Qed.

Lemma str_index_of_neg c s :
  str_index_of c s = (-1)%Z ↔ c ∉ s.
Proof.
  trans (list_find (λ x, x = c) s = None).
  + unfold str_index_of. case_match; [|done].
    case_match. split; [lia|congruence].
  + rewrite list_find_None, Forall_forall. naive_solver.
Qed.

Lemma str_index_of_take c s n :
  (str_index_of c s < n)%Z →
  str_index_of c (str_take n s) = str_index_of c s.
Admitted.

Lemma str_index_of_drop c s n :
  (0 ≤ str_index_of c s)%Z →
  str_index_of c (str_drop n s) = (str_index_of c s - n)%Z.
Admitted.

(* Lemma str_find_take s c i n :
  str_find s c = Some i →
  i < n →
  str_find (take n s) c = Some i.
Proof.
  rewrite !str_find_Some. intros [? Hp] ?. split.
  + by setoid_rewrite lookup_take.
  + by rewrite take_take, min_l by lia.
Qed.

Lemma str_find_drop s c i n :
  str_find s c = Some i →
  n ≤ i →
  str_find (drop n s) c = Some (i - n).
Proof.
  rewrite !str_find_Some. intros [? Hp] ?. split.
  + setoid_rewrite lookup_drop.
    by rewrite Nat.add_sub_assoc, Nat.add_sub' by done.
  + rewrite <-skipn_firstn_comm.
    rewrite <-(take_drop n (take i s)) in Hp. by apply not_elem_of_app in Hp as [_ ?].
Qed.
*)