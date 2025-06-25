From stdpp Require Import listset.

(** * Unicode Characters *)

Definition char : Type := nat.

Definition charset : Type := listset char.

Definition charset_is_singleton (C : charset) : option char :=
  match listset_car C with
  | [c] => Some c
  | _ => None
  end.

Lemma charset_is_singleton_Some C c :
  charset_is_singleton C = Some c → C ≡ {[ c ]}.
Admitted.

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

Coercion Z.of_nat : nat >-> Z.

Definition str : Type := list char.

Definition infix : relation str := λ t s, ∃ s1 s2, s = s1 ++ t ++ s2.

Infix "`infix_of`" := infix (at level 70).

Definition str_take (i : Z) (s : str) : str := take (Z.to_nat i) s.

Definition str_drop (i : Z) (s : str) : str :=
  if bool_decide (0 ≤ i)%Z then drop (Z.to_nat i) s else [].

Definition str_substr (i j : Z) (s : str) : str := str_take (j - i) (str_drop i s).

Definition str_at (i : Z) (s : str) : str := str_take 1 (str_drop i s).

Definition str_index_of (t : str) (s : str) : Z.
Admitted.

Fixpoint str_alphabet (s : str) : charset :=
  match s with
  | [] => ∅
  | c :: s' => {[ c ]} ∪ str_alphabet s'
  end.

Section string_properties.

  Lemma unfold_str_drop i s :
    (0 ≤ i)%Z →
    str_drop i s = drop (Z.to_nat i) s.
  Proof.
    intros. unfold str_drop. by rewrite bool_decide_true by lia.
  Qed.

  Lemma str_drop_neg i s :
    (i < 0)%Z →
    str_drop i s = [].
  Proof.
    intros. unfold str_drop. by rewrite bool_decide_false by lia.
  Qed.

  Lemma str_substr_take_drop i j s :
    (0 ≤ i)%Z →
    str_substr i j s = take (Z.to_nat (j - i)) (drop (Z.to_nat i) s).
  Proof.
    intros. unfold str_substr, str_take. by rewrite unfold_str_drop by lia.
  Qed.

  Lemma str_substr_drop_take i j s :
    (0 ≤ i ≤ j)%Z →
    str_substr i j s = drop (Z.to_nat i) (take (Z.to_nat j) s).
  Proof.
    intros. rewrite str_substr_take_drop, take_drop_commute by lia. do 2 f_equal. lia.
  Qed.

  (* str_at *)

  Lemma str_at_empty_iff i s :
    str_at i s = [] ↔ (i < 0 ∨ length s ≤ i)%Z.
  Admitted.

  Corollary str_at_empty i s :
    (i < 0 ∨ length s ≤ i)%Z → str_at i s = [].
  Proof. apply str_at_empty_iff. Qed.

  Lemma str_at_singleton_iff i s :
    (∃ c, str_at i s = [c]) ↔ (0 ≤ i < length s)%Z.
  Admitted.

  Lemma str_at_singleton_lt_length i s c :
    str_at i s = [c] → (0 ≤ i < length s)%Z.
  Proof. intros. apply str_at_singleton_iff. by exists c. Qed.

  Lemma str_at_lookup_None i s :
    (0 ≤ i)%Z →
    str_at i s = [] ↔ s !! (Z.to_nat i) = None.
  Proof.
  Admitted.

  Lemma str_at_lookup_Some i s c :
    (0 ≤ i)%Z →
    str_at i s = [c] ↔ s !! (Z.to_nat i) = Some c.
  Admitted.

  (* str_index_of *)

  Lemma str_index_of_neg t s :
    (str_index_of t s < 0)%Z ↔ ¬ (t `infix_of` s).
  Admitted.

  Lemma str_index_of_nonneg t s :
    (0 ≤ str_index_of t s)%Z ↔ t `infix_of` s.
  Admitted.

  Lemma str_index_of_nonneg_lt_length t s :
    (0 ≤ str_index_of t s)%Z → (str_index_of t s < length s)%Z.
  Admitted.

  Lemma str_index_of_eq i t s :
    (0 ≤ i)%Z →
    str_index_of t s = i ↔
    t `prefix_of` str_drop i s ∧ (∀ j, (0 ≤ j < i)%Z → ¬ (t `prefix_of` str_drop j s)).
  Admitted.

  Lemma str_index_of_char_eq i c s :
    (0 ≤ i)%Z →
    str_index_of [c] s = i ↔
    str_at i s = [c] ∧ c ∉ str_take i s.
  Admitted.

  (* Other properties *)
  
  Lemma str_at_singleton_inv i c c' :
    str_at i [c] = [c'] → i = 0 ∧ c = c'.
  Admitted.

  Lemma str_at_concat_inv i s1 s2 c :
    str_at i (s1 ++ s2) = [c] →
    ((0 ≤ i < length s1)%Z ∧ str_at i s1 = [c]) ∨
    ((length s1 < i < length s2)%Z ∧ str_at (i - length s1) s2 = [c]).
  Admitted.

  Lemma infix_app_l t s1 s2 :
    t `infix_of` s1 → t `infix_of` s1 ++ s2.
  Proof.
    intros [tl [tr ->]]. exists tl, (tr ++ s2). by simplify_list_eq.
  Qed.

  Lemma infix_app_r t s1 s2 :
    t `infix_of` s2 → t `infix_of` s1 ++ s2.
  Proof.
    intros [tl [tr ->]]. exists (s1 ++ tl), tr. by simplify_list_eq.
  Qed.

  Lemma str_take_nil i :
    str_take i [] = [].
  Proof.
    unfold str_take. apply take_nil.
  Qed.

  Lemma str_drop_nil i :
    str_drop i [] = [].
  Proof.
    unfold str_drop. case_bool_decide; [apply drop_nil | done].
  Qed.

  Lemma str_take_0 s :
    str_take 0 s = [].
  Proof.
    unfold str_take. apply take_0.
  Qed.

  Lemma str_drop_0 s :
    str_drop 0 s = s.
  Proof.
    unfold str_drop. rewrite bool_decide_true by lia. apply drop_0.
  Qed.

  Lemma str_take_neg i s :
    (i < 0)%Z →
    str_take i s = [].
  Proof.
    intros. unfold str_take. replace (Z.to_nat i) with 0%nat by lia. apply take_0.
  Qed.


  Lemma length_str_take i s :
    length (str_take i s) = Z.to_nat (i `min` length s).
  Proof.
    unfold str_take. rewrite length_take. lia.
  Qed.

  Lemma length_str_drop i s :
    length (str_drop i s) = if bool_decide (0 ≤ i)%Z then (Z.to_nat (length s - i)) else 0.
  Proof.
    unfold str_drop. case_bool_decide; [|done].
    rewrite length_drop. lia.
  Qed.

  Lemma str_take_app_l i s1 s2 :
    (i ≤ length s1)%Z →
    str_take i (s1 ++ s2) = str_take i s1.
  Proof.
    intros. unfold str_take. rewrite take_app.
    replace (Z.to_nat i - length s1) with 0 by lia.
    by rewrite take_0, app_nil_r.
  Qed.

  Lemma str_take_app_r i s1 s2 :
    (length s1 ≤ i)%Z →
    str_take i (s1 ++ s2) = s1 ++ str_take (i - length s1) s2.
  Proof.
    intros. unfold str_take. rewrite take_app, take_ge by lia.
    do 2 f_equal. lia.
  Qed.

  Lemma str_take_app i s1 s2 :
    str_take i (s1 ++ s2) = str_take i s1 ++ str_take (i - length s1) s2.
  Proof.
    unfold str_take. rewrite take_app. do 2 f_equal. lia.
  Qed.

  Lemma str_drop_app_l i s1 s2 :
    (0 ≤ i < length s1)%Z →
    str_drop i (s1 ++ s2) = str_drop i s1 ++ s2.
  Proof.
    intros. unfold str_drop. rewrite bool_decide_true by lia.
    rewrite drop_app. f_equal. replace (Z.to_nat i - length s1) with 0 by lia.
    apply drop_0.
  Qed.

  Lemma str_drop_app_r i s1 s2 :
    (length s1 ≤ i)%Z →
    str_drop i (s1 ++ s2) = str_drop (i - length s1) s2.
  Proof.
    intros. unfold str_drop. repeat case_bool_decide; try lia.
    rewrite drop_app. rewrite drop_ge by lia. rewrite app_nil_l.
    f_equal. lia.
  Qed.

  Lemma lookup_str_take (i : nat) k s :
    (i < k)%Z → (str_take k s) !! i = s !! i.
  Proof.
    intros. unfold str_take. setoid_rewrite lookup_take; [done|lia].
  Qed.

  Lemma lookup_str_drop (i : nat) k s :
    (0 ≤ k)%Z → (str_drop k s) !! i = s !! (Z.to_nat k + i).
  Proof.
    intros. unfold str_drop. rewrite bool_decide_true by lia.
    by setoid_rewrite lookup_drop.
  Qed.

  Lemma elem_of_str_take c k s :
    (0 < k)%Z →
    c ∈ str_take k s → ∃ i : nat, s !! i = Some c ∧ (i < k)%Z.
  Proof.
    unfold str_take. intros ? Hc. apply elem_of_take in Hc as [i [??]].
    exists i. split; [done|lia].
  Qed.

  Lemma str_take_take i j s :
    str_take i (str_take j s) = str_take (i `min` j) s.
  Proof.
    unfold str_take. rewrite take_take. f_equal. lia.
  Qed.

  Lemma str_drop_drop i j s :
    (0 ≤ i ∧ 0 ≤ j)%Z →
    str_drop i (str_drop j s) = str_drop (i + j) s.
  Proof.
    intros. unfold str_drop. rewrite !bool_decide_true by lia.
    rewrite drop_drop. f_equal. lia.
  Qed.

  Lemma str_take_take_drop i j s :
    (0 ≤ i ∧ 0 ≤ j)%Z →
    str_take i s ++ str_take j (str_drop i s) = str_take (i + j) s.
  Proof.
    intros. unfold str_take, str_drop. rewrite bool_decide_true by lia.
    rewrite take_take_drop. f_equal. lia.
  Qed.

  Lemma str_drop_take_drop i j s :
    (0 ≤ i ≤ j)%Z →
    str_drop i (str_take j s) ++ str_drop j s = str_drop i s.
  Proof.
    intros. unfold str_drop, str_take. rewrite !bool_decide_true by lia.
    by rewrite drop_take_drop by lia.
  Qed.

  Lemma str_take_drop_commute i j s :
    (0 ≤ i ∧ 0 ≤ j)%Z →
    str_take j (str_drop i s) = str_drop i (str_take (i + j) s).
  Proof.
    intros. unfold str_take, str_drop. rewrite bool_decide_true by lia.
    rewrite take_drop_commute. do 2 f_equal. lia.
  Qed. 

  Lemma reverse_str_drop_reverse s k :
    (0 ≤ k)%Z →
    reverse (str_drop k (reverse s)) = str_take (length s - k) s.
  Proof.
    intros. unfold str_drop, str_take. rewrite bool_decide_true by lia.
    rewrite drop_reverse, reverse_involutive. f_equal. lia.
  Qed.

  Lemma reverse_str_take_reverse s k :
    (0 ≤ k ≤ length s)%Z →
    reverse (str_take k (reverse s)) = str_drop (length s - k) s.
  Proof.
    intros. unfold str_drop, str_take. rewrite bool_decide_true by lia.
    rewrite take_reverse, reverse_involutive. f_equal. lia.
  Qed.

  Lemma prefix_str_take k s :
    str_take k s `prefix_of` s.
  Proof.
    unfold str_take. apply prefix_take.
  Qed.

  Lemma suffix_str_drop k s :
    str_drop k s `suffix_of` s.
  Proof.
    unfold str_drop. case_bool_decide; [apply suffix_drop | apply suffix_nil].
  Qed.

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

  Lemma str_index_of_nil s :
    str_index_of [] s = 0.
  Admitted.

  Lemma str_index_of_prefix t s :
    let i := str_index_of t s in
    (0 ≤ i)%Z → t `prefix_of` str_drop i s.
  Proof. Admitted.

  Lemma str_index_of_lt_not_prefix i t s :
    (0 ≤ i < str_index_of t s)%Z →
    ¬ (t `prefix_of` str_drop i s).
  Proof. Admitted.

  Lemma not_elem_of_prefix {A} (l l' : list A) x :
    x ∉ l → 
    l' `prefix_of` l →
    x ∉ l'.
  Proof.
    intros ? Hl' Hx. destruct Hl' as [? ->]. set_solver.
  Qed.

  Lemma not_elem_of_suffix {A} (l l' : list A) x :
    x ∉ l → 
    l' `suffix_of` l →
    x ∉ l'.
  Proof.
    intros ? Hl' Hx. destruct Hl' as [? ->]. set_solver.
  Qed.

  Lemma str_index_of_take t s i :
    (0 ≤ str_index_of t s ∧ str_index_of t s + length t ≤ i)%Z →
    str_index_of t (str_take i s) = str_index_of t s.
  Proof.
    intros. apply str_index_of_eq; [lia|]. split.
    * admit.
    * admit. 
    (* * rewrite lookup_str_take by lia. apply str_index_of_nonneg'. lia. *)
    (* * rewrite str_take_take, Z.min_l by lia. apply str_index_of_nonneg'. lia. *)
  Admitted.

  Lemma str_index_of_drop t s i :
    (0 ≤ i ≤ str_index_of t s)%Z →
    str_index_of t (str_drop i s) = (str_index_of t s - i)%Z.
  Proof.
    intros. apply str_index_of_eq; [lia|]. split.
    * rewrite str_drop_drop, Z.sub_add by lia. apply str_index_of_eq; [lia|done].
    * intros j ?. rewrite str_drop_drop by lia. apply str_index_of_lt_not_prefix. lia.
  Qed.

  Lemma elem_of_str_alphabet c s :
    c ∈ str_alphabet s ↔ c ∈ s.
  Proof.
    induction s; set_solver.
  Qed.

End string_properties.