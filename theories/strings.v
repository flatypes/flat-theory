From stdpp Require Import listset.

(** * Characters & Character Sets *)

(** A (Unicode) character is represented by its _code point_. *)
Definition char : Type := nat.

(** A character set is a finite set of characters. *)
Definition charset : Type := listset char.

Definition charset_is_singleton (C : charset) : option char :=
  match listset_car C with
  | [c] => Some c
  | _ => None
  end.

Lemma charset_is_singleton_Some C c :
  charset_is_singleton C = Some c → C ≡ {[ c ]}.
Admitted.

Global Instance charset_equiv_singleton_dec (C : charset) σ : Decision (C ≡ {[σ]}).
Admitted.

(** * Strings & String Operations *)

(** A string is a list of characters. *)
Definition str : Type := list char.

Definition char_to_str (σ : char) : str := [σ].
Coercion char_to_str : char >-> str.

(** The following basic string operations are simply list operations:
  - concat: [app] (notation [_ ++ _])
  - reverse: [reverse]
  - length: [length]
 *)

Local Open Scope Z_scope.
Coercion Z.of_nat : nat >-> Z.

(** Auxiliary definitions for string take and drop, by list [take] and [drop]. *)
Definition str_take (s : str) (n : Z) : str := take (Z.to_nat n) s.
Definition str_drop (s : str) (n : Z) : str :=
  if bool_decide (0 ≤ n) then drop (Z.to_nat n) s else [].

(** The substring operation is also defined in terms of [str_take] and [str_drop]. *)
Definition substr (s : str) (i j : Z) : str := str_take (str_drop s i) (j - i).
Notation "s [ i : j ]" := (substr s i j) (at level 2, i at level 50, j at level 50,
  left associativity, format "s [ i : j ]").

Lemma str_take_substr s n :
  str_take s n = s[0:n].
Proof.
  unfold substr, str_take, str_drop.
  rewrite bool_decide_true, drop_0 by lia. f_equal. lia.
Qed.

Lemma str_drop_substr s n :
  str_drop s n = s[n : length s].
Proof.
  unfold substr, str_take, str_drop. case_bool_decide.
  - rewrite take_ge; [done|]. rewrite length_drop. lia.
  - by rewrite take_nil.
Qed.

Notation "s [ : n ]" := (str_take s n) (at level 2, n at level 50, left associativity,
  format "s [ : n ]").
Notation "s [ n : ]" := (str_drop s n) (at level 2, n at level 50, left associativity,
  format "s [ n : ]").

(** The char-at operation is defined in terms of [str_take] and [str_drop]. *)
Definition char_at (s : str) (i : Z) : str := str_take (str_drop s i) 1.
Notation "s [ i ]" := (char_at s i) (at level 2, i at level 50, no associativity, format "s [ i ]").

Ltac unfold_substr :=
  unfold substr, char_at, str_take, str_drop in *; repeat (rewrite bool_decide_true by lia).

(** The prefix and suffix operations are defined by list relations 
    [`prefix_of`] and [`suffix_of`]. *)
Definition str_prefix (t s : str) : bool := bool_decide (t `prefix_of` s).
Definition str_suffix (t s : str) : bool := bool_decide (t `suffix_of` s).
Infix "⊑" := str_prefix (at level 70, no associativity).
Infix "⊒" := str_suffix (at level 70, no associativity).

(** The find operation is defined by [list_find]. *)
Definition find (s t : str) : Z :=
  match list_find (λ k : nat, t ⊑ s[k:]) (seq 0 (length s)) with
  | Some (k, _) => k
  | None => -1
  end.

(** The infix operation (a.k.a. contains) is defined in terms of [find]. *)
Definition str_infix (t s : str) : bool := bool_decide (0 ≤ find s t).
Infix "`in`" := str_infix (at level 70, no associativity).

(** Fixpoint str_alphabet (s : str) : charset :=
  match s with
  | [] => ∅
  | c :: s' => {[ c ]} ∪ str_alphabet s'
  end. **)

Section str_ops_properties.

  Implicit Type (s t : str) (σ : char).

  Lemma str_take_app_l i s1 s2 :
    i ≤ length s1 →
    (s1 ++ s2)[:i] = s1[:i].
  Proof.
    intros. unfold str_take. rewrite take_app.
    replace (Z.to_nat i - length s1)%nat with 0%nat by lia.
    by rewrite take_0, app_nil_r.
  Qed.

  Lemma str_take_app_r i s1 s2 :
    length s1 ≤ i →
    (s1 ++ s2)[:i] = s1 ++ s2[:i - length s1].
  Proof.
    intros. unfold str_take. rewrite take_app, take_ge by lia.
    do 2 f_equal. lia.
  Qed.

  Lemma str_drop_app_l i s1 s2 :
    0 ≤ i < length s1 →
    (s1 ++ s2)[i:] = s1[i:] ++ s2.
  Proof.
    intros. unfold str_drop. rewrite bool_decide_true by lia.
    rewrite drop_app. f_equal. replace (Z.to_nat i - length s1)%nat with 0%nat by lia.
    apply drop_0.
  Qed.

  Lemma str_drop_app_r i s1 s2 :
    length s1 ≤ i →
    (s1 ++ s2)[i:] = s2[i - length s1:].
  Proof.
    intros. unfold str_drop. repeat case_bool_decide; try lia.
    rewrite drop_app. rewrite drop_ge by lia. rewrite app_nil_l.
    f_equal. lia.
  Qed.

  Lemma substr_alt s i j :
    s[i:j] = s[:j][i:].
  Proof.
    intros. unfold substr, str_take, str_drop. case_bool_decide; [|by rewrite take_nil].
    rewrite take_drop_commute. destruct (Z.le_gt_cases i j) as [?|?].
    - do 2 f_equal. lia.
    - replace (Z.to_nat (j - i))%nat with 0%nat by lia. rewrite Nat.add_0_r.
      rewrite skipn_firstn_comm, Nat.sub_diag, take_0.
      symmetry. apply nil_length_inv. rewrite length_drop, length_take. lia.
  Qed.

  Lemma char_at_lookup_Some s i σ :
    s[i] = σ →
    0 ≤ i ∧ s !! (Z.to_nat i) = Some σ.
  Proof.
    unfold char_at, str_take, str_drop. case_bool_decide; [|done].
    intros Hi. split; [done|].
    apply (f_equal (λ s, s !! 0%nat)) in Hi. simpl in Hi. rewrite <-Hi.
    setoid_rewrite lookup_take; [|lia]. setoid_rewrite lookup_drop.
    f_equal. lia.
  Qed.
    
  Lemma lookup_Some_char_at s i σ :
    0 ≤ i →
    s !! (Z.to_nat i) = Some σ →
    s[i] = σ.
  Proof.
    intros ? Hi. apply list_eq => k. unfold_substr. destruct k.
    - simpl. rewrite <-Hi.
      setoid_rewrite lookup_take; [|lia]. setoid_rewrite lookup_drop. f_equal. lia.
    - simpl. rewrite lookup_nil. apply lookup_ge_None. rewrite length_take, length_drop. lia.
  Qed.

  Lemma char_at_inv_singleton c i σ :
    [c][i] = σ →
    i = 0 ∧ c = σ.
  Proof.
    intros Hi. apply char_at_lookup_Some in Hi as [? Hi].
    apply list_lookup_singleton_Some in Hi as [??]. split; [lia|done].
  Qed.

  Lemma char_at_inv_app i s1 s2 σ :
    (s1 ++ s2)[i] = σ →
    (0 ≤ i < length s1 ∧ s1[i] = σ) ∨
    (length s1 < i < length s2 ∧ s2[i - length s1] = σ).
  Admitted.

  (** [t ⊑ s] iff [t] is a prefix of [s]. *)
  Lemma str_prefix_spec t s :
    t ⊑ s ↔ t `prefix_of` s.
  Proof. apply bool_decide_spec. Qed.

  (** [t ⊒ s] iff [t] is a suffix of [s]. *)
  Lemma str_suffix_spec t s :
    t ⊒ s ↔ t `suffix_of` s.
  Proof. apply bool_decide_spec. Qed.

  (** The pattern [t] occurs in [s] at index [i]. *)
  Definition occur (t s : str) (i : Z) : Prop := t `prefix_of` s[i:].

  Lemma find_occur i s t :
    0 ≤ i →
    find s t = i →
    occur t s i.
  Admitted.

  Lemma find_first_occur i s t k :
    0 ≤ i →
    find s t = i →
    0 ≤ k ≤ length s - length t →
    occur t s k →
    i ≤ k.
  Admitted.

  Lemma occur_find s t i :
    0 ≤ i →
    occur t s i ∧ (∀ k, 0 ≤ k ≤ length s - length t → occur t s k → i ≤ k) →
    find s t = i.
  Admitted.

  Lemma find_nonneg i t s :
    occur t s i →
    0 ≤ find s t.
  Admitted.

  Lemma find_char_at s σ i :
    find s σ = i →
    0 ≤ i →
    s[i] = σ ∧ σ ∉ s[:i].
  Admitted.

  Lemma find_le s t :
    find s t ≤ length s - length t.
  Admitted.

  Lemma find_inv_empty s i :
    find s ([]) = i →
    s = [] ∨ i = 0.
  Admitted.

  (** [t `in` s] iff [t] is an infix of [s], i.e., [t] occurs in [s] at some index [i]. *)
  Lemma str_infix_spec t s :
    t `in` s ↔ ∃ k, 0 ≤ k ≤ length s - length t ∧ occur t s k.
  Proof.
    unfold str_infix. rewrite bool_decide_spec.
  Admitted.
  
  (*
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

  Lemma str_take_drop i s :
    (0 ≤ i)%Z →
    str_take i s ++ str_drop i s = s.
  Proof.
    intros. unfold str_take. rewrite unfold_str_drop by lia. apply take_drop.
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

  Lemma str_index_of_range t s i :
    str_index_of t s = i →
    (-1 ≤ i < length s)%Z.
  Admitted.

  Lemma str_index_of_neg t s :
    (str_index_of t s < 0)%Z ↔ ¬ (t `infix_of` s).
  Admitted.

  Lemma str_index_of_nonneg t s :
    (0 ≤ str_index_of t s)%Z ↔ t `infix_of` s.
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
  *)

End str_ops_properties.