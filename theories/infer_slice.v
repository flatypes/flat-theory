From stdpp Require Import sets.
From flat Require Import regexes split_regex.

Section infer_slice.

  Implicit Type (s : str).

  Fixpoint re_drop_1 (r : regex) : regex :=
    match r with
    | re_none => re_null
    | re_null => re_null
    | re_lit C => re_null
    | re_concat r1 r2 => 
      (re_drop_1 r1 ++ᵣ r2) ∪ (if bool_decide ([] ∈ r1) then re_drop_1 r2 else ∅)
    | re_union r1 r2 => re_drop_1 r1 ∪ re_drop_1 r2
    | re_star r => (re_drop_1 r ++ᵣ re_star r) ∪ re_null
    end.

  Lemma infer_drop_1 s r :
    s ∈ r →
    drop 1 s ∈ re_drop_1 r.
  Proof.
    induction 1; simpl.
    - constructor.
    - constructor.
    - destruct s1.
      * rewrite bool_decide_true by done. simpl. apply elem_of_union. by right.
      * rewrite drop_app, length_cons, drop_0.
        apply elem_of_union. left. by constructor.
    - apply elem_of_union. by left.
    - apply elem_of_union. by right.
    - apply elem_of_union. right. constructor.
    - rewrite drop_app. destruct s1; [done|]. rewrite length_cons, drop_0.
      apply elem_of_union. left. by constructor.
  Qed.

  Fixpoint re_drop (k : nat) (r : regex) : regex :=
    match k with
    | 0 => r
    | S k' => re_drop k' (re_drop_1 r)
    end.

  Lemma infer_drop s r k :
    s ∈ r →
    drop k s ∈ re_drop k r.
  Proof.
    revert s r. induction k as [|k IHk] => s r ?; simpl. { by rewrite drop_0. }
    replace (S k) with (1 + k) by lia.
    rewrite <-drop_drop. apply IHk. by apply infer_drop_1.
  Qed.

  Fixpoint re_take_1 (r : regex) : regex :=
    match r with
    | re_none => re_null
    | re_null => re_null
    | re_lit C => re_lit C
    | re_concat r1 r2 => 
      re_take_1 r1 ∪ (if bool_decide ([] ∈ r1) then re_take_1 r2 else ∅)
    | re_union r1 r2 => re_take_1 r1 ∪ re_take_1 r2
    | re_star r => re_take_1 r ∪ re_null
    end.

  Lemma infer_take_1 s r :
    s ∈ r →
    take 1 s ∈ re_take_1 r.
  Proof.
    induction 1; simpl.
    - constructor.
    - by constructor.
    - destruct s1.
      * rewrite bool_decide_true by done. simpl. apply elem_of_union. by right.
      * rewrite take_app, length_cons, take_0, app_nil_r.
        apply elem_of_union. by left.
    - apply elem_of_union. by left.
    - apply elem_of_union. by right.
    - apply elem_of_union. right. constructor.
    - rewrite take_app. destruct s1; [done|]. rewrite length_cons, take_0, app_nil_r.
      apply elem_of_union. by left.
  Qed.

  Fixpoint re_take (k : nat) (r : regex) : regex :=
    match k with
    | 0 => re_null
    | S k' => re_take_1 r ++ᵣ re_take k' (re_drop_1 r)
    end.

  Lemma infer_take s r k :
    s ∈ r →
    take k s ∈ re_take k r.
  Proof.
    revert s r. induction k as [|k IHk] => s r ?; simpl. { rewrite take_0. constructor. }
    replace (S k) with (1 + k) by lia.
    rewrite <-take_take_drop. constructor.
    + by apply infer_take_1.
    + apply IHk. by apply infer_drop_1.
  Qed.

  Set Printing Coercions.

  Inductive index : Type :=
    | i_nat : nat → index
    | i_rev : nat → index
    | i_fst : char → index
    .

  Definition index_sem (s : str) (i : index) : Z :=
    match i with
    | i_nat k => k
    | i_rev k => length s - k
    | i_fst c => str_index_of c s
    (* | i_fst_shr c k => str_index_of c s + k *)
    (* | i_fst_shl c k => str_index_of c s - k *)
    end.

  Local Notation "⟦ i ⟧ s" := (index_sem s i) (at level 20).

  Definition re_drop_index (i : index) (r : regex) : regex :=
    match i with
    | i_nat k => re_drop k r
    | i_rev k => re_rev (re_take k (re_rev r))
    | i_fst c => re_drop_until c r
    (* | i_fst_shr c k => re_drop_until_shr c k r *)
    (* | i_fst_shl c k => re_drop_until_shl c k r *)
    end.

  Definition re_take_index (i : index) (r : regex) : regex :=
    match i with
    | i_nat k => re_take k r
    | i_rev k => re_rev (re_drop k (re_rev r))
    | i_fst c => re_take_until c r
    (* | i_fst_shr c k => re_take_until_shr c k r *)
    (* | i_fst_shl c k => re_take_until_shl c k r *)
    end.

  Lemma reverse_drop_reverse s k :
    reverse (drop k (reverse s)) = take (length s - k) s.
  Proof.
    by rewrite drop_reverse, reverse_involutive.
  Qed.

  Lemma reverse_take_reverse k s :
    reverse (take k (reverse s)) = drop (length s - k) s.
  Proof.
    by rewrite take_reverse, reverse_involutive.
  Qed.

  Lemma infer_drop_index s r i :
    (0 ≤ ⟦ i ⟧ s)%Z →
    s ∈ r →
    str_drop (⟦ i ⟧ s) s ∈ re_drop_index i r.
  Proof.
    intros. unfold str_drop. rewrite bool_decide_true by lia.
    destruct i; simpl in *.
    - rewrite Nat2Z.id. by apply infer_drop.
    - replace (length s - n)%Z with (Z.of_nat (length s - n)) by lia.
      rewrite Nat2Z.id, <-reverse_take_reverse. apply elem_of_re_rev.
      by apply infer_take, elem_of_re_rev.
    - apply elem_of_re_drop_until; [..|done].
      all: apply str_index_of_nonneg; lia.
  Qed.

  Lemma infer_take_index s r i :
    (0 ≤ ⟦ i ⟧ s)%Z →
    s ∈ r →
    str_take (⟦ i ⟧ s) s ∈ re_take_index i r.
  Proof.
    intros. unfold str_take. destruct i; simpl in *.
    - rewrite Nat2Z.id. by apply infer_take.
    - replace (length s - n)%Z with (Z.of_nat (length s - n)) by lia.
      rewrite Nat2Z.id, <-reverse_drop_reverse. apply elem_of_re_rev.
      by apply infer_drop, elem_of_re_rev.
    - apply elem_of_re_take_until; [..|done].
      all: apply str_index_of_nonneg; lia.
  Qed.

  Lemma rewrite_drop_shl i k s :
    (0 ≤ i < length s ∧ 0 ≤ k ≤ i)%Z →
    str_drop (i - k) s = reverse (str_take k (reverse (str_take i s))) ++ (str_drop i s).
  Proof.
    intros. unfold str_drop, str_take.
    rewrite !bool_decide_true by lia.
    rewrite reverse_take_reverse, length_take, min_l, drop_take_drop by lia.
    f_equal. lia.
  Qed.

  Lemma rewrite_drop_shr i k s :
    (0 ≤ i ∧ 0 ≤ k)%Z →
    str_drop (i + k) s = str_drop k (str_drop i s).
  Proof.
    intros. unfold str_drop. rewrite !bool_decide_true by lia.
    rewrite drop_drop. f_equal. lia.
  Qed.

  Lemma str_at_take_1_drop i s :
    str_at i s = str_take 1 (str_drop i s).
  Proof.
    unfold str_at, str_take, str_drop. case_bool_decide; [case_match eqn:Heq|].
    - assert (Z.to_nat i < length s). { by apply lookup_lt_is_Some. }
      apply list_eq => j. destruct j; simpl.
      * rewrite lookup_take, lookup_drop by lia.
        by replace (Z.to_nat i + 0) with (Z.to_nat i) by lia.
      * by rewrite lookup_nil, lookup_take_ge by lia.
    - apply lookup_ge_None in Heq. by rewrite drop_ge, take_nil by lia.
    - by rewrite take_nil.
  Qed.

  Lemma str_drop_reverse i s :
    (0 ≤ i)%Z →
    str_drop i (reverse s) = reverse (str_take (length s - i) s).
  Proof.
    intros. unfold str_drop, str_take. rewrite bool_decide_true by lia.
    rewrite drop_reverse. do 2 f_equal. lia.
  Qed.

  Lemma str_take_reverse i s :
    (0 ≤ i ≤ length s)%Z →
    str_take i (reverse s) = reverse (str_drop (length s - i) s).
  Proof.
    intros. unfold str_drop, str_take. rewrite bool_decide_true by lia.
    rewrite take_reverse. do 2 f_equal. lia.
  Qed.

  Lemma str_at_reverse i s :
    (0 ≤ i < length s)%Z →
    str_at i (reverse s) = str_at (length s - (i + 1)) s.
  Proof.
    intros. unfold str_at. rewrite !bool_decide_true by lia.
    setoid_rewrite reverse_lookup; [|lia].
    by replace ((length s - S (Z.to_nat i))) with (Z.to_nat (Z.of_nat (length s) - (i + 1))) by lia.
  Qed.

  Lemma infer_at s r i :
    (0 ≤ ⟦ i ⟧ s)%Z →
    s ∈ r →
    str_at (⟦ i ⟧ s) s ∈ re_take_1 (re_drop_index i r).
  Proof.
    intros. rewrite str_at_take_1_drop. by apply infer_take_1, infer_drop_index.
  Qed.

  Lemma rewrite_str_at_index_of c s :
    let i := str_index_of c s in
    (0 ≤ i)%Z →
    str_at i s = [c].
  Proof.
    intros i ?. unfold str_at. rewrite bool_decide_true by lia.
    assert (i = Z.to_nat i) as Hi by lia. by apply str_index_of_nonneg in Hi as [-> _].
  Qed.

  Lemma rewrite_str_at_shl i k s :
    (0 ≤ i < length s ∧ 0 < k ≤ i)%Z →
    str_at (i - k) s = str_at (k - 1) (reverse (str_take i s)).
  Proof.
  Admitted.

  Lemma rewrite_str_at_shr i k s :
    (0 ≤ i ∧ 0 ≤ k)%Z →
    str_at (i + k) s = str_at k (str_drop i s).
  Proof.
    intros. by rewrite !str_at_take_1_drop, rewrite_drop_shr by lia.
  Qed.

  Inductive index_pos : index → Prop :=
    | i_nat_pos k : index_pos (i_nat k)
    | i_fst_pos c : index_pos (i_fst c)
    (* | i_fst_shr_pos c k : index_pos (i_fst_shr c k) *)
    .
  
  Lemma index_sem_take i n s :
    index_pos i →
    (0 ≤ ⟦ i ⟧ s < n)%Z →
    ⟦ i ⟧ (str_take n s) = ⟦ i ⟧ s.
  Proof.
    inversion 1; subst; simpl; intros.
    - done.
    - rewrite str_index_of_take; lia.
  Qed.

  Lemma infer_substr_drop_take s r i j r1 r2 :
    index_pos i →
    (0 ≤ ⟦ i ⟧ s < ⟦ j ⟧ s)%Z →
    s ∈ r →
    re_take_index j r = r1 →
    re_drop_index i r1 = r2 →
    str_substr (⟦ i ⟧ s) (⟦ j ⟧ s) s ∈ r2.
  Proof.
    intros. subst. rewrite str_substr_alt.
    rewrite <-(index_sem_take i (⟦ j ⟧ s)); [|done|lia].
    apply infer_drop_index. { rewrite index_sem_take; [lia|done|lia]. }
    apply infer_take_index; [lia|done].
  Qed.

  Inductive index_neg : index → Prop :=
    | i_rev_neg k : index_neg (i_rev k)
    | i_fst_neg c : index_neg (i_fst c)
    (* | i_fst_shl_neg c k : index_neg (i_fst_shl c k) *)
    .

  Lemma index_sem_drop i n s :
    index_neg i →
    (0 ≤ n < ⟦ i ⟧ s)%Z →
    ⟦ i ⟧ (str_drop n s) = (⟦ i ⟧ s - n)%Z.
  Proof.
    inversion 1; subst; simpl; intros.
    - unfold str_drop. rewrite bool_decide_true, length_drop; lia.
    - rewrite str_index_of_drop; lia.
  Qed.
  
  Lemma infer_substr_take_drop s r i j r1 r2 :
    index_neg j →
    (0 ≤ ⟦ i ⟧ s < ⟦ j ⟧ s)%Z →
    s ∈ r →
    re_drop_index i r = r1 →
    re_take_index j r1 = r2 →
    str_substr (⟦ i ⟧ s) (⟦ j ⟧ s) s ∈ r2.
  Proof.
    intros. subst. unfold str_substr.
    rewrite <-(index_sem_drop j (⟦ i ⟧ s)); [|done|lia].
    apply infer_take_index.
    { rewrite index_sem_drop; [lia|done|lia]. }
    apply infer_drop_index; [lia|done].
  Qed.

  Lemma rewrite_substr_l_shl (i j k : nat) s :
    i < length s ∧ k ≤ i < j →
    str_substr (i - k)%nat j s = reverse (str_take k (reverse (str_take i s))) ++
                                 (str_substr i j s).
  Proof.
    intros. rewrite !str_substr_alt. unfold str_drop, str_take.
    rewrite !bool_decide_true, !Nat2Z.id by lia.
    rewrite reverse_take_reverse, length_take, min_l, <-(drop_take_drop _ _ i) by lia.
    by rewrite take_take, min_l by lia.
  Qed.

  Lemma rewrite_substr_l_shr (i j k : nat) s :
    str_substr (i + k)%nat j s = str_drop k (str_substr i j s).
  Proof.
    intros. rewrite !str_substr_alt. unfold str_drop, str_take.
    rewrite !bool_decide_true, !Nat2Z.id by lia. by rewrite drop_drop.
  Qed.

  Lemma rewrite_substr_r_shl (i j k : nat) s :
    i < j < length s ∧ k ≤ j →
    str_substr i (j - k) s = reverse (str_drop k (reverse (str_substr i j s))).
  Proof.
    intros. unfold str_substr, str_take, str_drop.
    rewrite !bool_decide_true, !Nat2Z.id by lia.
    replace (Z.to_nat (j - i)) with (j - i) by lia.
    rewrite reverse_drop_reverse, length_take, length_drop, min_l, take_take, min_l by lia.
    by replace (Z.to_nat (j - k - i)) with (j - i - k) by lia.
  Qed.

  Lemma rewrite_substr_r_shr (i j k : nat) s :
    i < j →
    str_substr i (j + k) s = (str_substr i j s) ++ (take k (str_drop j s)).
  Proof.
    intros. unfold str_substr, str_take, str_drop.
    rewrite !bool_decide_true, !Nat2Z.id by lia.
    replace (Z.to_nat (j + k - i)) with ((j - i) + k) by lia. rewrite <-take_take_drop.
    replace (Z.to_nat (j - i)) with (j - i) by lia.
    rewrite drop_drop. by replace (i + (j - i)) with j by lia.
  Qed.

End infer_slice.