From stdpp Require Import list options sets.
From flat Require Import regexes synth_prefix.

Section lang_infer.

  Implicit Type (s : str).

  Corollary infer_concat s1 r1 s2 r2 :
    s1 ∈ r1 →
    s2 ∈ r2 →
    s1 ++ s2 ∈ r1 ⧺ r2.
  Proof.
    by constructor.
  Qed.

  Corollary infer_reverse s r :
    s ∈ r →
    reverse s ∈ re_rev r.
  Proof. apply elem_of_re_rev. Qed.

  Fixpoint re_drop_1 (r : regex) : regex :=
    match r with
    | re_none => re_null
    | re_null => re_null
    | re_lit C => re_null
    | re_concat r1 r2 => 
      (re_drop_1 r1 ⧺ r2) ∪ (if bool_decide ([] ∈ r1) then re_drop_1 r2 else ∅)
    | re_union r1 r2 => re_drop_1 r1 ∪ re_drop_1 r2
    | re_star r => (re_drop_1 r ⧺ re_star r) ∪ re_null
    end.

  Lemma elem_of_re_drop_1 s r :
    s ∈ r →
    drop 1 s ∈ re_drop_1 r.
  Proof.
    induction 1; simpl.
    - constructor.
    - constructor.
    - destruct s1.
      * rewrite bool_decide_true by done. simpl. apply elem_of_union. by right.
      * simplify_list_eq. rewrite drop_0. apply elem_of_union. left. by constructor.
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

  Lemma elem_of_re_drop s r k :
    s ∈ r →
    drop k s ∈ re_drop k r.
  Proof.
    revert s r. induction k as [|k IHk] => s r ?; simpl. { by rewrite drop_0. }
    replace (S k) with (1 + k) by lia.
    rewrite <-drop_drop. apply IHk. by apply elem_of_re_drop_1.
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

  Lemma elem_of_re_take_1 s r :
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
    | S k' => re_take_1 r ⧺ re_take k' (re_drop_1 r)
    end.

  Lemma elem_of_re_take s r k :
    s ∈ r →
    take k s ∈ re_take k r.
  Proof.
    revert s r. induction k as [|k IHk] => s r ?; simpl. { rewrite take_0. constructor. }
    replace (S k) with (1 + k) by lia.
    rewrite <-take_take_drop. constructor.
    + by apply elem_of_re_take_1.
    + apply IHk. by apply elem_of_re_drop_1.
  Qed.

  (* General incomplete approach for index of str pattern *)

  Definition re_find_str (t : str) (r : regex) : list (regex * regex) :=
    match t with
    | [] => [(re_null, r)]
    | c :: t' =>
      '(r1, r2) ← re_find c r ;
      let r' := derive_ext t r2 in
      if bool_decide (r' ≢ ∅) then [(r1, {[ t ]} ⧺ r')] else []
    end.

  Lemma elem_of_re_find_str s r t i :
    s ∈ r →
    str_index_of t s = i →
    (0 ≤ i)%Z →
    ∃ r1 r2, (r1, r2) ∈ re_find_str t r ∧ str_take i s ∈ r1 ∧ str_drop i s ∈ r2.
  Proof.
    intros ? H ?. destruct t as [|c t'].
    - rewrite str_index_of_nil in H. subst. unfold re_find_str.
      exists re_null, r. repeat split; [set_solver | constructor | done].
    - apply str_index_of_eq in H as [??]; [|lia]. destruct H as [? Heq].
      assert (str_at i s = [c]) as Hi. { unfold str_at. by rewrite Heq. }
      eapply elem_of_re_find in Hi as [r1 [r2 [? [Hp Hs]]]]; [|done].
      rewrite Heq in *. apply elem_of_derive_ext in Hs.
      exists r1, ({[ c :: t' ]} ⧺ derive_ext (c :: t') r2). repeat split; [|done|].
      + unfold re_find_str. rewrite elem_of_list_bind. eexists. split; [|done].
        case_match. rewrite bool_decide_true; set_solver.
      + constructor; [set_solver | done].
  Qed.

  Definition re_take_until (t : str) (r : regex) : regex := ⋃ (fst <$> re_find_str t r).
  Definition re_drop_until (t : str) (r : regex) : regex := ⋃ (snd <$> re_find_str t r).

  Lemma elem_of_re_take_until s r t i :
    s ∈ r →
    str_index_of t s = i →
    (0 ≤ i)%Z →
    str_take i s ∈ re_take_until t r.
  Proof.
    intros ? H ?. unfold re_take_until. rewrite elem_of_union_list.
    eapply elem_of_re_find_str in H as [? [? [? [??]]]]; [|done|lia].
    setoid_rewrite elem_of_list_fmap. eauto.
  Qed.
  
  Lemma elem_of_re_drop_until s r t i :
    s ∈ r →
    str_index_of t s = i →
    (0 ≤ i)%Z →
    str_drop i s ∈ re_drop_until t r.
  Proof.
    intros ? H ?. unfold re_drop_until. rewrite elem_of_union_list.
    eapply elem_of_re_find_str in H as [? [? [? [??]]]]; [|done|lia].
    setoid_rewrite elem_of_list_fmap. eauto.
  Qed.

  (* Special case for char *)

  Fixpoint re_exclude (c : char) (r : regex) : regex :=
    match r with
    | re_none => re_none
    | re_null => re_null
    | re_lit C => re_lit (C ∖ {[ c ]})
    | re_concat r1 r2 => re_exclude c r1 ⧺ re_exclude c r2
    | re_union r1 r2 => re_exclude c r1 ∪ re_exclude c r2
    | re_star r => re_star (re_exclude c r)
    end.

  Lemma elem_of_re_exclude s c r :
    s ∈ r →
    c ∉ s →
    s ∈ re_exclude c r.
  Proof.
    induction 1; simpl; intros; constructor; set_solver.
  Qed.

  Definition re_find_first (c : char) (r : regex) : list (regex * regex) :=
    '(r1, r2) ← re_find c r ;
    let r1' := re_exclude c r1 in
    if bool_decide (r1' ≢ ∅) then [(r1', re_lit {[ c ]} ⧺ derive c r2)] else [].

  Lemma elem_of_re_find_first s r c i :
    s ∈ r →
    str_index_of [c] s = i →
    (0 ≤ i)%Z →
    ∃ r1 r2, (r1, r2) ∈ re_find_first c r ∧ str_take i s ∈ r1 ∧ str_drop i s ∈ r2.
  Proof.
    intros Hs H ?. apply str_index_of_char_eq in H as [Hi Hp]; [|lia]. 
    destruct (elem_of_re_find _ _ _ _ Hs Hi) as [r1 [r2 [? [??]]]].
    eapply elem_of_re_exclude in Hp; [|done].
    exists (re_exclude c r1), (re_lit {[ c ]} ⧺ derive c r2). repeat split; [|done|].
    + unfold re_find_first. rewrite elem_of_list_bind. eexists. split; [|done].
      case_match. rewrite bool_decide_true; set_solver.
    + assert (∃ s', str_drop i s = c :: s') as [s' Hs'].
      { rewrite str_at_lookup_Some in Hi by lia. rewrite unfold_str_drop by lia. eexists. by apply drop_S. }
      rewrite Hs' in *. apply elem_of_concat_lit; [set_solver|]. by apply elem_of_derive.
  Qed.

  Inductive index : Type :=
    | i_nat : nat → index
    | i_rev : nat → index
    | i_fst : str → index
    .

  Definition index_sem (s : str) (i : index) : Z :=
    match i with
    | i_nat k => k
    | i_rev k => length s - k
    | i_fst c => str_index_of c s
    end.

  Local Notation "⟦ i ⟧ s" := (index_sem s i) (at level 20).

  Definition re_take_index (i : index) (r : regex) : regex :=
    match i with
    | i_nat k => re_take k r
    | i_rev k => re_rev (re_drop k (re_rev r))
    | i_fst c => re_take_until c r
    end.

  Set Printing Coercions.

  Ltac simplify_arith :=
    repeat match goal with
    | _ => progress simplify_eq/=
    | |- context [Z.to_nat (Z.of_nat _)] =>
      rewrite Nat2Z.id
    | |- context [Z.to_nat (Z.of_nat ?x - Z.of_nat ?y)] =>
      try replace (Z.to_nat (Z.of_nat x - Z.of_nat y)) with (x - y) by lia
    end.

  Lemma infer_take_index s r i :
    (0 ≤ ⟦ i ⟧ s)%Z →
    s ∈ r →
    str_take (⟦ i ⟧ s) s ∈ re_take_index i r.
  Proof.
    intros. destruct i; simpl in *.
    - unfold str_take. rewrite Nat2Z.id. by apply elem_of_re_take.
    - rewrite<-reverse_str_drop_reverse by lia. apply elem_of_re_rev.
      unfold str_drop. rewrite bool_decide_true, Nat2Z.id by lia.
      by apply elem_of_re_drop, elem_of_re_rev.
    - apply elem_of_re_take_until; [done..|lia].
  Qed.

  Lemma rewrite_take_shl i k s :
    (0 ≤ k ≤ i ∧ i ≤ length s)%Z →
    str_take (i - k) s = reverse (str_drop k (reverse (str_take i s))).
  Proof.
    intros. rewrite reverse_str_drop_reverse by lia.
    rewrite str_take_take. f_equal. rewrite length_str_take. lia.
  Qed.

  Lemma rewrite_take_shr i k s :
    (0 ≤ k ∧ 0 ≤ i)%Z →
    str_take (i + k) s = str_take i s ++ str_take k (str_drop i s).
  Proof.
    intros. by rewrite str_take_take_drop by lia.
  Qed.

  Definition re_drop_index (i : index) (r : regex) : regex :=
    match i with
    | i_nat k => re_drop k r
    | i_rev k => re_rev (re_take k (re_rev r))
    | i_fst c => re_drop_until c r
    end.
  
  Lemma infer_drop_index s r i :
    (0 ≤ ⟦ i ⟧ s)%Z →
    s ∈ r →
    str_drop (⟦ i ⟧ s) s ∈ re_drop_index i r.
  Proof.
    intros. destruct i; simpl in *.
    - unfold str_drop. rewrite bool_decide_true, Nat2Z.id by lia.
      by apply elem_of_re_drop.
    - rewrite<-reverse_str_take_reverse by lia. apply elem_of_re_rev.
      unfold str_take. rewrite Nat2Z.id. by apply elem_of_re_take, elem_of_re_rev.
    - apply elem_of_re_drop_until; [done..|lia].
  Qed.

  Lemma rewrite_drop_shl i k s :
    (0 ≤ k ≤ i ∧ i ≤ length s)%Z →
    str_drop (i - k) s = reverse (str_take k (reverse (str_take i s))) ++ (str_drop i s).
  Proof.
    intros. rewrite reverse_str_take_reverse; rewrite length_str_take; [|lia].
    rewrite str_drop_take_drop by lia. f_equal. lia.
  Qed.

  Lemma rewrite_drop_shr i k s :
    (0 ≤ k ∧ 0 ≤ i)%Z →
    str_drop (i + k) s = str_drop k (str_drop i s).
  Proof.
    intros. rewrite str_drop_drop by lia. f_equal. lia.
  Qed.

  (** Substring *)

  Lemma rewrite_substr_dependent i k s :
    str_substr i (i + k) s = str_take k (str_drop i s).
  Proof.
    unfold str_substr. f_equal. lia.
  Qed.

  Inductive index_neg : index → Prop :=
    | i_rev_neg k : index_neg (i_rev k)
    | i_fst_neg c : index_neg (i_fst c)
    .

  Lemma index_shift_suffix i n s :
    index_neg i →
    (0 ≤ n < ⟦ i ⟧ s)%Z →
    ⟦ i ⟧ (str_drop n s) = (⟦ i ⟧ s - n)%Z.
  Proof.
    inversion 1; subst; simpl; intros.
    - rewrite length_str_drop, bool_decide_true by lia. lia. 
    - rewrite str_index_of_drop; lia.
  Qed.
  
  Lemma infer_substr_independent s r i j r1 r2 :
    index_neg j →
    (0 ≤ ⟦ i ⟧ s < ⟦ j ⟧ s)%Z →
    s ∈ r →
    re_drop_index i r = r1 →
    re_take_index j r1 = r2 →
    str_substr (⟦ i ⟧ s) (⟦ j ⟧ s) s ∈ r2.
  Proof.
    intros. subst. unfold str_substr.
    rewrite <-(index_shift_suffix j (⟦ i ⟧ s)); [|done|lia].
    apply infer_take_index.
    { rewrite index_shift_suffix; [lia|done|lia]. }
    apply infer_drop_index; [lia|done].
  Qed.

  Inductive index_pos : index → Prop :=
    | i_nat_pos k : index_pos (i_nat k)
    | i_fst_pos c : index_pos (i_fst c)
    .
  
  (* TODO: only consider when j is const and i is fst_pos *)
  Lemma index_shift_prefix i n s :
    index_pos i →
    (0 ≤ ⟦ i ⟧ s < n)%Z →
    ⟦ i ⟧ (str_take n s) = ⟦ i ⟧ s.
  Proof.
    inversion 1; subst; simpl; intros. { lia. }
    rewrite str_index_of_take; [done|].
  Admitted.

  Lemma infer_substr_drop_take s r i j r1 r2 :
    index_pos i →
    (0 ≤ ⟦ i ⟧ s < ⟦ j ⟧ s)%Z →
    s ∈ r →
    re_take_index j r = r1 →
    re_drop_index i r1 = r2 →
    str_substr (⟦ i ⟧ s) (⟦ j ⟧ s) s ∈ r2.
  Proof.
    intros. subst. rewrite str_substr_alt.
    rewrite <-(index_shift_prefix i (⟦ j ⟧ s)); [|done|lia].
    apply infer_drop_index. { rewrite index_shift_prefix; [lia|done|lia]. }
    apply infer_take_index; [lia|done].
  Qed.

  Lemma rewrite_substr_l_shl i j k s :
    (0 ≤ k ≤ i ∧ i ≤ j ≤ length s)%Z →
    str_substr (i - k) j s = reverse (str_take k (reverse (str_take i s))) ++
                             (str_substr i j s).
  Proof.
    intros. rewrite !str_substr_alt, rewrite_drop_shl.
    2: { rewrite length_str_take. lia. }
    do 4 f_equal. rewrite str_take_take. f_equal. lia.
  Qed.

  Lemma rewrite_substr_l_shr i j k s :
    (0 ≤ k ∧ 0 ≤ i)%Z →
    str_substr (i + k) j s = str_drop k (str_substr i j s).
  Proof.
    intros. by rewrite !str_substr_alt, rewrite_drop_shr by lia.
  Qed.

  Lemma rewrite_substr_r_shl i j k s :
    (0 ≤ k ∧ 0 ≤ i ≤ j - k ∧ j ≤ length s)%Z →
    str_substr i (j - k) s = reverse (str_drop k (reverse (str_substr i j s))).
  Proof.
    intros. unfold str_substr.
    replace (j - k - i)%Z with ((j - i) - k)%Z by lia.
    rewrite rewrite_take_shl; [done|].
    rewrite length_str_drop, bool_decide_true by lia. lia.
  Qed.

  Lemma rewrite_substr_r_shr i j k s :
    (0 ≤ k ∧ 0 ≤ i ≤ j)%Z →
    str_substr i (j + k) s = (str_substr i j s) ++ (str_take k (str_drop j s)).
  Proof.
    intros. unfold str_substr.
    replace (j + k - i)%Z with ((j - i) + k)%Z by lia.
    rewrite rewrite_take_shr by lia.
    do 2 f_equal. rewrite str_drop_drop by lia. f_equal. lia.
  Qed.

  (** Char at: by definition *)

  Lemma rewrite_str_at_index_of t s k :
    let i := str_index_of t s in
    (0 ≤ i ∧ 0 ≤ k < length t)%Z →
    str_at (i + k) s = str_at k t.
  Proof.
    intros i ?. unfold str_at. rewrite Z.add_comm, <-str_drop_drop by lia.
    assert (t `prefix_of` str_drop i s) as [? ->]. { apply str_index_of_prefix. lia. }
    rewrite str_drop_app_l by lia.
    rewrite str_take_app_l; [done|]. rewrite length_str_drop, bool_decide_true; lia.
  Qed.

End lang_infer.