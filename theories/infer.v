From stdpp Require Import list options sets.
From flat Require Import regexes split_regex.

Section infer_basic.

  Implicit Type (s : str).

  Corollary infer_concat s1 r1 s2 r2 :
    s1 ∈ r1 →
    s2 ∈ r2 →
    s1 ++ s2 ∈ r1 ++ᵣ r2.
  Proof.
    by constructor.
  Qed.

  Fixpoint re_length_min (r : regex) : nat :=
    match r with
    | re_none => 0
    | re_null => 0
    | re_lit _ => 1
    | re_concat r1 r2 => re_length_min r1 + re_length_min r2
    | re_union r1 r2 => re_length_min r1 `min` re_length_min r2
    | re_star _ => 0
    end.

  Lemma infer_length_min s r :
    s ∈ r →
    re_length_min r ≤ length s.
  Proof.
    induction 1; simpl; try lia. rewrite length_app. lia.
  Qed.

  Fixpoint re_length_max (r : regex) : option nat :=
    match r with
    | re_none => Some 0
    | re_null => Some 0
    | re_lit _ => Some 1
    | re_concat r1 r2 => 
      m1 ← re_length_max r1; m2 ← re_length_max r2; Some (m1 + m2)
    | re_union r1 r2 =>
      m1 ← re_length_max r1; m2 ← re_length_max r2; Some (m1 `max` m2)
    | re_star r =>
      m ← re_length_max r; if bool_decide (m = 0) then Some 0 else None
    end.

  Lemma infer_length_max s r :
    s ∈ r →
    ∀ m, re_length_max r = Some m → length s ≤ m.
  Proof.
    induction 1; intros; simplify_option_eq; try lia.
    - rewrite length_app. apply Nat.add_le_mono; auto.
    - etrans; [|by apply Nat.le_max_l]. auto.
    - etrans; [|by apply Nat.le_max_r]. auto.
    - rewrite length_app. replace 0 with (0 + 0) by lia. apply Nat.add_le_mono; auto.
  Qed.

  Corollary infer_reverse s r :
    s ∈ r →
    reverse s ∈ re_rev r.
  Proof. apply elem_of_re_rev. Qed.

End infer_basic.

Section infer_test.

  Implicit Type (s t : str) (r : regex).

  Fixpoint re_cnf (r : regex) : list regex :=
    match r with
    | re_null => []
    | re_concat r1 r2 => re_cnf r1 ++ re_cnf r2
    | _ => [r]
    end.

  Lemma re_cnf_cons s r r1 l :
    s ∈ r →
    re_cnf r = r1 :: l →
    ∃ s1 s2 r2, s = s1 ++ s2 ∧ s1 ∈ r1 ∧ s2 ∈ r2 ∧ re_cnf r2 = l.
  Admitted.

  Lemma re_cnf_app s r l1 l2 :
    s ∈ r →
    re_cnf r = l1 ++ l2 →
    ∃ s1 s2 r1 r2, s = s1 ++ s2 ∧ s1 ∈ r1 ∧ s2 ∈ r2 ∧ re_cnf r1 = l1 ∧ re_cnf r2 = l2.
  Admitted.

  Fixpoint collect_prefix (l : list regex) : str :=
    match l with
    | re_lit C :: l' =>
      match charset_is_singleton C with
      | Some c => c :: collect_prefix l'
      | None => []
      end
    | _ => []
    end.

  Lemma collect_prefix_spec s r l :
    s ∈ r →
    re_cnf r = l →
    collect_prefix l `prefix_of` s.
  Proof.
    revert s r. induction l as [|r' l'] => s r Hs Hl; simplify_eq/=.
    { apply prefix_nil. }
    case_match; simplify_eq/=; try apply prefix_nil.
    case_match eqn:HC; simplify_eq/=; [|apply prefix_nil].
    apply charset_is_singleton_Some in HC.
    eapply re_cnf_cons in Hl; [|done].
    destruct Hl as [s1 [s2 [r2 [-> [Hs1 [??]]]]]].
    inv Hs1. rewrite HC, elem_of_singleton in H3. simplify_eq.
    rewrite str_app_cons. apply prefix_cons. eauto.
  Qed.

  Lemma infer_prefix_must s r l t :
    s ∈ r →
    re_cnf r = l →
    t `prefix_of` collect_prefix l →
    t `prefix_of` s.
  Proof.
    intros. trans (collect_prefix l). { done. }
    by eapply collect_prefix_spec.
  Qed.

  Lemma infer_suffix_must s r l t :
    s ∈ r →
    re_cnf (re_rev r) = l →
    (reverse t) `prefix_of` collect_prefix l →
    t `suffix_of` s.
  Proof.
    intros Hs ??. apply suffix_prefix_reverse.
    apply elem_of_re_rev in Hs. by eapply infer_prefix_must.
  Qed.

  Lemma infer_infix_must s r l t i :
    s ∈ r →
    re_cnf r = l →
    t `infix_of` collect_prefix (drop i l) →
    t `infix_of` s.
  Proof.
    intros Hs Hr ?. rewrite <-(take_drop i l) in Hr.
    apply (re_cnf_app _ _ _ _ Hs) in Hr as [s1 [s2 [r1 [r2 [-> [? [Hs2 [? Hr2]]]]]]]].
    apply (collect_prefix_spec _ _ _ Hs2) in Hr2 as [? ->].
    by apply infix_app_r, infix_app_l.
  Qed.

  Fixpoint derive (c : char) (r : regex) : regex :=
    match r with
    | re_none => ∅
    | re_null => ∅
    | re_lit C => if bool_decide (c ∈ C) then re_null else ∅
    | re_concat r1 r2 => (derive c r1 ++ᵣ r2) ∪ (if bool_decide ([] ∈ r1) then derive c r2 else ∅)
    | re_union r1 r2 => derive c r1 ∪ derive c r2
    | re_star r => derive c r ++ᵣ re_star r
    end.

  Lemma elem_of_derive s c r :
    s ∈ derive c r ↔ c :: s ∈ r.
  Proof.
    split.
    + revert s. induction r => s; simpl; intros Hr.
      - by apply not_elem_of_empty in Hr.
      - by apply not_elem_of_empty in Hr.
      - case_bool_decide; [|by apply not_elem_of_empty in Hr].
        inv Hr. by constructor.
      - apply elem_of_union in Hr as [Hr|Hr].
        * inv Hr. rewrite app_comm_cons. constructor; [auto|done].
        * case_bool_decide; [|by apply not_elem_of_empty in Hr].
          rewrite <-(app_nil_l (c :: s)). constructor; [done|auto].
      - apply elem_of_union. apply elem_of_union in Hr as [?|?]; auto.
      - inv Hr. rewrite app_comm_cons. constructor; [done|auto|done].
    + revert s. induction r => s.
      all: inversion 1 as [|?|?????? Heq|?|?|?|?????? Heq]; subst.
      - simpl. case_bool_decide; [constructor | congruence].
      - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; simpl; apply elem_of_union.
        * right. rewrite bool_decide_true; eauto.
        * left. constructor; eauto.
      - simpl. apply elem_of_union. eauto.
      - simpl. apply elem_of_union. eauto.
      - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; [done|].
        simpl. constructor; eauto.
  Qed.

  Fixpoint derive_ext (t : str) (r : regex) : regex :=
    match t with
    | [] => r
    | c :: t' => derive_ext t' (derive c r)
    end.

  Lemma elem_of_derive_ext t s r :
    s ∈ derive_ext t r ↔ t ++ s ∈ r.
  Proof.
    revert r. induction t => r; simpl. { done. } by rewrite <-elem_of_derive.
  Qed.

  Lemma infer_prefix_never s r t :
    s ∈ r →
    derive_ext t r ≡ ∅ →
    ¬ (t `prefix_of` s).
  Proof.
    intros Hs Ht [? ->]. apply elem_of_derive_ext in Hs.
    rewrite Ht in Hs. by apply not_elem_of_empty in Hs.
  Qed.

  (* Axiom *)
  Lemma elem_of_non_empty {A C} `{SemiSet A C} (X : C) :
    X ≢ ∅ → ∃ x, x ∈ X.
  Admitted.

  Lemma infer_prefix_never_complete r t :
    (∀ s, s ∈ r → ¬ (t `prefix_of` s)) →
    derive_ext t r ≡ ∅.
  Proof.
    intros H. destruct (re_empty_dec (derive_ext t r)) as [?|Hr]; [done|].
    apply elem_of_non_empty in Hr as [s Hs].
    apply elem_of_derive_ext in Hs. unfold prefix in H. naive_solver.
  Qed.

  Lemma infer_suffix_never s r t :
    s ∈ r →
    derive_ext (reverse t) (re_rev r) ≡ ∅ →
    ¬ (t `suffix_of` s).
  Proof.
    intros Hs ?. rewrite suffix_prefix_reverse.
    apply elem_of_re_rev in Hs. by eapply infer_prefix_never.
  Qed.

  Fixpoint search (c : char) (r : regex) : list regex :=
    match r with
    | re_none => []
    | re_null => []
    | re_lit C => if bool_decide (c ∈ C) then [re_lit C] else []
    | re_concat r1 r2 => ((λ r', r' ++ᵣ r2) <$> search c r1) ++ search c r2
    | re_union r1 r2 => search c r1 ++ search c r2
    | re_star r => (λ r', r' ++ᵣ re_star r) <$> (search c r)
    end.

  Lemma app_eq_app_cons_inv {A : Type} (l1 l2 k1 k2 : list A) x :
    l1 ++ l2 = k1 ++ x :: k2 →
    (∃ k, l1 = k1 ++ x :: k ∧ k2 = k ++ l2) ∨ (∃ k, k1 = l1 ++ k ∧ l2 = k ++ x :: k2).
  Proof.
    intros Heq. apply app_eq_inv in Heq as [[l' [-> ?]]|[l' [-> ->]]]; [destruct l'|].
    - simplify_list_eq. right. exists []. by simplify_list_eq.
    - simplify_list_eq. left. eauto.
    - right. eauto. 
  Qed.

  Lemma elem_of_search s r c t :
    s ∈ r →
    c :: t `suffix_of` s →
    ∃ r', c :: t ∈ r' ∧ r' ∈ search c r.
  Proof.
    intros Hs. revert c t.
    induction Hs as [|C c'|r1 r2 s1 s2 ? IHr1 ? IHr2|
      r1 r2 s1 s2 IHr|r1 r2 s1 s2 IHr|?|r s1 s2 ?? IHr1 ? IHr2] => c t Ht.
    - by apply suffix_nil_inv in Ht.
    - apply suffix_cons_inv in Ht as [Ht|Ht]; [|by apply suffix_nil_inv in Ht].
      simplify_eq/=. rewrite bool_decide_true by done.
      exists (re_lit C). split; [by constructor | by apply elem_of_list_singleton].
    - destruct Ht as [p Ht].
      apply app_eq_app_cons_inv in Ht as [[s1' [-> ->]]|[s2' [-> ->]]].
      * destruct (IHr1 c s1') as [r1' [??]]. { by apply suffix_app_r. }
        exists (r1' ++ᵣ r2). split. { rewrite app_comm_cons. by constructor. }
        simpl. apply elem_of_app. left. apply elem_of_list_fmap. eauto.
      * destruct (IHr2 c t) as [r2' [??]]. { by apply suffix_app_r. }
        exists r2'. split; [done|]. simpl. apply elem_of_app. by right.
    - destruct (IHr c t) as [r' [??]]; [done|].
      exists r'. split; [done|]. simpl. apply elem_of_app. by left.
    - destruct (IHr c t) as [r' [??]]; [done|].
      exists r'. split; [done|]. simpl. apply elem_of_app. by right.
    - by apply suffix_nil_inv in Ht.
    - destruct Ht as [p Ht].
      apply app_eq_app_cons_inv in Ht as [[s1' [-> ->]]|[s2' [-> ->]]].
      * destruct (IHr1 c s1') as [r1' [??]]. { by apply suffix_app_r. }
        exists (r1' ++ᵣ re_star r). split. { rewrite app_comm_cons. by constructor. }
        simpl. apply elem_of_list_fmap. eauto.
      * destruct (IHr2 c t) as [r2' [??]]. { by apply suffix_app_r. }
        by exists r2'.
  Qed.

  Lemma infer_infix_never s r c t :
    s ∈ r →
    Forall (λ r', derive_ext (c :: t) r' ≡ ∅) (search c r) →
    ¬ ((c :: t) `infix_of` s).
  Proof.
    intros Hs H [? [t' ?]].
    assert (c :: t ++ t' `suffix_of` s) as Ht'. { unfold suffix. eauto. }
    apply (elem_of_search _ _ _ _ Hs) in Ht' as [r' [Ht' Hr']].
    rewrite Forall_forall in H. apply H, (infer_prefix_never _ _ _ Ht') in Hr'.
    unfold prefix in Hr'. eauto.
  Qed.

  Fixpoint re_alphabet (r : regex) : charset :=
    match r with
    | re_none => ∅
    | re_null => ∅
    | re_lit C => C
    | re_concat r1 r2 => re_alphabet r1 ∪ re_alphabet r2
    | re_union r1 r2 => re_alphabet r1 ∪ re_alphabet r2
    | re_star r => re_alphabet r
    end.

  Lemma elem_of_re_alphabet s c r :
    s ∈ r →
    c ∈ s →
    c ∈ re_alphabet r.
  Proof.
    induction 1; set_solver.
  Qed.

  Lemma infer_infix_never_alphabet s r t :
    s ∈ r →
    str_alphabet t ⊈ re_alphabet r →
    ¬ (t `infix_of` s).
  Proof.
    intros Hs H Ht. apply H. intros c Hc.
    apply (elem_of_re_alphabet _ _ _ Hs).
    rewrite elem_of_str_alphabet in Hc. destruct Ht as [? [? ?]]. set_solver.
  Qed.

End infer_test.

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
    | S k' => re_take_1 r ++ᵣ re_take k' (re_drop_1 r)
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
    - unfold str_take. apply elem_of_re_take_until; [..|done].
      all: apply str_index_of_nonneg; lia.
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
    - unfold str_drop. rewrite bool_decide_true by lia.
      apply elem_of_re_drop_until; [..|done].
      all: apply str_index_of_nonneg; lia.
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

  Inductive index_pos : index → Prop :=
    | i_nat_pos k : index_pos (i_nat k)
    | i_fst_pos c : index_pos (i_fst c)
    .
  
  Lemma index_shift_prefix i n s :
    index_pos i →
    (0 ≤ ⟦ i ⟧ s < n)%Z →
    ⟦ i ⟧ (str_take n s) = ⟦ i ⟧ s.
  Proof.
    inversion 1; subst; simpl; intros. { lia. }
    rewrite str_index_of_take; lia.
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
    rewrite <-(index_shift_prefix i (⟦ j ⟧ s)); [|done|lia].
    apply infer_drop_index. { rewrite index_shift_prefix; [lia|done|lia]. }
    apply infer_take_index; [lia|done].
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
  
  Lemma infer_substr_take_drop s r i j r1 r2 :
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

  (** Char at *)

  Lemma rewrite_at i s :
    str_at i s = str_take 1 (str_drop i s).
  Proof.
    unfold str_at. case_bool_decide.
    - unfold str_take, str_drop. rewrite bool_decide_true by lia.
      case_match eqn:Heq. 1: apply list_eq => k; destruct k; simpl.
      * rewrite lookup_take, lookup_drop, <-Heq by lia. f_equal. lia.
      * by rewrite lookup_nil, lookup_take_ge by lia.
      * apply lookup_ge_None in Heq. by rewrite drop_ge by lia.
    - unfold str_drop. by rewrite bool_decide_false by lia.
  Qed.

  Lemma rewrite_str_at_index_of c s :
    let i := str_index_of c s in
    (0 ≤ i)%Z →
    str_at i s = [c].
  Proof.
    intros i ?. unfold str_at. rewrite bool_decide_true by lia.
    assert (i = Z.to_nat i) as Hi by lia. by apply str_index_of_nonneg in Hi as [-> _].
  Qed.

  (** String Index-Of *)

End infer_slice.