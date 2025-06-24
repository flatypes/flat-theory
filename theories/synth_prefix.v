From stdpp Require Import sets.
From flat Require Import regexes.

Section synth_prefix.

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
    | re_concat r1 r2 => (derive c r1 ⧺ r2) ∪ (if bool_decide ([] ∈ r1) then derive c r2 else ∅)
    | re_union r1 r2 => derive c r1 ∪ derive c r2
    | re_star r => derive c r ⧺ re_star r
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
    bool_decide (derive_ext t r ≡ ∅) = true →
    ¬ (t `prefix_of` s).
  Proof.
    rewrite bool_decide_eq_true.
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
    bool_decide (derive_ext (reverse t) (re_rev r) ≡ ∅) = true →
    ¬ (t `suffix_of` s).
  Proof.
    intros Hs ?. rewrite suffix_prefix_reverse.
    apply elem_of_re_rev in Hs. by eapply infer_prefix_never.
  Qed.

  Fixpoint re_find (c : char) (r : regex) : list (regex * regex) :=
    match r with
    | re_none => []
    | re_null => []
    | re_lit C => if bool_decide (c ∈ C) then [(re_null, re_lit C)] else []
    | re_concat r1 r2 => 
      ((λ '(r1l, r1r), (r1l, r1r ⧺ r2)) <$> re_find c r1) ++
      ((λ '(r2l, r2r), (r1 ⧺ r2l, r2r)) <$> re_find c r2)
    | re_union r1 r2 => re_find c r1 ++ re_find c r2
    | re_star r => 
      (λ '(rl, rr), (re_star r ⧺ rl, rr ⧺ re_star r)) <$> re_find c r
    end.

  Lemma elem_of_re_find s r i c :
    s ∈ r →
    str_at i s = [c] →
    ∃ r1 r2, (r1, r2) ∈ re_find c r ∧ str_take i s ∈ r1 ∧ str_drop i s ∈ r2.
  Proof.
    intros Hs. revert i c.
    induction Hs as [|C c'|r1 r2 s1 s2 ? IHr1 ? IHr2|
      r1 r2 s1 s2 IHr|r1 r2 s1 s2 IHr|?|r s1 s2 ?? IHr1 ? IHr2] => i c Hi.
    - apply str_at_singleton_lt_length in Hi. rewrite length_nil in Hi. lia.
    - apply str_at_singleton_inv in Hi as [-> ->].
      simpl. rewrite str_take_0, str_drop_0, bool_decide_true by done.
      exists re_null, (re_lit C). repeat split; [set_solver | constructor | by constructor].
    - apply str_at_concat_inv in Hi as [[? Hi]|[? Hi]].
      * clear IHr2. apply IHr1 in Hi as [r1l [r1r [? [??]]]]. exists r1l, (r1r ⧺ r2).
        split. { simpl. rewrite elem_of_app. left. rewrite elem_of_list_fmap.
                 eexists. split; [|done]. done. }
        split. { by rewrite str_take_app_l by lia. }
        rewrite str_drop_app_l by lia. by constructor.
      * clear IHr1. apply IHr2 in Hi as [r2l [r2r [? [??]]]]. exists (r1 ⧺ r2l), r2r.
        split. { simpl. rewrite elem_of_app. right. rewrite elem_of_list_fmap.
                 eexists. split; [|done]. done. }
        split. { rewrite str_take_app_r by lia. by constructor. }
        by rewrite str_drop_app_r by lia.
    - set_solver.
    - set_solver.
    - apply str_at_singleton_lt_length in Hi. rewrite length_nil in Hi. lia.
    - apply str_at_concat_inv in Hi as [[? Hi]|[? Hi]].
      * clear IHr2. apply IHr1 in Hi as [r1l [r1r [? [??]]]].
        exists (re_star r ⧺ r1l), (r1r ⧺ re_star r).
        split. { simpl. rewrite elem_of_list_fmap. eexists. split; [|done]. done. }
        split. { rewrite str_take_app_l by lia.
          rewrite <-app_nil_l at 1. constructor; [constructor | done]. }
        rewrite str_drop_app_l by lia. by constructor.
      * clear IHr1. apply IHr2 in Hi as [r1 [r2 [Hr1r2 [Hs1l ?]]]].
        exists r1, r2. split. { done. }
        split. { rewrite str_take_app_r by lia.
          simpl in Hr1r2. apply elem_of_list_fmap in Hr1r2 as [[??] [Hr1 ?]].
          inv Hr1. inv Hs1l. rewrite app_assoc. constructor; [by constructor | done]. }
        by rewrite str_drop_app_r by lia.
  Qed.

  Lemma infer_infix_never s r c t :
    s ∈ r →
    Forall (λ r', bool_decide (derive_ext (c :: t) r' ≡ ∅) = true) (snd <$> re_find c r) →
    ¬ ((c :: t) `infix_of` s).
  Proof.
    intros ? H [t1 [t2 ?]].
    assert (str_at (length t1) s = [c]) as Hc.
    { rewrite str_at_lookup_Some by lia. subst. setoid_rewrite list_lookup_middle; [done|lia]. }
    apply (elem_of_re_find _ r) in Hc as [? [r' [? [? Hs']]]]; [|done].
    assert (r' ∈ (re_find c r).*2) as Hr'.
    { apply elem_of_list_fmap. eexists. split; [|done]. done. }
    rewrite Forall_forall in H. specialize (H _ Hr'). rewrite bool_decide_eq_true in H.
    assert (str_drop (length t1) s = (c :: t) ++ t2) as Heq.
    { unfold str_drop. rewrite bool_decide_true by lia. subst. by rewrite drop_app_length' by lia. }
    rewrite Heq in Hs'. apply elem_of_derive_ext in Hs'. set_solver.
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

End synth_prefix.