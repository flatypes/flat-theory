From stdpp Require Import sets.
From flat Require Import regexes util.

Section split_regex.
  
  Fixpoint re_head_tail (r : regex) : list (charset * regex) :=
    match r with
    | re_none => []
    | re_null => []
    | re_lit C => if bool_decide (C ≡ ∅) then [] else [(C, re_null)]
    | re_concat r1 r2 =>
      ((λ '(C, r'), (C, r' ++ᵣ r2)) <$> re_head_tail r1) ++
      (if bool_decide (ε ∈ r1) then re_head_tail r2 else [])
    | re_union r1 r2 => re_head_tail r1 ++ re_head_tail r2
    | re_star r => (λ '(C, r'), (C, r' ++ᵣ re_star r)) <$> re_head_tail r
    end.

  Lemma re_head_tail_nil r :
    re_head_tail r = [] → ∀ s, s ∈ r → s = [].
  Proof.
    induction r; simpl.
    - inversion 2.
    - by inversion 2.
    - case_bool_decide as Hr; [|done]. inversion 2; subst.
      rewrite elem_of_equiv_empty in Hr. naive_solver.
    - intros Hr. inversion 1; subst.
      apply app_nil in Hr as [Hr1 Hr2]. apply fmap_nil_inv in Hr1.
      rewrite bool_decide_true in Hr2 by naive_solver.
      naive_solver.
    - intros Hr. inversion 1; subst.
      all: apply app_nil in Hr as [??]; auto.
    - intros Hr. inversion 1; subst; [done|].
      apply fmap_nil_inv in Hr. naive_solver.
  Qed.

  Lemma elem_of_re_head_tail c s r :
    c :: s ∈ r →
    ∃ C r', c ∈ C ∧ s ∈ r' ∧ (C, r') ∈ re_head_tail r.
  Proof.
    revert s. induction r as [| |?|r1 IHr1 r2 IHr2|r1 IHr1 r2 IHr2|r IHr] => s.
    all: inversion 1 as [|?|?????? Heq|?|?|?|?????? Heq]; subst.
    - eexists. exists re_null. repeat split; [done|constructor|].
      simpl. case_bool_decide as Heq.
      * rewrite elem_of_equiv_empty in Heq. naive_solver.
      * by apply elem_of_list_singleton.
    - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]].
      * edestruct IHr2 as [C [r' [? [??]]]]; eauto.
        exists C, r'. repeat split; [done..|].
        simpl. apply elem_of_app. right. by rewrite bool_decide_true.
      * edestruct IHr1 as [C [r' [? [??]]]]; eauto.
        exists C, (r' ++ᵣ r2). repeat split; [done|by constructor|].
        simpl. apply elem_of_app. left. apply elem_of_list_fmap. naive_solver.
    - edestruct IHr1 as [C [r' [? [??]]]]; eauto.
      exists C, r'. repeat split; [done..|].
      simpl. apply elem_of_app. by left.
    - edestruct IHr2 as [C [r' [? [??]]]]; eauto.
      exists C, r'. repeat split; [done..|].
      simpl. apply elem_of_app. by right.
    - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; [naive_solver|].
      edestruct IHr as [C [r' [? [??]]]]; eauto.
      exists C, (r' ++ᵣ re_star r). repeat split; [done|by constructor|].
      simpl. apply elem_of_list_fmap. naive_solver.
  Qed.

  Fixpoint re_split_at (i : nat) (r : regex) : list (regex * regex) :=
    match i with
    | 0%nat => [(re_null, r)]
    | S i' =>
      '(C, r') ← re_head_tail r;
      '(r1, r2) ← re_split_at i' r';
      [(re_lit C ++ᵣ r1, r2)]
    end.

  Lemma re_split_at_nil i r :
    re_split_at i r = [] → ∀ s, s ∈ r → length s ≤ i.
  Proof.
    intros Hr s Hs. induction i; simpl in *. { done. }
    destruct (re_head_tail r) eqn:Heq.
    - rewrite (re_head_tail_nil _ Heq s) by done. rewrite length_nil. lia.
    - admit.
  Admitted.

  Lemma elem_of_re_split_at i r s :
    i ≤ length s →
    s ∈ r →
    ∃ r1 r2, (take i s) ∈ r1 ∧ (drop i s) ∈ r2 ∧ (r1, r2) ∈ re_split_at i r.
  Proof.
    revert s r. induction i as [|i' IHi'] => s r Hi Hs.
    - rewrite take_0, drop_0. simpl.
      exists re_null, r. split; [constructor|]. split; [done | by apply elem_of_list_singleton].
    - destruct s as [|c s].
      * simpl in Hi. lia.
      * apply elem_of_re_head_tail in Hs as [C [r' [? [Hs ?]]]].
        rewrite firstn_cons, skipn_cons.
        rewrite length_cons in Hi.
        edestruct IHi' as [r1 [r2 [? [??]]]]; [|done|]; [lia|].
        exists (re_lit C ++ᵣ r1), r2.
        split. { by apply elem_of_concat_lit. }
        split. { done. }
        simpl. apply elem_of_list_bind. exists (C, r'). split; [|done].
        apply elem_of_list_bind. exists (r1, r2). split; [by apply elem_of_list_singleton | done].
  Qed.

  Definition re_take (i : nat) (r : regex) : regex := big_union (fst <$> re_split_at i r).
  Definition re_drop (i : nat) (r : regex) : regex := big_union (snd <$> re_split_at i r).

  Lemma elem_of_re_take_drop i r s :
    i ≤ length s →
    s ∈ r →
    (take i s) ∈ re_take i r ∧ (drop i s) ∈ re_drop i r.
  Proof.
    intros ? Hs.
    apply (elem_of_re_split_at i) in Hs as [r1 [r2 [? [??]]]]; [|done].
    unfold re_split_at. simpl. split.
    all: eapply elem_of_big_union; [|done].
    all: apply elem_of_list_fmap; by exists (r1, r2).
  Qed.

  Corollary elem_of_re_take i r s :
    i ≤ length s →
    s ∈ r →
    (take i s) ∈ re_take i r.
  Proof. apply elem_of_re_take_drop. Qed.

  Corollary elem_of_re_drop i r s :
    i ≤ length s →
    s ∈ r →
    (drop i s) ∈ re_drop i r.
  Proof. apply elem_of_re_take_drop. Qed.

  Definition re_take_rev (i : nat) (r : regex) : regex := re_rev (re_drop i (re_rev r)).
  Definition re_drop_rev (i : nat) (r : regex) : regex := re_rev (re_take i (re_rev r)).

  Lemma elem_of_re_take_rev i r s :
    i ≤ length s →
    s ∈ r →
    (drop (length s - i) s) ∈ re_take_rev i r.
  Admitted.

  Lemma elem_of_re_drop_rev i r s :
    i ≤ length s →
    s ∈ r →
    (take (length s - i) s) ∈ re_drop_rev i r.
  Admitted.

  Fixpoint re_split_by (c : char) (r : regex) : (list (regex * regex) * regex) :=
    match r with
    | re_none => ([], ∅)
    | re_null => ([], re_null)
    | re_lit C =>
      if bool_decide (c ∈ C) then ([(re_null, re_lit {[c]})], re_lit (C #- c))
      else ([], re_lit C)
    | re_concat r1 r2 =>
      let '(cuts1, r1') := re_split_by c r1 in
      let '(cuts2, r2') := re_split_by c r2 in
      (((λ '(r1l, r1r), (r1l, r1r ++ᵣ r2)) <$> cuts1) ++
      ((λ '(r2l, r2r), (r1' ++ᵣ r2l, r2r)) <$> cuts2), r1' ++ᵣ r2')
    | re_union r1 r2 =>
      let '(cuts1, r1') := re_split_by c r1 in
      let '(cuts2, r2') := re_split_by c r2 in
      (cuts1 ++ cuts2, r1' ∪ r2')
    | re_star r => 
      let '(cuts, r') := re_split_by c r in
      ((λ '(rl, rr), (re_star r' ++ᵣ rl, rr ++ᵣ re_star r)) <$> cuts, re_star r')
    end.

  Lemma elem_of_re_split_by_snd c r s :
    c ∉ s →
    s ∈ r →
    s ∈ (re_split_by c r).2.
  Proof.
    intros Hc. induction 1; simpl in *.
    - constructor.
    - rewrite elem_of_list_singleton in Hc.
      case_bool_decide; constructor; [by apply elem_of_charset_delete | done].
    - rewrite elem_of_app in Hc. do 2 case_match. simpl in *. constructor; auto.
    - do 2 case_match. simpl in *. apply elem_of_union. left. auto.
    - do 2 case_match. simpl in *. apply elem_of_union. right. auto.
    - case_match. simpl in *. constructor.
    - rewrite elem_of_app in Hc. case_match. simpl in *. constructor; auto.
  Qed.

  Lemma elem_of_re_split_by_fst c r s :
    s ∈ r →
    ∀ i, s !! i = Some c → c ∉ (take i s) →
      ∃ r1 r2, (take i s) ∈ r1 ∧ (drop i s) ∈ r2 ∧ (r1, r2) ∈ (re_split_by c r).1.
  Proof.
    induction 1 as [|C c'|r1 r2 ??? IHr1 ? IHr2|
      r1 r2 ?? IHr|r1 r2 ?? IHr|r|r ???? IHr1 ? IHr2] => i Hi Hp; simpl in *.
    - naive_solver.
    - apply list_lookup_singleton_Some in Hi as [-> ->].
      rewrite take_0, drop_0, bool_decide_true by done. simpl.
      exists re_null, (re_lit {[c]}). split; [constructor|].
      split. { constructor. by apply elem_of_singleton. }
      by apply elem_of_list_singleton.
    - rewrite lookup_app_Some in Hi.
      destruct Hi as [Hi|[? Hi]]; [clear IHr2 | clear IHr1].
      * assert (i ≤ length s1)%nat. { by apply Nat.lt_le_incl, lookup_lt_is_Some. }
        rewrite take_app_le, drop_app_le in * by done.
        specialize (IHr1 _ Hi) as [r1l [r1r [? [??]]]]; [done..|].
        exists r1l, (r1r ++ᵣ r2). split; [done|]. split; [by constructor|].
        do 2 case_match. simpl in *. apply elem_of_app. left.
        apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
      * rewrite take_app_ge, drop_app_ge in * by done.
        apply not_elem_of_app in Hp as [Hp1 Hp2].
        specialize (IHr2 _ Hi) as [r2l [r2r [? [??]]]]; [done..|].
        eapply elem_of_re_split_by_snd in Hp1; [|done].
        destruct (re_split_by c r1) as [? r1']. simpl in *.
        exists (r1' ++ᵣ r2l), r2r. split; [by constructor|]. split; [done|].
        case_match. simpl in *. apply elem_of_app. right.
        apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
    - specialize (IHr _ Hi) as [rl [rr [? [? ?]]]]; [done..|].
      exists rl, rr. split; [done|]. split; [done|].
      do 2 case_match. simpl in *. apply elem_of_app. by left.
    - specialize (IHr _ Hi) as [rl [rr [? [? ?]]]]; [done..|].
      exists rl, rr. split; [done|]. split; [done|].
      do 2 case_match. simpl in *. apply elem_of_app. by right.
    - naive_solver.
    - rewrite lookup_app_Some in Hi.
      destruct Hi as [Hi|[? Hi]]; [clear IHr2 | clear IHr1].
      * assert (i ≤ length s1)%nat. { by apply Nat.lt_le_incl, lookup_lt_is_Some. }
        rewrite take_app_le, drop_app_le in * by done.
        specialize (IHr1 _ Hi) as [r1l [r1r [? [??]]]]; [done|].
        destruct (re_split_by c r) as [? r1']. simpl in *.
        exists (re_star r1' ++ᵣ r1l), (r1r ++ᵣ re_star r).
        split. { rewrite <-app_nil_l at 1. constructor; [constructor | done]. }
        split. { by constructor. }
        apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
      * rewrite take_app_ge, drop_app_ge in * by done.
        apply not_elem_of_app in Hp as [Hp1 Hp2].
        specialize (IHr2 _ Hi) as [r2l [r2r [Hr2l [? IHr2]]]]; [done|].
        eapply elem_of_re_split_by_snd in Hp1; [|done].
        destruct (re_split_by c r) as [? r1']. simpl in Hp1.
        exists r2l, r2r. split; [|done].
        apply elem_of_list_fmap in IHr2 as [[? ?] [IHr2 ?]].
        inversion IHr2; subst; clear IHr2.
        inversion Hr2l; subst; clear Hr2l.
        rewrite app_assoc. constructor; [by constructor | done].
  Qed.

  Definition re_take_until (c : char) (r : regex) : regex :=
    big_union (fst <$> (re_split_by c r).1).
  Definition re_drop_until (c : char) (r : regex) : regex :=
    big_union (snd <$> (re_split_by c r).1).

  Lemma elem_of_re_take_drop_until c r s i :
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (take i s) ∈ re_take_until c r ∧ (drop i s) ∈ re_drop_until c r.
  Proof.
    intros ?? Hs.
    eapply elem_of_re_split_by_fst in Hs as [r1 [r2 [? [??]]]]; [|done..]. split.
    all: eapply elem_of_big_union; [|done].
    all: apply elem_of_list_fmap; by exists (r1, r2).
  Qed.

  Corollary elem_of_re_take_until c r s i :
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (take i s) ∈ re_take_until c r.
  Proof. apply elem_of_re_take_drop_until. Qed.

  Corollary elem_of_re_drop_until c r s i :
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (drop i s) ∈ re_drop_until c r.
  Proof. apply elem_of_re_take_drop_until. Qed.

  Definition re_take_until_shr (c : char) (k : nat) (r : regex) : regex :=
    re_take_until c r ++ᵣ re_take k (re_drop_until c r).

  Definition re_take_until_shl (c : char) (k : nat) (r : regex) : regex :=
    re_drop_rev k (re_take_until c r).

  Definition re_drop_until_shr (c : char) (k : nat) (r : regex) : regex :=
    re_drop k (re_drop_until c r).

  Definition re_drop_until_shl (c : char) (k : nat) (r : regex) : regex :=
    re_take_rev k (re_take_until c r) ++ᵣ re_drop_until c r.

  Lemma elem_of_re_take_until_shr c k r s i :
    i + k < length s →
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (take (i + k) s) ∈ re_take_until_shr c k r.
  Proof.
    intros. unfold re_take_until_shr. rewrite <-take_take_drop.
    constructor.
    - by apply elem_of_re_take_until.
    - apply elem_of_re_take. { rewrite length_drop. lia. }
      by apply elem_of_re_drop_until.
  Qed.

  Lemma elem_of_re_take_until_shl c k r s i :
    k < i →
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (take (i - k) s) ∈ re_take_until_shl c k r.
  Proof.
    intros. unfold re_take_until_shl.
    assert (i < length s). { by apply lookup_lt_is_Some. }
    assert (take (i - k) s = take (length (take i s) - k) (take i s)) as ->.
    { by rewrite length_take, min_l, take_take, min_l by lia. }
    apply elem_of_re_drop_rev. { rewrite length_take. lia. }
    by apply elem_of_re_take_until.
  Qed.

  Lemma elem_of_re_drop_until_shr c k r s i :
    i + k < length s →
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (drop (i + k) s) ∈ re_drop_until_shr c k r.
  Proof.
    intros. unfold re_drop_until_shr. rewrite <-drop_drop.
    apply elem_of_re_drop. { rewrite length_drop. lia. }
    by apply elem_of_re_drop_until.
  Qed.

  Lemma elem_of_re_drop_until_shl c k r s i :
    k < i →
    s !! i = Some c →
    c ∉ take i s →
    s ∈ r →
    (drop (i - k) s) ∈ re_drop_until_shl c k r.
  Proof.
    intros. unfold re_drop_until_shl.
    assert (i < length s). { by apply lookup_lt_is_Some. }
    rewrite <-(drop_take_drop _ _ i) by lia. constructor.
    - assert (length (take i s) = i) as Hi. { rewrite length_take. lia. }
      rewrite <-Hi at 1. apply elem_of_re_take_rev. { lia. }
      by apply elem_of_re_take_until.
    - by apply elem_of_re_drop_until.
  Qed.

End split_regex.