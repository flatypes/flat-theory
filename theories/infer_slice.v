From stdpp Require Import sets.
From flat Require Import regexes util.

Section infer_slice.
  Local Open Scope Z_scope.

  Implicit Type s : str.
  Implicit Type r : regex.

  Fixpoint re_hd_tl (r : regex) : list (charset * regex) :=
    match r with
    | re_none => []
    | re_null => []
    | re_lit C => if bool_decide (C ≡ ∅) then [] else [(C, re_null)]
    | re_concat r1 r2 =>
      ((λ '(C, r'), (C, r' ++ᵣ r2)) <$> re_hd_tl r1) ++
      (if bool_decide (ε ∈ r1) then re_hd_tl r2 else [])
    | re_union r1 r2 => re_hd_tl r1 ++ re_hd_tl r2
    | re_star r => (λ '(C, r'), (C, r' ++ᵣ re_star r)) <$> re_hd_tl r
    end.

  Lemma elem_of_re_hd_tl c s r :
    c :: s ∈ r →
    ∃ C r', c ∈ C ∧ s ∈ r' ∧ (C, r') ∈ re_hd_tl r.
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

  Fixpoint re_take_drop (r : regex) (i : nat) : list (regex * regex) :=
    match i with
    | 0%nat => [(re_null, r)]
    | S i' =>
      '(C, r') ← re_hd_tl r;
      '(r1, r2) ← re_take_drop r' i';
      [(re_lit C ++ᵣ r1, r2)]
    end.

  Lemma elem_of_re_take_drop s r i :
    s ∈ r →
    (0 ≤ i < length s)%nat →
    ∃ r1 r2, (take i s) ∈ r1 ∧ (drop i s) ∈ r2 ∧ (r1, r2) ∈ re_take_drop r i.
  Proof.
    revert s r. induction i as [|i' IHi'] => s r Hs Hi.
    - rewrite take_0, drop_0. simpl.
      exists re_null, r. split; [constructor|]. split; [done | by apply elem_of_list_singleton].
    - destruct s as [|c s].
      * simpl in Hi. lia.
      * apply elem_of_re_hd_tl in Hs as [C [r' [? [Hs ?]]]].
        rewrite firstn_cons, skipn_cons.
        specialize (IHi' _ _ Hs) as [r1 [r2 [? [??]]]]. { simpl in Hi. lia. }
        exists (re_lit C ++ᵣ r1), r2.
        split. { by apply elem_of_concat_lit. }
        split. { done. }
        simpl. apply elem_of_list_bind. exists (C, r'). split; [|done].
        apply elem_of_list_bind. exists (r1, r2). split; [by apply elem_of_list_singleton | done].
  Qed.

  Definition re_split_at_index (r : regex) (i : nat) : (regex * regex) :=
    let splits := re_take_drop r i in
    (union_many (fst <$> splits), union_many (snd <$> splits)).

  Lemma re_split_at_index_spec s r i :
    s ∈ r →
    (0 ≤ i < length s)%nat →
    (take i s) ∈ (re_split_at_index r i).1 ∧ (drop i s) ∈ (re_split_at_index r i).2.
  Proof.
    intros Hs ?.
    apply (elem_of_re_take_drop s r i) in Hs as [r1 [r2 [? [??]]]]; [|done].
    unfold re_split_at_index. simpl. split.
    all: eapply elem_of_union_many; [|done].
    all: apply elem_of_list_fmap; by exists (r1, r2).
  Qed.

  Lemma infer_substr_begin_const s i r :
    s ∈ r →
    0 ≤ i < length s →
    str_substr_begin s i ∈ (re_split_at_index r (Z.to_nat i)).2.
  Proof.
    intros Hs ?.
    apply (re_split_at_index_spec s r (Z.to_nat i)) in Hs as [??]; [|lia].
    unfold str_substr_begin. rewrite bool_decide_true; done.
  Qed.

  Lemma infer_substr_until_const s i r :
    s ∈ r →
    0 ≤ i < length s →
    str_substr_until s i ∈ (re_split_at_index r (Z.to_nat i)).1.
  Proof.
    intros Hs ?.
    apply (re_split_at_index_spec s r (Z.to_nat i)) in Hs as [??]; [|lia].
    unfold str_substr_until. done.
  Qed.

  Fixpoint re_find_char (r : regex) (c : char) : (list (regex * regex) * regex) :=
    match r with
    | re_none => ([], ∅)
    | re_null => ([], re_null)
    | re_lit C =>
      if bool_decide (c ∈ C) then ([(re_null, re_lit {[c]})], re_lit (C #- c))
      else ([], re_lit C)
    | re_concat r1 r2 =>
      let '(cuts1, r1') := re_find_char r1 c in
      let '(cuts2, r2') := re_find_char r2 c in
      (((λ '(r1l, r1r), (r1l, r1r ++ᵣ r2)) <$> cuts1) ++
      ((λ '(r2l, r2r), (r1' ++ᵣ r2l, r2r)) <$> cuts2), r1' ++ᵣ r2')
    | re_union r1 r2 =>
      let '(cuts1, r1') := re_find_char r1 c in
      let '(cuts2, r2') := re_find_char r2 c in
      (cuts1 ++ cuts2, r1' ∪ r2')
    | re_star r => 
      let '(cuts, r') := re_find_char r c in
      ((λ '(rl, rr), (re_star r' ++ᵣ rl, rr ++ᵣ re_star r)) <$> cuts, re_star r')
    end.

  Lemma re_find_char_None s r c :
    s ∈ r →
    c ∉ s →
    s ∈ (re_find_char r c).2.
  Proof.
    induction 1 as [|C c'|r1 r2|r1 r2|r1 r2|r|r] => Hc; simpl in *.
    - constructor.
    - rewrite elem_of_list_singleton in Hc.
      case_bool_decide; constructor; [by apply elem_of_charset_delete | done].
    - rewrite elem_of_app in Hc.
      destruct (re_find_char r1 c) as [??]. destruct (re_find_char r2 c) as [??]. simpl in *.
      constructor; auto.
    - destruct (re_find_char r1 c) as [??]. destruct (re_find_char r2 c) as [??]. simpl in *.
      apply elem_of_union. auto.
    - destruct (re_find_char r1 c) as [??]. destruct (re_find_char r2 c) as [??]. simpl in *.
      apply elem_of_union. auto.
    - destruct (re_find_char r c) as [??]. simpl.
      constructor.
    - rewrite elem_of_app in Hc.
      destruct (re_find_char r c) as [??]. simpl in *.
      constructor; auto.
  Qed.

  Lemma re_find_char_Some s r c :
    s ∈ r →
    ∀ i, s !! i = Some c → c ∉ (take i s) →
      ∃ r1 r2, (take i s) ∈ r1 ∧ (drop i s) ∈ r2 ∧ (r1, r2) ∈ (re_find_char r c).1.
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
        destruct (re_find_char r1 c) as [??]. destruct (re_find_char r2 c) as [??]. simpl in *.
        apply elem_of_app. left.
        apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
      * rewrite take_app_ge, drop_app_ge in * by done.
        apply not_elem_of_app in Hp as [Hp1 Hp2].
        specialize (IHr2 _ Hi) as [r2l [r2r [? [??]]]]; [done..|].
        eapply re_find_char_None in Hp1; [|done].
        destruct (re_find_char r1 c) as [? r1']. simpl in *.
        exists (r1' ++ᵣ r2l), r2r. split; [by constructor|]. split; [done|].
        destruct (re_find_char r2 c) as [??]. simpl in *.
        apply elem_of_app. right.
        apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
    - specialize (IHr _ Hi) as [rl [rr [? [? ?]]]]; [done..|].
      exists rl, rr. split; [done|]. split; [done|].
      destruct (re_find_char r1 c) as [??]. destruct (re_find_char r2 c) as [??]. simpl in *.
      apply elem_of_app. by left.
    - specialize (IHr _ Hi) as [rl [rr [? [? ?]]]]; [done..|].
      exists rl, rr. split; [done|]. split; [done|].
      destruct (re_find_char r1 c) as [??]. destruct (re_find_char r2 c) as [??]. simpl in *.
      apply elem_of_app. by right.
    - naive_solver.
    - rewrite lookup_app_Some in Hi.
      destruct Hi as [Hi|[? Hi]]; [clear IHr2 | clear IHr1].
      * assert (i ≤ length s1)%nat. { by apply Nat.lt_le_incl, lookup_lt_is_Some. }
        rewrite take_app_le, drop_app_le in * by done.
        specialize (IHr1 _ Hi) as [r1l [r1r [? [??]]]]; [done|].
        destruct (re_find_char r c) as [? r1']. simpl in *.
        exists (re_star r1' ++ᵣ r1l), (r1r ++ᵣ re_star r).
        split. { rewrite <-app_nil_l at 1. constructor; [constructor | done]. }
        split. { by constructor. }
        apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
      * rewrite take_app_ge, drop_app_ge in * by done.
        apply not_elem_of_app in Hp as [Hp1 Hp2].
        specialize (IHr2 _ Hi) as [r2l [r2r [Hr2l [? IHr2]]]]; [done|].
        eapply re_find_char_None in Hp1; [|done].
        destruct (re_find_char r c) as [? r1']. simpl in Hp1.
        exists r2l, r2r. split; [|done].
        apply elem_of_list_fmap in IHr2 as [[? ?] [IHr2 ?]].
        inversion IHr2; subst; clear IHr2.
        inversion Hr2l; subst; clear Hr2l.
        rewrite app_assoc. constructor; [by constructor | done].
  Qed.

  Definition re_split_at_char (r : regex) (c : char) : (regex * regex) :=
    let (splits, _) := re_find_char r c in
    (union_many (fst <$> splits), union_many (snd <$> splits)).

  Lemma infer_substr_begin_index_of s c r :
    s ∈ r →
    let i := str_index_of s c in
    0 ≤ i < length s →
    str_substr_begin s i ∈ (re_split_at_char r c).2.
  Proof.
    intros Hs i Hi.
    unfold str_substr_begin. rewrite bool_decide_true by done.
    destruct Hi as [Hi ?].
    apply str_index_of_ge_0, str_find_Some in Hi as [Hi ?].
    eapply re_find_char_Some in Hi as [r1 [r2 [? [??]]]]; [|done..].
    unfold re_split_at_char. destruct (re_find_char r c) as [??]. simpl in *.
    eapply elem_of_union_many; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Lemma infer_substr_until_index_of s c r :
    s ∈ r →
    let i := str_index_of s c in
    0 ≤ i < length s →
    str_substr_until s i ∈ (re_split_at_char r c).1.
  Proof.
    intros Hs i Hi. unfold str_substr_until.
    destruct Hi as [Hi ?].
    apply str_index_of_ge_0, str_find_Some in Hi as [Hi ?].
    eapply re_find_char_Some in Hi as [r1 [r2 [? [??]]]]; [|done..].
    unfold re_split_at_char. destruct (re_find_char r c) as [??]. simpl in *.
    eapply elem_of_union_many; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

End infer_slice.