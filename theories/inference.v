From stdpp Require Import list sets.
From flat Require Import regexes ranges.


Ltac unfold_str_drop :=
  unfold str_drop in *; repeat (rewrite bool_decide_true in * by lia).

(** * Prefix, Suffix, and Infix *)

Section infer_test.

  Implicit Type (s t : str) (σ : char) (r : regex).

  Lemma infer_prefix_false_sound s r t :
    s ∈ r →
    d_str t r ≡ ∅ →
    ¬ (t ⊑ s).
  Proof.
    intros Hs ? Hp. apply str_prefix_spec in Hp as [? ->]. apply elem_of_d_str in Hs. set_solver.
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

  Local Open Scope Z_scope.

  (** Lemma 4.1 *)
  Lemma elem_of_re_take_1 s r :
    s ∈ r →
    str_take s 1 ∈ re_take_1 r.
  Proof.
    unfold str_take. induction 1; simpl.
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

  Fixpoint re_prefix_forall (t : str) (r : regex) : bool :=
    match t with
    | [] => true
    | σ :: t' => bool_decide (re_take_1 r ≡ {[σ]}) && re_prefix_forall t' (d_char σ r)
    end.
  
  (** Lemma 4.2; infer_prefix_true_sound *)
  Lemma re_prefix_forall_spec s r t :
    s ∈ r →
    re_prefix_forall t r →
    t ⊑ s.
  Proof.
    revert r. induction t as [|σ t'] => r Hs Ht; [done|].
    simpl in Ht. apply andb_True in Ht as [Hσ ?]. apply bool_decide_spec in Hσ.
    apply elem_of_re_take_1 in Hs. set_solver.
  Qed.

  Fixpoint re_split (σ : char) (r : regex) : list (regex * regex) :=
    match r with
    | re_none => []
    | re_null => []
    | re_lit C => if bool_decide (σ ∈ C) then [(re_null, re_lit C)] else []
    | re_concat r1 r2 => 
      ((λ '(r1l, r1r), (r1l, r1r ⧺ r2)) <$> re_split σ r1) ++
      ((λ '(r2l, r2r), (r1 ⧺ r2l, r2r)) <$> re_split σ r2)
    | re_union r1 r2 => re_split σ r1 ++ re_split σ r2
    | re_star r => 
      (λ '(rl, rr), (re_star r ⧺ rl, rr ⧺ re_star r)) <$> re_split σ r
    end.

  (** Lemma 4.3 *)
  Lemma elem_of_re_split s r i σ :
    s ∈ r →
    s[i] = [σ] →
    ∃ r1 r2, (r1, r2) ∈ re_split σ r ∧ s[:i] ∈ r1 ∧ s[i:] ∈ r2.
  Proof.
    intros Hs. revert i σ.
    induction Hs as [|C|r1 r2 s1 s2 ? IHr1 ? IHr2|
      r1 r2 s1 s2 IHr|r1 r2 s1 s2 IHr|?|r s1 s2 ?? IHr1 ? IHr2] => i σ Hi.
    - by apply char_at_lookup_Some in Hi as [??].
    - apply char_at_inv_singleton in Hi as [-> ->].
      simpl. rewrite bool_decide_true by done.
      unfold str_take, str_drop. rewrite bool_decide_true, take_0, drop_0 by lia.
      exists re_null, (re_lit C). repeat split; [set_solver | constructor | by constructor].
    - apply char_at_inv_app in Hi as [[? Hi]|[? Hi]].
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
    - by apply char_at_lookup_Some in Hi as [??].
    - apply char_at_inv_app in Hi as [[? Hi]|[? Hi]].
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
  
  Definition re_split_suffix (σ : char) (r : regex) : regex := ⋃ (snd <$> re_split σ r).

  Lemma elem_of_re_split_suffix s r i σ :
    s ∈ r →
    s[i] = [σ] →
    s[i:] ∈ re_split_suffix σ r.
  Proof.
    intros ? Hi.
    eapply elem_of_re_split in Hi as [r1 [r2 [? [??]]]]; [|done].
    apply elem_of_union_list. exists r2. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Lemma infer_infix_false_sound t σ t' s r :
    t = σ :: t' →
    s ∈ r →
    d_str t (re_split_suffix σ r) ≡ ∅ →
    ¬ (t `in` s).
  Proof.
    intros -> Hs ? Hi. apply str_infix_spec in Hi as [i [? [? Hi]]].
    assert (s[i] = σ).
    { apply lookup_Some_char_at; [lia|]. unfold_str_drop.
      apply (f_equal (λ s, s !! 0%nat)) in Hi. simpl in Hi. rewrite <-Hi.
      setoid_rewrite lookup_drop. f_equal. lia. }
    eapply elem_of_re_split_suffix in Hs; [|done]. rewrite Hi in Hs. apply elem_of_d_str in Hs.
    set_solver.
  Qed.

  Fixpoint re_have_forall (σ : char) (r : regex) : bool :=
    match r with
    | re_none => false
    | re_null => false
    | re_lit C => bool_decide (C ≡ {[σ]})
    | re_concat r1 r2 => re_have_forall σ r1 || re_have_forall σ r2
    | re_union r1 r2 => re_have_forall σ r1 && re_have_forall σ r2
    | re_star r => false
    end.

  (** Lemma 4.4 *)
  Lemma elem_of_re_have_forall s r σ :
    s ∈ r →
    re_have_forall σ r →
    σ ∈ s.
  Proof.
    induction 1; simpl; try naive_solver.
    - rewrite bool_decide_spec. set_solver.
    - intros. apply elem_of_app. naive_solver.
  Qed.

  Lemma infer_infix_true_sound t σ t' s r :
    t = σ :: t' →
    s ∈ r →
    re_have_forall σ r →
    re_prefix_forall t (re_split_suffix σ r) →
    t `in` s.
  Proof.
    intros -> Hs Hh ?.
    eapply elem_of_re_have_forall in Hh; [|done]. apply elem_of_list_lookup in Hh as [i Hi].
    unfold str_infix. apply bool_decide_spec, (find_nonneg i).
    eapply str_prefix_spec, re_prefix_forall_spec; [|done].
    apply elem_of_re_split_suffix; [done|]. apply lookup_Some_char_at; [lia|].
    rewrite <-Hi. f_equal. lia.
  Qed.

End infer_test.

Section infer_substr.

  Implicit Type (s t : str) (σ : char) (i j : Z) (r : regex).

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

  (** Lemma 4.5 *)
  Lemma elem_of_re_drop_1 s r :
    s ∈ r →
    str_drop s 1 ∈ re_drop_1 r.
  Proof.
    unfold_str_drop. induction 1; simpl.
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

  Fixpoint re_drop (n : nat) (r : regex) : regex :=
    match n with
    | 0 => r
    | S n' => re_drop n' (re_drop_1 r)
    end.

  (** Lemma 4.6 *)
  Lemma elem_of_re_drop s r (n : nat) :
    s ∈ r →
    str_drop s n ∈ re_drop n r.
  Proof.
    unfold_str_drop.
    revert s r. induction n as [|n IHn] => s r ?; simpl. { by rewrite drop_0. }
    replace (Z.to_nat (S n)) with (1 + n) by lia.
    rewrite <-drop_drop. rewrite Nat2Z.id in IHn. apply IHn. by apply elem_of_re_drop_1.
  Qed.

  Fixpoint re_take (n : nat) (r : regex) : regex :=
    match n with
    | 0 => re_null
    | S n' => re_take_1 r ⧺ re_take n' (re_drop_1 r)
    end.

  (** Lemma 4.7 *)
  Lemma elem_of_re_take s r (n : nat) :
    s ∈ r →
    str_take s n ∈ re_take n r.
  Proof.
    unfold str_take.
    revert s r. induction n as [|n IHn] => s r ?; simpl. { rewrite take_0. constructor. }
    replace (Z.to_nat (S n)) with (1 + n) by lia.
    rewrite <-take_take_drop. constructor.
    + by apply elem_of_re_take_1.
    + rewrite Nat2Z.id in IHn. apply IHn. by apply elem_of_re_drop_1.
  Qed.

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

  Definition re_find (σ : char) (r : regex) : list (regex * regex) :=
    '(r1, r2) ← re_split σ r;
    let r1' := re_exclude σ r1 in
    if bool_decide (r1' ≢ ∅) then [(r1', re_lit {[σ]} ⧺ re_drop_1 r2)] else [].

  Local Open Scope Z_scope.

  (** Lemma 4.8 *)
  Lemma elem_of_re_find s r i σ :
    s ∈ r →
    0 ≤ i →
    find s σ = i →
    ∃ r1 r2, (r1, r2) ∈ re_find σ r ∧ s[:i] ∈ r1 ∧ s[i:] ∈ r2.
  Proof.
    intros ?? Hi.
    apply find_char_at in Hi as [Hi ?]; [|lia].
    edestruct elem_of_re_split as [r1 [r2 [? [??]]]]; [done..|].
    exists (re_exclude σ r1), (re_lit {[σ]} ⧺ re_drop_1 r2).
    assert (s[:i] ∈ re_exclude σ r1). { by apply elem_of_re_exclude. }
    repeat split; [|done|].
    + unfold re_find. apply elem_of_list_bind. eexists. split; [|done].
      case_match. rewrite bool_decide_true; set_solver.
    + unfold str_drop in *. rewrite bool_decide_true in * by lia.
      erewrite drop_S by (by apply char_at_lookup_Some).
      apply elem_of_concat_lit; [set_solver|].
      replace (S (Z.to_nat i)) with ((Z.to_nat i) + 1)%nat by lia. rewrite <-drop_drop.
      by apply elem_of_re_drop_1.
  Qed.

  Definition re_find_suffix (σ : char) (r : regex) : regex := ⋃ (snd <$> re_find σ r).
  Definition re_find_prefix (σ : char) (r : regex) : regex := ⋃ (fst <$> re_find σ r).

  Lemma elem_of_re_find_suffix s r σ i :
    s ∈ r →
    0 ≤ i →
    find s σ = i →
    s[i:] ∈ re_find_suffix σ r.
  Proof.
    intros ?? Hi.
    eapply elem_of_re_find in Hi as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r2. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Lemma elem_of_re_find_prefix s r σ i :
    s ∈ r →
    0 ≤ i →
    find s σ = i →
    s[:i] ∈ re_find_prefix σ r.
  Proof.
    intros ?? Hi.
    eapply elem_of_re_find in Hi as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r1. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Definition re_split_str (σ : char) (t' : str) (r : regex) : list (regex * regex) :=
    '(r1, r2) ← re_split σ r;
    let t := σ :: t' in
    let r2' := d_str t r2 in
    if bool_decide (r2' ≢ ∅) then [(r1, {[t]} ⧺ r2')] else [].

  Lemma elem_of_re_split_str s r t σ t' i :
    s ∈ r →
    t = σ :: t' →
    0 ≤ i →
    t ⊑ s[i:] →
    ∃ r1 r2, (r1, r2) ∈ re_split_str σ t' r ∧ s[:i] ∈ r1 ∧ s[i:] ∈ r2.
  Proof.
    intros ??? Ht.
    apply str_prefix_spec in Ht as [s' Ht].
    assert (s[i] = σ) as Hi. { unfold char_at. rewrite Ht. naive_solver. }
    eapply elem_of_re_split in Hi as [r1 [r2 [? [??]]]]; [|done].
    exists r1, ({[t]} ⧺ d_str t r2). 
    assert (s' ∈ d_str t r2). { apply elem_of_d_str. by rewrite <-Ht. }
    repeat split; [|done|].
    + unfold re_split_str. apply elem_of_list_bind. eexists. split; [|done]. case_match.
      rewrite bool_decide_true; set_solver.
    + rewrite Ht. constructor; [set_solver | done].
  Qed.

  Definition re_split_str_suffix (σ : char) (t' : str) (r : regex) : regex :=
    ⋃ (snd <$> re_split_str σ t' r).
  Definition re_split_str_prefix (σ : char) (t' : str) (r : regex) : regex :=
    ⋃ (fst <$> re_split_str σ t' r).
  
  Lemma elem_of_re_split_str_suffix s r t σ t' i :
    s ∈ r →
    t = σ :: t' →
    0 ≤ i →
    t ⊑ s[i:] →
    s[i:] ∈ re_split_str_suffix σ t' r.
  Proof.
    intros ??? Ht.
    eapply elem_of_re_split_str in Ht as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r2. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Lemma elem_of_re_split_str_prefix s r t σ t' i :
    s ∈ r →
    t = σ :: t' →
    0 ≤ i →
    t ⊑ s[i:] →
    s[:i] ∈ re_split_str_prefix σ t' r.
  Proof.
    intros ??? Ht.
    eapply elem_of_re_split_str in Ht as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r1. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  (** Abstract index. *)
  Inductive index : Type :=
    | index_l : nat → index
    | index_r : nat → index
    | index_at : str → index
    .

  (** Semantic interpretation: concretize [κ] as an index of a given string [s]. *)
  Definition index_con (κ : index) (s : str) : Z :=
    match κ with
    | index_l k => k
    | index_r k => length s - k
    | index_at t => find s t
    end.
  Notation "⟦ κ ⟧ s" := (index_con κ s) (at level 20, no associativity).

  Definition re_drop_index (κ : index) (r : regex) : regex :=
    match κ with
    | index_l k => re_drop k r
    | index_r k => re_rev (re_take k (re_rev r))
    | index_at ([]) => r
    | index_at ([σ]) => re_find_suffix σ r
    | index_at (σ :: t') => re_split_str_suffix σ t' r
    end.
  
  Definition re_take_index (κ : index) (r : regex) : regex :=
    match κ with
    | index_l k => re_take k r
    | index_r k => re_rev (re_drop k (re_rev r))
    | index_at ([]) => re_null
    | index_at ([σ]) => re_find_prefix σ r
    | index_at (σ :: t') => re_split_str_prefix σ t' r
    end.

  Lemma infer_drop_index_sound s r n κ :
    s ∈ r →
    0 ≤ n →
    ⟦κ⟧ s = n →
    str_drop s n ∈ re_drop_index κ r.
  Proof.
    intros ??. destruct κ as [k|k|t]; intros Hn; simpl; repeat case_match; simpl in *.
    - rewrite <-Hn. by apply elem_of_re_drop.
    - rewrite <-Hn, <-reverse_involutive at 1.
      apply elem_of_re_rev. unfold_str_drop. rewrite reverse_drop.
      replace (length s - Z.to_nat (length s - k))%nat with k%nat by lia.
      rewrite <-Nat2Z.id at 1. by apply elem_of_re_take, elem_of_re_rev.
    - unfold_str_drop. apply find_inv_empty in Hn as [?|?]; subst; [rewrite drop_nil|]; done.
    - by apply elem_of_re_find_suffix.
    - apply find_occur in Hn; [|lia]. eapply elem_of_re_split_str_suffix; [done..|].
      unfold str_prefix. naive_solver.
  Qed.

  Lemma fold_str_drop (n : nat) s :
    drop n s = str_drop s n.
  Proof.
    unfold_str_drop. f_equal. lia.
  Qed.

  Lemma infer_take_index_sound s r n κ :
    s ∈ r →
    0 ≤ n →
    ⟦κ⟧ s = n →
    str_take s n ∈ re_take_index κ r.
  Proof.
    intros Hs ?. destruct κ as [k|k|t]; intros Hn; simpl; repeat case_match; simpl in *.
    - rewrite <-Hn. by apply elem_of_re_take.
    - rewrite <-Hn, <-reverse_involutive at 1.
      apply elem_of_re_rev. unfold str_take.
      rewrite reverse_take. replace (length s - Z.to_nat (length s - k))%nat with k%nat by lia.
      rewrite fold_str_drop. by apply elem_of_re_drop, elem_of_re_rev.
    - unfold str_take. apply find_inv_empty in Hn as [?|?]; subst; [rewrite take_nil|]; constructor.
    - by apply elem_of_re_find_prefix.
    - apply find_occur in Hn; [|lia]. eapply elem_of_re_split_str_prefix; [done..|].
      unfold str_prefix. naive_solver.
  Qed.

  Inductive index_neg : index → Prop :=
    | index_neg_r k : index_neg (index_r k)
    | index_neg_at t : index_neg (index_at t)
    .

  (** Lemma 4.10 *)
  Lemma index_shift_suffix κ s n :
    index_neg κ →
    0 ≤ n < ⟦ κ ⟧ s →
    ⟦ κ ⟧ (s[n:]) = ⟦ κ ⟧ s - n.
  Proof.
    inversion 1; subst; simpl; intros.
    - unfold_str_drop. rewrite length_drop. lia.
    - apply occur_find; [lia|]. unfold occur. split.
      + unfold_str_drop. rewrite drop_drop, fold_str_drop. apply find_occur; lia.
      + intros k Hk Ht. unfold_str_drop. rewrite length_drop in Hk. rewrite drop_drop in Ht.
        apply Z.le_sub_le_add_l. pose (find_le s t). eapply find_first_occur; [lia|done|lia|].
        destruct Ht as [s' Hs']. exists s'. unfold_str_drop. rewrite <-Hs'. f_equal. lia.
  Qed.

  Lemma infer_substr_index_take_drop_sound s r (i j : nat) κi κj :
    s ∈ r →
    i < j →
    ⟦ κi ⟧ s = i →
    ⟦ κj ⟧ s = j →
    index_neg κj →
    s[i:j] ∈ re_take_index κj (re_drop_index κi r).
  Proof.
    intros. unfold substr. apply infer_take_index_sound; [|lia|].
    + apply infer_drop_index_sound; [done|lia|done].
    + rewrite index_shift_suffix; [lia|done|lia].
  Qed.

  Lemma infer_substr_index_drop_take_1_sound s r (i j : nat) :
    s ∈ r →
    i < j →
    s[i:j] ∈ re_drop i (re_take j r).
  Proof.
    intros. rewrite substr_alt by lia. by apply elem_of_re_drop, elem_of_re_take.
  Qed.

  Lemma prefix_take_ge {A : Type} (k l : list A) n :
    k `prefix_of` l →
    (length k ≤ n)%nat →
    k `prefix_of` take n l.
  Proof.
    intros [l' ->] ?. rewrite take_app. apply prefix_app_r. by rewrite take_ge by lia.
  Qed.

  Lemma infer_substr_index_drop_take_2_sound s r (i j : nat) t :
    s ∈ r →
    i + length t ≤ j →
    ⟦ index_at t ⟧ s = i →
    s[i:j] ∈ re_drop_index (index_at t) (re_take j r).
  Proof.
    intros ?? Hi. rewrite substr_alt by lia. apply infer_drop_index_sound; [|lia|].
    { by apply elem_of_re_take. }
    simpl in *. rewrite <-Hi. apply occur_find; [lia|]. unfold occur. split.
    + unfold_str_drop. unfold str_take. rewrite skipn_firstn_comm.
      apply prefix_take_ge; [|lia]. rewrite fold_str_drop. apply find_occur; lia. 
    + intros k Hk Ht. unfold str_take in *. rewrite length_take in Hk.
      eapply find_first_occur; [lia|done|lia|].
      unfold occur. etrans. { apply Ht. }
      unfold_str_drop. rewrite skipn_firstn_comm. apply prefix_take.
  Qed.

  (** Lemma 4.11 *)
  Lemma rewrite_substr_l_shl (i j k : nat) s :
    k ≤ i ∧ i ≤ j ≤ length s →
    s[i - k : j] = (reverse (reverse s[:i])[:k]) ++ s[i:j].
  Proof.
    intros. rewrite !substr_alt. unfold str_take. unfold_str_drop. rewrite !Nat2Z.id.
    rewrite take_reverse, reverse_involutive, length_take.
    rewrite <-(drop_take_drop _ _ i) by lia. f_equal. f_equal; [lia|].
    rewrite take_take. f_equal. lia.
  Qed.

  Lemma rewrite_substr_l_shr (i j k : nat) s :
    s[i + k : j] = s[i:j][k:].
  Proof.
    intros. rewrite !substr_alt. unfold str_take. unfold_str_drop. rewrite !Nat2Z.id.
    replace (Z.to_nat (i + k))%nat with (i + k)%nat by lia. by rewrite drop_drop.
  Qed.

  Lemma rewrite_substr_r_shl (i j k : nat) s :
    i ≤ j - k ∧ j ≤ length s →
    s[i : j - k] = reverse (reverse s[i:j])[k:].
  Proof.
    intros. unfold substr, str_take. unfold_str_drop. rewrite !Nat2Z.id.
    rewrite drop_reverse, reverse_involutive, length_take, length_drop, take_take.
    f_equal. lia.
  Qed.

  Lemma rewrite_substr_r_shr (i j k : nat) s :
    i ≤ j →
    s[i : j + k] = s[i:j] ++ s[j:][:k].
  Proof.
    intros. unfold substr, str_take. unfold_str_drop. rewrite !Nat2Z.id.
    replace (Z.to_nat (j + k - i))%nat with (j - i + k)%nat by lia.
    rewrite <-take_take_drop. f_equal; f_equal; [lia|].
    rewrite drop_drop. f_equal. lia.
  Qed.

End infer_substr.

Section infer_length.

  Local Open Scope range_scope.

  Fixpoint re_length (r : regex) : range :=
    match r with
    | re_none => {[ 0 ]}
    | re_null => {[ 0 ]}
    | re_lit _ => {[ 1 ]}
    | re_concat r1 r2 => re_length r1 + re_length r2
    | re_union r1 r2 => re_length r1 ⊔ re_length r2
    | re_star r => (fin 0, inf)
    end.

  (** Lemma 4.12 *)
  Lemma elem_of_re_length s r :
    s ∈ r →
    length s ∈ re_length r.
  Proof.
    induction 1.
    - by cbv.
    - by cbv.
    - rewrite length_app. by apply elem_of_range_add.
    - simpl. apply elem_of_range_join. by left.
    - simpl. apply elem_of_range_join. by right.
    - by cbv.
    - split; simpl; lia.
  Qed.

  Definition infer_length_sound := elem_of_re_length.

  Lemma infer_find_sound s r t (i : nat) :
    s ∈ r →
    find s t = i →
    i ∈ re_length (re_take_index (index_at t) r).
  Proof.
    intros.
    assert (i = length s[:i]) as ->.
    { unfold str_take. rewrite length_take. pose (find_le s t). lia. }
    apply elem_of_re_length, infer_take_index_sound; [done|lia|done].
  Qed.

End infer_length.