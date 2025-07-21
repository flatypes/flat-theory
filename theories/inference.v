From stdpp Require Import list sets.
From flat Require Import regexes intervals.

(** * Prefix, Suffix, and Infix *)

Section infer_test.

  Implicit Type (s t : str) (σ : char) (r : regex).

  Lemma infer_prefix_false_sound s r t :
    s ∈ r →
    d_str t r ≡ ∅ →
    ¬ (t ⊑ s).
  Proof.
    intros Hs ? Hp. apply bool_decide_spec in Hp as [? ->].
    apply elem_of_d_str in Hs. set_solver.
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

  (** Lemma 4.1 *)
  Lemma elem_of_re_take_1 s r :
    s ∈ r →
    take 1 s ∈ re_take_1 r.
  Proof.
    induction 1 as [|?|?? s1 s2|?|?|?|? s1 s2]; simpl.
    - constructor.
    - by constructor.
    - destruct s1.
      * rewrite bool_decide_true by done. simpl. set_solver.
      * rewrite take_app, length_cons, take_0, app_nil_r. set_solver.
    - set_solver.
    - set_solver.
    - apply elem_of_union. right. constructor.
    - rewrite take_app. destruct s1; [done|].
      rewrite length_cons, take_0, app_nil_r. set_solver.
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
    induction Hs as [|σ'|r1 r2 ??? IHr1 ? IHr2|?|?|?|r ???? IHr1 ? IHr2] => i σ Hi.
    - by apply char_at_lookup in Hi.
    - apply char_at_lookup, list_lookup_singleton_Some in Hi as [-> ->].
      simpl. rewrite bool_decide_true by done.
      exists re_null, (re_lit L). repeat split; [set_solver | constructor | by constructor].
    - apply char_at_inv_app in Hi as [[? Hi]|[? Hi]].
      * clear IHr2. apply IHr1 in Hi as [r1l [r1r [? [??]]]]. exists r1l, (r1r ⧺ r2).
        split. { simpl. rewrite elem_of_app. left. rewrite elem_of_list_fmap.
                 eexists. split; [|done]. done. }
        split. { by rewrite take_app_l by lia. }
        rewrite drop_app_l by lia. by constructor.
      * clear IHr1. apply IHr2 in Hi as [r2l [r2r [? [??]]]]. exists (r1 ⧺ r2l), r2r.
        split. { simpl. rewrite elem_of_app. right. rewrite elem_of_list_fmap.
                 eexists. split; [|done]. done. }
        split. { rewrite take_app_r by lia. by constructor. }
        by rewrite drop_app_r by lia.
    - set_solver.
    - set_solver.
    - by apply char_at_lookup in Hi.
    - apply char_at_inv_app in Hi as [[? Hi]|[? Hi]].
      * clear IHr2. apply IHr1 in Hi as [r1l [r1r [? [??]]]].
        exists (re_star r ⧺ r1l), (r1r ⧺ re_star r).
        split. { simpl. rewrite elem_of_list_fmap. eexists. split; [|done]. done. }
        split. { rewrite take_app_l by lia.
                 rewrite <-app_nil_l at 1. constructor; [constructor | done]. }
        rewrite drop_app_l by lia. by constructor.
      * clear IHr1. apply IHr2 in Hi as [r1 [r2 [Hr1r2 [Hs1l ?]]]].
        exists r1, r2. split. { done. }
        split. { rewrite take_app_r by lia.
                 simpl in Hr1r2. apply elem_of_list_fmap in Hr1r2 as [[??] [Hr1 ?]].
                 inv Hr1. inv Hs1l. rewrite app_assoc. constructor; [by constructor | done]. }
        by rewrite drop_app_r by lia.
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
    unfold str_infix. rewrite bool_decide_spec. intros -> Hs ? [i Hi].
    apply find_Some_occur in Hi as [s2 Hs2].
    apply (elem_of_re_split_suffix _ _ i σ) in Hs.
    2: { unfold char_at. by rewrite Hs2. }
    rewrite Hs2 in Hs. apply elem_of_d_str in Hs. set_solver.
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
    intros -> ? Hh Hp.
    eapply elem_of_re_have_forall in Hh; [|done].
    apply elem_of_list_lookup in Hh as [i Hi]. apply char_at_lookup in Hi.
    eapply re_prefix_forall_spec in Hp. 2: by apply elem_of_re_split_suffix.
    apply str_infix_infix. apply bool_decide_spec in Hp as [s2 Hs2].
    exists s[:i], s2. by rewrite <-Hs2, take_drop.
  Qed.

End infer_test.

Section infer_substr.

  Implicit Type (s t : str) (σ : char) (r : regex) (i j k : nat).

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
    drop 1 s ∈ re_drop_1 r.
  Proof.
    induction 1 as [|?|?? s1 s2|?|?|?|? s1 s2]; simpl.
    - constructor.
    - constructor.
    - destruct s1.
      * rewrite bool_decide_true by done. simpl. set_solver.
      * simpl. rewrite drop_0. apply elem_of_union. left. by constructor.
    - set_solver.
    - set_solver.
    - apply elem_of_union. right. constructor.
    - rewrite drop_app. destruct s1; [done|]. rewrite length_cons, drop_0.
      apply elem_of_union. left. by constructor.
  Qed.

  Fixpoint re_drop (k : nat) (r : regex) : regex :=
    match k with
    | 0 => r
    | S k' => re_drop k' (re_drop_1 r)
    end.

  Local Lemma S_plus_1_l n :
    S n = 1 + n.
  Proof. lia. Qed.

  (** Lemma 4.6 *)
  Lemma elem_of_re_drop s r k :
    s ∈ r →
    drop k s ∈ re_drop k r.
  Proof.
    revert s r. induction k as [|k IHk] => s r ?; simpl. { by rewrite drop_0. }
    rewrite S_plus_1_l, <-drop_drop.
    apply IHk. by apply elem_of_re_drop_1.
  Qed.

  Fixpoint re_take (k : nat) (r : regex) : regex :=
    match k with
    | 0 => re_null
    | S k' => re_take_1 r ⧺ re_take k' (re_drop_1 r)
    end.

  (** Lemma 4.7 *)
  Lemma elem_of_re_take s r k :
    s ∈ r →
    take k s ∈ re_take k r.
  Proof.
    revert s r. induction k as [|k IHk] => s r ?; simpl. { rewrite take_0. constructor. }
    rewrite S_plus_1_l, <-take_take_drop.
    constructor. { by apply elem_of_re_take_1. }
    apply IHk. by apply elem_of_re_drop_1.
  Qed.

  Fixpoint re_exclude (σ : char) (r : regex) : regex :=
    match r with
    | re_none => re_none
    | re_null => re_null
    | re_lit L => re_lit (L ∖ {[σ]})
    | re_concat r1 r2 => re_exclude σ r1 ⧺ re_exclude σ r2
    | re_union r1 r2 => re_exclude σ r1 ∪ re_exclude σ r2
    | re_star r => re_star (re_exclude σ r)
    end.

  Lemma elem_of_re_exclude s r σ :
    s ∈ r →
    σ ∉ s →
    s ∈ re_exclude σ r.
  Proof.
    induction 1; simpl; intros; constructor; set_solver.
  Qed.

  Definition re_find (σ : char) (r : regex) : list (regex * regex) :=
    '(r1, r2) ← re_split σ r;
    let r1' := re_exclude σ r1 in
    if bool_decide (r1' ≢ ∅) then [(r1', re_lit {[σ]} ⧺ re_drop_1 r2)] else [].

  Local Lemma S_plus_1_r n :
    S n = n + 1.
  Proof. lia. Qed.

  (** Lemma 4.8 *)
  Lemma elem_of_re_find s r i σ :
    s ∈ r →
    find s σ = Some i →
    ∃ r1 r2, (r1, r2) ∈ re_find σ r ∧ s[:i] ∈ r1 ∧ s[i:] ∈ r2.
  Proof.
    intros ? Hi.
    apply find_char_Some in Hi as [Hi ?].
    edestruct elem_of_re_split as [r1 [r2 [? [??]]]]; [done..|].
    exists (re_exclude σ r1), (re_lit {[σ]} ⧺ re_drop_1 r2).
    assert (s[:i] ∈ re_exclude σ r1). { by apply elem_of_re_exclude. }
    repeat split; [|done|].
    + unfold re_find. apply elem_of_list_bind. eexists. split; [|done].
      case_match. rewrite bool_decide_true; set_solver.
    + apply char_at_lookup in Hi. rewrite (drop_S _ σ) by done.
      apply elem_of_re_concat_lit; [set_solver|].
      rewrite S_plus_1_r, <-drop_drop. by apply elem_of_re_drop_1.
  Qed.

  Definition re_find_suffix (σ : char) (r : regex) : regex := ⋃ (snd <$> re_find σ r).
  Definition re_find_prefix (σ : char) (r : regex) : regex := ⋃ (fst <$> re_find σ r).

  Lemma elem_of_re_find_suffix s r σ i :
    s ∈ r →
    find s σ = Some i →
    s[i:] ∈ re_find_suffix σ r.
  Proof.
    intros ? Hi.
    eapply elem_of_re_find in Hi as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r2. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Lemma elem_of_re_find_prefix s r σ i :
    s ∈ r →
    find s σ = Some i →
    s[:i] ∈ re_find_prefix σ r.
  Proof.
    intros ? Hi.
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
    t ⊑ s[i:] →
    ∃ r1 r2, (r1, r2) ∈ re_split_str σ t' r ∧ s[:i] ∈ r1 ∧ s[i:] ∈ r2.
  Proof.
    intros ?? Ht. apply bool_decide_spec in Ht as [s' Ht].
    assert (s[i] = σ) as Hi. { unfold char_at. rewrite Ht. naive_solver. }
    eapply elem_of_re_split in Hi as [r1 [r2 [? [??]]]]; [|done].
    exists r1, ({[t]} ⧺ d_str t r2). 
    assert (s' ∈ d_str t r2). { apply elem_of_d_str. by rewrite <-Ht. }
    repeat split; [|done|].
    + unfold re_split_str. apply elem_of_list_bind. eexists. split; [|done]. case_match.
      rewrite bool_decide_true; set_solver.
    + rewrite Ht. constructor; [set_solver|done].
  Qed.

  Definition re_split_str_suffix (σ : char) (t' : str) (r : regex) : regex :=
    ⋃ (snd <$> re_split_str σ t' r).
  Definition re_split_str_prefix (σ : char) (t' : str) (r : regex) : regex :=
    ⋃ (fst <$> re_split_str σ t' r).
  
  Lemma elem_of_re_split_str_suffix s r t σ t' i :
    s ∈ r →
    t = σ :: t' →
    t ⊑ s[i:] →
    s[i:] ∈ re_split_str_suffix σ t' r.
  Proof.
    intros ?? Ht.
    eapply elem_of_re_split_str in Ht as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r2. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  Lemma elem_of_re_split_str_prefix s r t σ t' i :
    s ∈ r →
    t = σ :: t' →
    t ⊑ s[i:] →
    s[:i] ∈ re_split_str_prefix σ t' r.
  Proof.
    intros ?? Ht.
    eapply elem_of_re_split_str in Ht as [r1 [r2 [? [??]]]]; [|done..].
    apply elem_of_union_list. exists r1. split; [|done].
    apply elem_of_list_fmap. by exists (r1, r2).
  Qed.

  (** Abstract index. *)
  Inductive index : Type :=
    | index_l : nat → index
    | index_r : nat → index
    | index_at : char * str → index (* nonempty pattern *)
    .

  (** Semantic interpretation: concretize [κ] as an index of a given string [s]. *)
  Definition index_con (κ : index) (s : str) : option nat :=
    match κ with
    | index_l k => Some k
    | index_r k => if bool_decide (k ≤ length s) then Some (length s - k) else None
    | index_at (σ, t) => find s (σ :: t)
    end.
  Notation "⟦ κ ⟧ s" := (index_con κ s) (at level 20, no associativity, format "⟦  κ  ⟧  s").

  Definition re_drop_index (κ : index) (r : regex) : regex :=
    match κ with
    | index_l k => re_drop k r
    | index_r k => re_rev (re_take k (re_rev r))
    | index_at (σ, []) => re_find_suffix σ r
    | index_at (σ, t) => re_split_str_suffix σ t r
    end.
  
  Definition re_take_index (κ : index) (r : regex) : regex :=
    match κ with
    | index_l k => re_take k r
    | index_r k => re_rev (re_drop k (re_rev r))
    | index_at (σ, []) => re_find_prefix σ r
    | index_at (σ, t) => re_split_str_prefix σ t r
    end.

  Lemma infer_drop_index_sound s r κ i :
    s ∈ r →
    ⟦ κ ⟧ s = Some i →
    drop i s ∈ re_drop_index κ r.
  Proof.
    intros ?. destruct κ as [k|k|[σ t]]; simpl; [| case_bool_decide | destruct t as [|σ' t']].
    1-3: inv 1.
    - by apply elem_of_re_drop.
    - rewrite <-reverse_involutive at 1. apply elem_of_re_rev.
      rewrite reverse_drop, Nat.sub_sub_distr, Nat.sub_diag by lia. simpl.
      by apply elem_of_re_take, elem_of_re_rev.
    - by apply elem_of_re_find_suffix.
    - intros Hi. apply find_Some_occur in Hi.
      eapply elem_of_re_split_str_suffix; [done..|].
      unfold str_prefix. by apply bool_decide_spec.
  Qed.

  Lemma infer_take_index_sound s r κ j :
    s ∈ r →
    ⟦κ⟧ s = Some j →
    take j s ∈ re_take_index κ r.
  Proof.
    intros ?. destruct κ as [k|k|[σ t]]; simpl; [| case_bool_decide | destruct t as [|σ' t']].
    1-3: inv 1.
    - by apply elem_of_re_take.
    - rewrite <-reverse_involutive at 1. apply elem_of_re_rev.
      rewrite reverse_take, Nat.sub_sub_distr, Nat.sub_diag by lia. simpl.
      by apply elem_of_re_drop, elem_of_re_rev.
    - by apply elem_of_re_find_prefix.
    - intros Hi. apply find_Some_occur in Hi.
      eapply elem_of_re_split_str_prefix; [done..|].
      unfold str_prefix. by apply bool_decide_spec.
  Qed.

  Inductive index_neg : index → Prop :=
    | index_neg_r k : index_neg (index_r k)
    | index_neg_at x : index_neg (index_at x)
    .

  (** Lemma 4.10 *)
  Lemma index_shift_suffix κ s k i :
    index_neg κ →
    ⟦ κ ⟧ s = Some k →
    i < k →
    ⟦ κ ⟧ (s[i:]) = Some (k - i).
  Proof.
    inv 1 as [?|[σ t']]; simpl; [case_bool_decide|]. 1-2: inv 1.
    - intros. rewrite length_drop, bool_decide_true by lia. f_equal. lia.
    - remember (σ :: t') as t. intros Hk ?. apply find_eq_Some.
      + rewrite length_drop. apply find_Some_le in Hk. lia.
      + rewrite drop_drop. apply find_Some_occur. rewrite Hk. f_equal. lia.
      + intros j ? Hp. rewrite drop_drop in Hp.
        eapply find_Some_not_occur; [done| |done]. lia.
  Qed.

  Lemma infer_substr_index_take_drop_sound s r i j κi κj :
    s ∈ r →
    i < j →
    ⟦ κi ⟧ s = Some i →
    ⟦ κj ⟧ s = Some j →
    index_neg κj →
    s[i:j] ∈ re_take_index κj (re_drop_index κi r).
  Proof.
    intros. apply infer_take_index_sound.
    + by apply infer_drop_index_sound.
    + apply index_shift_suffix; [done..|lia].
  Qed.

  Lemma infer_substr_index_drop_take_1_sound s r i j :
    s ∈ r →
    i < j →
    s[i:j] ∈ re_drop i (re_take j r).
  Proof.
    intros. rewrite substr_alt. by apply elem_of_re_drop, elem_of_re_take.
  Qed.

  Lemma prefix_take_ge {A : Type} (k l : list A) n :
    k `prefix_of` l →
    (length k ≤ n)%nat →
    k `prefix_of` take n l.
  Proof.
    intros [l' ->] ?. rewrite take_app. apply prefix_app_r. by rewrite take_ge by lia.
  Qed.

  Lemma infer_substr_index_drop_take_2_sound s r i j σ t' :
    s ∈ r →
    i + length t' < j →
    ⟦ index_at (σ, t') ⟧ s = Some i →
    s[i:j] ∈ re_drop_index (index_at (σ, t')) (re_take j r).
  Proof.
    intros ?? Hi. rewrite substr_alt. 
    apply infer_drop_index_sound. { by apply elem_of_re_take. }
    simpl in *. remember (σ :: t') as t. apply find_eq_Some.
    + rewrite length_take. apply find_Some_le in Hi.
      simplify_eq. rewrite length_cons in *. lia.
    + rewrite <-substr_alt. unfold substr. apply prefix_take_ge.
      { by apply find_Some_occur. }
      simplify_eq. rewrite length_cons. lia.
    + intros k ? Hp. eapply find_Some_not_occur; [done..|].
      rewrite <-substr_alt in Hp. unfold substr in Hp.
      etrans. { apply Hp. } apply prefix_take.
  Qed.

  (** Lemma 4.11 *)
  Lemma rewrite_substr_l_shl i j k s :
    k ≤ i ∧ i ≤ j ≤ length s →
    s[i - k : j] = (reverse (reverse s[:i])[:k]) ++ s[i:j].
  Proof.
    intros. rewrite !substr_alt, take_reverse, reverse_involutive, length_take.
    rewrite <-(drop_take_drop _ _ i) by lia. f_equal. f_equal; [lia|].
    rewrite take_take. f_equal. lia.
  Qed.

  Lemma rewrite_substr_l_shr i j k s :
    s[i + k : j] = s[i:j][k:].
  Proof.
    by rewrite !substr_alt, drop_drop.
  Qed.

  Lemma rewrite_substr_r_shl i j k s :
    i ≤ j - k ∧ j ≤ length s →
    s[i : j - k] = reverse (reverse s[i:j])[k:].
  Proof.
    intros. unfold substr.
    rewrite drop_reverse, reverse_involutive, length_take, length_drop, take_take.
    f_equal. lia.
  Qed.

  Lemma rewrite_substr_r_shr i j k s :
    i ≤ j →
    s[i : j + k] = s[i:j] ++ s[j:][:k].
  Proof.
    intros. unfold substr.
    rewrite Nat.add_sub_swap, <-take_take_drop by lia.
    do 2 f_equal. rewrite drop_drop. f_equal. lia.
  Qed.

End infer_substr.

Section infer_length.

  Implicit Type (s t : str) (σ : char) (r : regex).

  Fixpoint re_length (r : regex) : interval :=
    match r with
    | re_none => {[0]}
    | re_null => {[0]}
    | re_lit _ => {[1]}
    | re_concat r1 r2 => (re_length r1 + re_length r2)%interval
    | re_union r1 r2 => re_length r1 ⊔ re_length r2
    | re_star r => 0 `to` ∞
    end.

  (** Lemma 4.12 *)
  Lemma elem_of_re_length s r :
    s ∈ r →
    length s ∈ re_length r.
  Proof.
    induction 1; try (cbv; lia).
    - rewrite length_app. simpl. by apply elem_of_interval_plus.
    - simpl. apply elem_of_interval_join. by left.
    - simpl. apply elem_of_interval_join. by right.
  Qed.

  Definition infer_length_sound := elem_of_re_length.

  Lemma infer_find_sound s r t σ t' i :
    s ∈ r →
    t = σ :: t' →
    find s t = Some i →
    i ∈ re_length (re_take_index (index_at (σ, t')) r).
  Proof.
    intros ? -> Hi.
    assert (i = length s[:i]) as ->.
    { rewrite length_take. apply find_Some_le in Hi. lia. }
    by apply elem_of_re_length, infer_take_index_sound.
  Qed.

End infer_length.