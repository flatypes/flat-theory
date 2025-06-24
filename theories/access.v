(* From stdpp Require Import list.
From flat Require Import regexes util.

Fixpoint cut_head_tail (r : regex) : list (charset * regex) :=
  match r with
  | re_none | re_null => []
  | re_lit C => [(C, re_null)]
  | re_concat r1 r2 =>
    ((λ '(C, r), (C, r ⧺ r2)) <$> cut_head_tail r1) ++
    (if nullable r1 then cut_head_tail r2 else [])
  | re_union r1 r2 =>
    cut_head_tail r1 ++ cut_head_tail r2
  | re_star r1 =>
    (λ '(C, r), (C, re_concat r (re_star r1))) <$> cut_head_tail r1
  end.

Lemma cut_head_tail_spec s r c :
  s ∈ r →
  head s = Some c →
  ∃ C r', (C, r') ∈ cut_head_tail r ∧ c ∈ C ∧ tail s ∈ r'.
Proof.
  induction 1 as [|C ?|r1 r2 s1 s2 ? IHs1 ? IHs2|???? IHs1|???? IHs2|?|r s1 s2 ? IHs1 ? IHs2] => Hs;
    [done|..|done|].
  - inversion Hs; subst; clear Hs.
    exists C, re_null. repeat split; [|done|constructor].
    simpl. by rewrite elem_of_list_singleton.
  - destruct s1.
    + destruct IHs2 as [C [r' [? [??]]]]; [done|].
      exists C, r'. repeat split; [|done..].
      simpl. replace (nullable r1) with true by (symmetry; by rewrite nullable_spec).
      rewrite elem_of_app. by right.
    + destruct IHs1 as [C [r' [? [??]]]]; [done|].
      exists C, (r' ⧺ r2). repeat split; [|done|by constructor].
      simpl. rewrite elem_of_app, elem_of_list_fmap. left. by exists (C, r').
  - destruct IHs1 as [C [r' [? [??]]]]; [done|].
    exists C, r'. repeat split; [|done..].
    simpl. rewrite elem_of_app. by left.
  - destruct IHs2 as [C [r' [? [??]]]]; [done|].
    exists C, r'. repeat split; [|done..].
    simpl. rewrite elem_of_app. by right.
  - destruct s1.
    + destruct IHs2 as [C [r' [? [??]]]]; [done|].
      exists C, r'. repeat split; done.
    + destruct IHs1 as [C [r' [? [??]]]]; [done|].
      exists C, (r' ⧺ (re_star r)). repeat split; [|done|by constructor].
      simpl. rewrite elem_of_list_fmap. by exists (C, r').
Qed.

Fixpoint cut_at_index (r : regex) (k : nat) : list (regex * charset * regex) :=
  match k with
  | 0 => (λ '(C, r), (re_null, C, r)) <$> cut_head_tail r
  | S k' => 
    '(r1, C1, r) ← cut_at_index r k';
    (λ '(C2, r2), (r1 ⧺ re_lit C1, C2, r2)) <$> cut_head_tail r
  end.

Lemma cut_at_index_spec s r k c :
  s ∈ r →
  s !! k = Some c →
  ∃ r1 C r2, (r1, C, r2) ∈ cut_at_index r k ∧ take k s ∈ r1 ∧ c ∈ C ∧ drop (S k) s ∈ r2.
Proof.
  intros. generalize dependent c. induction k as [|k IHk] => c Hc.
  - rewrite <-head_lookup in Hc.
    destruct (cut_head_tail_spec s r c) as [C [r' [? [??]]]]; [done..|].
    exists re_null, C, r'. repeat split; [|constructor|done|naive_solver].
    simpl. rewrite elem_of_list_fmap. by exists (C, r').
  - assert (is_Some (s !! S k)) as Hk. { by exists c. }
    rewrite lookup_lt_is_Some in Hk. apply Nat.lt_succ_l in Hk.
    rewrite <-lookup_lt_is_Some in Hk. destruct Hk as [c' ?].
    destruct (IHk c') as [r1 [C1 [r' ?]]]; [done|].
    exists (re_concat r1 (re_lit C1)), C1.
Admitted.

Definition infer_char_at (r : regex) (k : nat) : charset :=
  big_union ((λ '(r1, C, r2), C) <$> (cut_at_index r k)).

Lemma rule_infer_char_at s r k c :
  s ∈ r →
  s !! k = Some c →
  c ∈ infer_char_at r k.
Proof.
  intros. unfold infer_char_at.
  destruct (cut_at_index_spec s r k c) as [r1 [C' [r2 [? [? [??]]]]]]; [done..|].
  eapply elem_of_big_union; [by apply elem_of_list_fmap; exists (r1, C', r2) | done].
Qed.

Definition refine_char_at (r : regex) (k : nat) (Cₜ : charset) : regex :=
  big_union ((λ '(r1, C, r2), r1 ⧺ re_lit (C ∩ Cₜ) ⧺ r2) <$> (cut_at_index r k)).

Lemma str_cut_middle (s : str) k c :
  s !! k = Some c →
  take k s ++ [c] ++ drop (S k) s = s.
Proof.
  intros. rewrite <-cons_middle. erewrite <-drop_S; [|done]. by rewrite take_drop.
Qed.

Lemma rule_refine_char_at s r k c Cₜ :
  s ∈ r →
  s !! k = Some c →
  c ∈ Cₜ →
  s ∈ refine_char_at r k Cₜ.
Proof.
  intros.
  destruct (cut_at_index_spec s r k c) as [r1 [C' [r2 [? [? [??]]]]]]; [done..|].
  eapply elem_of_big_union; first by apply elem_of_list_fmap; exists (r1, C', r2).
  rewrite <-(str_cut_middle s k c); [|done].
  constructor; [done|]. constructor; [|done]. by constructor.
Qed.

Definition infer_take (r : regex) (k : nat) : regex :=
  big_union ((λ '(r1, _, _), r1) <$> (cut_at_index r k)).

Lemma rule_infer_take s r k :
  s ∈ r →
  k < length s →
  take k s ∈ infer_take r k.
Proof.
  intros ? Hk. apply lookup_lt_is_Some in Hk as [c ?].
  destruct (cut_at_index_spec s r k c) as [r1 [C' [r2 [? [? [??]]]]]]; [done..|].
  eapply elem_of_big_union; [by apply elem_of_list_fmap; exists (r1, C', r2) | done].
Qed.

Definition infer_drop (r : regex) (k : nat) : regex :=
  big_union ((λ '(_, C, r2), re_lit C ⧺ r2) <$> (cut_at_index r k)).

Lemma rule_infer_drop s r k :
  s ∈ r →
  k < length s →
  drop k s ∈ infer_drop r k.
Proof.
  intros ? Hk. apply lookup_lt_is_Some in Hk as [c ?].
  destruct (cut_at_index_spec s r k c) as [r1 [C' [r2 [? [? [??]]]]]]; [done..|].
  eapply elem_of_big_union; first by apply elem_of_list_fmap; exists (r1, C', r2).
  erewrite drop_S; [|done]. rewrite cons_app. constructor; [|done]. by constructor.
Qed. *)
