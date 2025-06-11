From stdpp Require Import list.
From flat Require Import regexes derivatives util.

Fixpoint infer_drop (n : nat) (r : regex) : regex :=
  match n with
  | 0 => r
  | S n' => 
    let r' := infer_drop n' (d_all r) in
    if bool_decide (ε ∈ r) then re_null ∪ r' else r'
  end.

Lemma rule_infer_drop s r n :
  s ∈ r →
  drop n s ∈ infer_drop n r.
Proof.
  revert s r. induction n as [|n' IHn'] => s r Hs.
  - by rewrite drop_0.
  - destruct s.
    * rewrite drop_nil. simpl. case_bool_decide; [|naive_solver].
      apply elem_of_union_l. constructor.
    * simpl. case_bool_decide; [apply elem_of_union; right |].
      all: apply IHn'; eapply elem_of_d_all; eauto.
Qed.

Fixpoint infer_take (n : nat) (r : regex) : regex :=
  match n with
  | 0 => re_null
  | S n' => 
    let r' := union_many ((λ '(C, r'), (re_lit C) ++ᵣ (infer_take n') r') <$> dd_all r) in
    if bool_decide (ε ∈ r) then re_null ∪ r' else r'
  end.

Lemma rule_infer_take s r n :
  s ∈ r →
  take n s ∈ infer_take n r.
Proof.
  revert s r. induction n as [|n' IHn'] => s r Hs.
  - rewrite take_0. constructor.
  - destruct s.
    * rewrite take_nil. simpl. case_bool_decide; [|naive_solver].
      apply elem_of_union. left. constructor.
    * simpl. case_bool_decide; [apply elem_of_union; right|].
      all: apply elem_of_dd_all in Hs as [C [r' [? [??]]]].
      all: eapply elem_of_union_many; [by apply elem_of_list_fmap; exists (C, r') |].
      all: apply elem_of_concat_lit; auto.
Qed.

Definition infer_substr (r : regex) (i j : nat) : regex :=
  if bool_decide (i < j) then infer_take (j - i) (infer_drop i r) else re_null.

Lemma rule_infer_substr s r i j :
  s ∈ r →
  substr s i j ∈ infer_substr r i j.
Proof.
  intros. unfold substr, infer_substr. case_bool_decide.
  - by apply rule_infer_take, rule_infer_drop.
  - constructor.
Qed. 

Definition infer_char_at_const (i : nat) (r : regex) : charset :=
  first_set (infer_drop i r).

Lemma rule_infer_char_at_const s r i c :
  s ∈ r →
  s !! i = Some c →
  c ∈ infer_char_at_const i r.
Proof.
  intros Hs Hc.
  eapply elem_of_first_set. erewrite <-drop_S; eauto.
  by apply rule_infer_drop.
Qed.

Lemma rule_infer_char_at_index_of s c i :
  index_of s c = Some i →
  s !! i = Some c.
Proof.
  revert i. induction s => i.
  - by inversion 1.
  - simpl. case_bool_decide; [naive_solver|].
    rewrite fmap_Some. intros [j [? ->]]. setoid_rewrite lookup_cons. auto.
Qed.