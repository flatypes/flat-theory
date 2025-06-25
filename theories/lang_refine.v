From stdpp Require Import list sets.
From flat Require Import regexes lemma_infer ranges util.

(* Refine by char-at *)

Fixpoint re_split_0 (r : regex) : list (charset * regex) :=
  match r with
  | re_none => []
  | re_null => []
  | re_lit C => if bool_decide (C ≡ ∅) then [] else [(C, re_null)]
  | re_concat r1 r2 =>
    ((λ '(C, r'), (C, r' ⧺ r2)) <$> re_split_0 r1) ++
    (if bool_decide ([] ∈ r1) then re_split_0 r2 else [])
  | re_union r1 r2 => re_split_0 r1 ++ re_split_0 r2
  | re_star r => (λ '(C, r'), (C, r' ⧺ re_star r)) <$> re_split_0 r
  end.

Lemma elem_of_re_split_0 s r c :
  s ∈ r →
  head s = Some c →
  ∃ C r', (C, r') ∈ re_split_0 r ∧ c ∈ C ∧ tail s ∈ r'.
Proof.
  induction 1 as [|C c'|r1 r2 s1 s2 ? IHr1 ? IHr2|
    r1 r2 s1 s2 IHr|r1 r2 s1 s2 IHr|?|r s1 s2 ?? IHr1 ? IHr2]; intros; simplify_list_eq.
  - exists C, re_null. repeat split; [|done|constructor].
    rewrite bool_decide_false; set_solver.
  - destruct s1; simplify_list_eq.
    * clear IHr1. edestruct IHr2 as [C [r' [? [??]]]]; [done|].
      exists C, r'. repeat split; [|done..].
      apply elem_of_app. right. by rewrite bool_decide_true.
    * clear IHr2. edestruct IHr1 as [C [r' [? [??]]]]; [done|].
      exists C, (r' ⧺ r2). repeat split; [|done|by constructor].
      apply elem_of_app. left. apply elem_of_list_fmap. naive_solver.
  - set_solver.
  - set_solver.
  - destruct s1; [done|]. simplify_list_eq.
    clear IHr2. edestruct IHr1 as [C [r' [? [??]]]]; [done|].
    exists C, (r' ⧺ re_star r). repeat split; [|done|by constructor].
    apply elem_of_list_fmap. naive_solver.
Qed.

Fixpoint re_split (i : nat) (r : regex) : list (regex * charset * regex) :=
  match i with
  | 0 => (λ '(C, r'), (re_null, C, r')) <$> re_split_0 r
  | S i' =>
    '(C, r') ← re_split_0 r ;
    '(r1, C', r2) ← re_split i' r' ;
    [(re_lit C ⧺ r1, C', r2)]
  end.

Lemma elem_of_re_split s r i c :
  s ∈ r →
  s !! i = Some c →
  ∃ r1 C r2, (r1, C, r2) ∈ re_split i r ∧ c ∈ C ∧ (take i s) ∈ r1 ∧ (drop (S i) s) ∈ r2.
Proof.
  revert s r c. induction i as [|i' IHi'] => s r c Hs ?.
  - edestruct elem_of_re_split_0 as [C [r' [? [??]]]]; [done | by rewrite head_lookup|].
    exists re_null, C, r'. repeat split; [|done|constructor|done].
    unfold re_split. apply elem_of_list_fmap. eexists. split; [|done]. done.
  - destruct s as [|c' s']; [done|]. simplify_list_eq.
    edestruct elem_of_re_split_0 as [C [r' [? [? Hs']]]]; [done..|].
    specialize (IHi' _ _ c Hs') as [r1 [C' [r2 [? [? [??]]]]]]. { done. }
    exists (re_lit C ⧺ r1), C', r2. repeat split; [|done|..|done].
    + simpl. apply elem_of_list_bind. eexists. split; [|done].
      apply elem_of_list_bind. eexists. split; [|done]. set_solver.
    + by apply elem_of_concat_lit.
Qed.

Definition re_split_refine (C : charset) (i : nat) (r : regex) : list regex :=
  '(r1, C1, r2) ← re_split i r ;
  let C' := C1 ∩ C in
  if bool_decide (C' ≢ ∅) then [r1 ⧺ re_lit C' ⧺ r2] else [].

Lemma refine_char_at s r i c C :
  s ∈ r →
  s !! i = Some c →
  c ∈ C →
  s ∈ ⋃ (re_split_refine C i r).
Proof.
  intros Hs ??. apply elem_of_union_list.
  eapply elem_of_re_split in Hs as [r1 [C1 [r2 [? [? [??]]]]]]; [|done].
  exists (r1 ⧺ re_lit (C1 ∩ C) ⧺ r2). split.
  + unfold re_split_refine. apply elem_of_list_bind. eexists. split; [|done].
    case_match. simplify_eq. rewrite bool_decide_true; set_solver.
  + rewrite <-(take_drop i) at 1. constructor; [done|].
    rewrite (drop_S _ c i) by done. apply elem_of_concat_lit; [set_solver | done].
Qed.

(* Refine by length *)

Local Open Scope range_scope.

Fixpoint re_length_in (R : range) (r : regex) : regex :=
  match r with
  | re_none => ∅
  | re_null => if bool_decide (0 ∈ R) then r else ∅
  | re_lit _ => if bool_decide (1 ∈ R) then r else ∅
  | re_concat r1 r2 =>
    let R1 := re_length r1 in
    let R2 := re_length r2 in
    if range_is_singleton R1 then r1 ⧺ re_length_in (R - R1) r2
    else if range_is_singleton R2 then re_length_in (R - R2) r1 ⧺ r2
    else r1 ⧺ r2
  | re_union r1 r2 => re_length_in R r1 ∪ re_length_in R r2
  | re_star r => if bool_decide (0 ∉ R) then r ⧺ (re_star r) else re_star r
  end.

Lemma refine_length s r R :
  s ∈ r →
  length s ∈ R →
  s ∈ re_length_in R r.
Proof.
  intros Hs Hl. generalize dependent R.
  induction Hs as [|C c'|r1 r2 s1 s2 ? IHr1 ? IHr2|
    r1 r2 s1 s2 IHr|r1 r2 s1 s2 IHr|?|r s1 s2 ?? IHr1 ? IHr2] => R Hl; simpl.
  - rewrite bool_decide_true by done. constructor.
  - rewrite bool_decide_true by done. by constructor.
  - repeat case_match.
    * constructor; [done|]. apply IHr2.
      rewrite <-(Nat.add_sub' (length s1)), <-length_app at 1.
      apply elem_of_range_sub; [done | by apply elem_of_re_length].
    * constructor; [|done]. apply IHr1.
      rewrite <-(Nat.add_sub _ (length s2)), <-length_app at 1.
      apply elem_of_range_sub; [done | by apply elem_of_re_length].
    * by constructor.
  - set_solver.
  - set_solver.
  - rewrite bool_decide_false by set_solver. constructor.
  - case_bool_decide; by constructor.
Qed.