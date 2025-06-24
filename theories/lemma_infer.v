From stdpp Require Import list.
From flat Require Import regexes lang_infer.

Section lemma_infer.

  Implicit Type (s : str) (r : regex).

  (* Length *)

  Fixpoint re_length_min (r : regex) : nat :=
    match r with
    | re_none => 0
    | re_null => 0
    | re_lit _ => 1
    | re_concat r1 r2 => re_length_min r1 + re_length_min r2
    | re_union r1 r2 => re_length_min r1 `min` re_length_min r2
    | re_star _ => 0
    end.

  Lemma re_length_min_le s r :
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

  Lemma re_length_max_ge s r :
    s ∈ r →
    ∀ m, re_length_max r = Some m → length s ≤ m.
  Proof.
    induction 1; intros; simplify_option_eq; try lia.
    - rewrite length_app. apply Nat.add_le_mono; auto.
    - etrans; [|by apply Nat.le_max_l]. auto.
    - etrans; [|by apply Nat.le_max_r]. auto.
    - rewrite length_app. replace 0 with (0 + 0) by lia. apply Nat.add_le_mono; auto.
  Qed.

  Lemma infer_length_lemma s r :
    s ∈ r →
    (re_length_min r ≤ length s) ∧ 
    (match re_length_max r with Some m => length s ≤ m | None => True end).
  Proof.
    intros. split.
    + by apply re_length_min_le.
    + case_match; [|done]. by eapply re_length_max_ge.
  Qed.

  (* Index-Of *)

  Definition index_of_in_range (i : Z) (t s : str) (r : regex) : Prop :=
    let r' := re_take_until t r in
    (re_length_min r' ≤ Z.to_nat i) ∧ 
    (match re_length_max r' with Some m => Z.to_nat i ≤ m | None => True end) ∧
    (Z.to_nat i < length s).

  Lemma infer_index_of_nonneg_lemma s r t i :
    s ∈ r →
    str_index_of t s = i →
    (0 ≤ i)%Z →
    index_of_in_range i t s r.
  Proof.
    intros. unfold index_of_in_range. intros.
    assert (str_take i s ∈ re_take_until t r). { apply elem_of_re_take_until; [done..|lia]. }
    assert (Z.to_nat i < length s). admit.
    repeat split; [..|done].
    + trans (length (str_take i s)); [by apply re_length_min_le|].
      rewrite length_str_take. lia.
    + case_match; [|done]. trans (length (str_take i s)); [|by eapply re_length_max_ge].
      rewrite length_str_take. lia.
  Admitted.

  (* Index of Char-At *)

  Lemma infer_index_of_char_at_lemma i s c r :
    str_at i s = [c] →
    s ∈ r →
    index_of_in_range i [c] s r.
  Proof.
    intros.
  Admitted.

  (* Char-At *)

  Lemma infer_char_at_lemma i s C :
    str_at i s ∈ re_lit C →
    Exists (λ c, str_at i s = [c]) (elements C).
  Proof.
    intros Hi. apply elem_of_re_lit_inv in Hi as [c [??]].
    apply Exists_exists. exists c. split; [by apply elem_of_elements | done].
  Qed.

End lemma_infer.
