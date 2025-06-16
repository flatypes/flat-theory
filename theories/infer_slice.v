From stdpp Require Import sets.
From flat Require Import regexes split_regex.

Section infer_slice.
  Local Open Scope Z_scope.

  Implicit Type s : str.
  Implicit Type r : regex.

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

  Lemma infer_substr_begin_index_of s c r :
    s ∈ r →
    let i := str_index_of s c in
    0 ≤ i < length s →
    str_substr_begin s i ∈ (re_split_at_char r c).2.
  Proof.
    intros Hs ??.
    apply (re_split_at_char_spec s c r) in Hs as [??]; [|lia].
    unfold str_substr_begin. rewrite bool_decide_true; done.
  Qed.

  Lemma infer_substr_until_index_of s c r :
    s ∈ r →
    let i := str_index_of s c in
    0 ≤ i < length s →
    str_substr_until s i ∈ (re_split_at_char r c).1.
  Proof.
    intros Hs ??.
    apply (re_split_at_char_spec s c r) in Hs as [??]; [|lia].
    by unfold str_substr_until.
  Qed.

End infer_slice.