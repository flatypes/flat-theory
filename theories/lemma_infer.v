From stdpp Require Import list.
From flat Require Import regexes ranges lang_infer.

Implicit Type (s : str) (r : regex).

Section length.

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

End length.

(* Index-Of *)

Lemma infer_index_of_nonneg_lemma s r t i :
  s ∈ r →
  str_index_of t s = i →
  (0 ≤ i)%Z →
  Z.to_nat i ∈ re_length (re_take_until t r).
Proof.
  intros ?? Hi. assert (length (str_take i s) = Z.to_nat i) as <-.
  { unfold str_take. rewrite length_take, min_l; [done|].
    subst. apply str_index_of_nonneg_lt_length in Hi. lia. }
  by apply elem_of_re_length, elem_of_re_take_until.
Qed.

(* Index of Char-At *)

(* Lemma infer_index_of_char_at_lemma i s c r :
  str_at i s = [c] →
  s ∈ r →
  Z.to_nat i ∈ re_length (re_take_until [c] r).
Proof.
  intros Hi ?. assert (length (str_take i s) = Z.to_nat i) as <-.
  { unfold str_take. rewrite length_take, min_l; [done|].
    apply str_at_singleton_lt_length in Hi. lia. }
  apply elem_of_re_length. apply elem_of_re_take_until. admit.
Admitted. *)

(* Char-At *)

Lemma infer_char_at_lemma i s C :
  str_at i s ∈ re_lit C →
  Exists (λ c, str_at i s = [c]) (elements C).
Proof.
  intros Hi. apply elem_of_re_lit_inv in Hi as [c [??]].
  apply Exists_exists. exists c. split; [by apply elem_of_elements | done].
Qed.
