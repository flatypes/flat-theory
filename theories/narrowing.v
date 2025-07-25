From stdpp Require Import list sets.
From flat Require Import regexes inference.

Section length_cmp.

  Fixpoint re_length_in (I : interval) (r : regex) : regex :=
    match r with
    | re_none => ∅
    | re_null => if bool_decide (0 ∈ I) then r else ∅
    | re_lit _ => if bool_decide (1 ∈ I) then r else ∅
    | re_concat r1 r2 =>
      match interval_to_nat (re_length r1), interval_to_nat (re_length r2) with
      | Some k, _ => r1 ⧺ re_length_in (I -ₙ k)%interval r2
      | _, Some k => re_length_in (I -ₙ k)%interval r1 ⧺ r2
      | _, _ => r1 ⧺ r2
      end
    | re_union r1 r2 => re_length_in I r1 ∪ re_length_in I r2
    | re_star r =>
      match interval_to_nat (re_length r) with
      | Some (S n) => let k := S n in re_loop (I /ₙ k)%interval r
      | _ => if bool_decide (0 ∉ I) then re_plus r else re_star r
      end
    end.

  Lemma narrow_length_sound s r I :
    s ∈ r →
    length s ∈ I →
    s ∈ re_length_in I r.
  Proof.
    revert s I. induction r as [| |?|r1 IHr1 r2 IHr2|?|?] => s I; simpl.
    - inv 1.
    - inv 1. simpl. intros. rewrite bool_decide_true by done. constructor.
    - inv 1. simpl. intros. rewrite bool_decide_true by done. by constructor.
    - inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. intros.
      case_match eqn:Heq1; [|case_match eqn:Heq2].
      * constructor; [done|]. apply IHr2; [done|].
        rewrite <-(Nat.add_sub' (length s1)), <-length_app at 1.
        apply elem_of_re_length in Hs1. rewrite (interval_to_nat_spec _ _ _ Heq1 Hs1).
        by apply elem_of_interval_minus_nat.
      * constructor; [|done]. apply IHr1; [done|].
        rewrite <-(Nat.add_sub _ (length s2)), <-length_app at 1.
        apply elem_of_re_length in Hs2. rewrite (interval_to_nat_spec _ _ _ Heq2 Hs2).
        by apply elem_of_interval_minus_nat.
      * by constructor.
    - inv 1; intros; set_solver.
    - intros Hs HI. case_match eqn:Heq; [case_match|].
      1,3: case_bool_decide; [|done]; inv Hs; [set_solver|]; by constructor.
      apply elem_of_re_star_pow in Hs as [k Hs]. apply (elem_of_weaken _ _ _ Hs).
      apply re_pow_subseteq_loop, elem_of_interval_div_nat; [lia|].
      assert (length s = n * k).
      { clear IHr HI. generalize dependent s. induction k as [|k' IHk'] => s Hs; [by inv Hs|].
        inv Hs as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?].
        rewrite length_app, Nat.mul_succ_r, Nat.add_comm. f_equal; [auto|].
        apply elem_of_re_length in Hs1. by eapply interval_to_nat_spec. }
      congruence.
  Qed.

(* Lemma refine_index_of s r t i R :
  s ∈ r →
  find s t = i →
  (0 ≤ i)%Z →
  Z.to_nat i ∈ R →
  s ∈ (re_length_in R (re_take_until t r)) ⧺ re_drop_until t r.
Proof.
  intros ? Hi ??.
  rewrite <-(str_take_drop i) at 1 by lia. constructor.
  + apply refine_length; [by apply elem_of_re_take_until|].
    unfold str_take. rewrite length_take, min_l; [done|].
    apply str_index_of_range in Hi. lia.
  + by apply elem_of_re_drop_until.
Qed. *)

End length_cmp.

Section char_at_eq.

  Fixpoint re_split_at_at_0 (r : regex) : list (charset * regex) :=
    match r with
    | re_none => []
    | re_null => []
    | re_lit C => if bool_decide (C ≡ ∅) then [] else [(C, re_null)]
    | re_concat r1 r2 =>
      ((λ '(C, r'), (C, r' ⧺ r2)) <$> re_split_at_at_0 r1) ++
      (if bool_decide ([] ∈ r1) then re_split_at_at_0 r2 else [])
    | re_union r1 r2 => re_split_at_at_0 r1 ++ re_split_at_at_0 r2
    | re_star r => (λ '(C, r'), (C, r' ⧺ re_star r)) <$> re_split_at_at_0 r
    end.

  Lemma elem_of_re_split_at_at_0 s r c :
    s ∈ r →
    head s = Some c →
    ∃ C r', (C, r') ∈ re_split_at_at_0 r ∧ c ∈ C ∧ tail s ∈ r'.
  Proof.
    induction 1 as [|c' C|r1 r2 s1 s2 ? IHr1 ? IHr2|
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

  Fixpoint re_split_at (i : nat) (r : regex) : list (regex * charset * regex) :=
    match i with
    | 0 => (λ '(C, r'), (re_null, C, r')) <$> re_split_at_at_0 r
    | S i' =>
      '(C, r') ← re_split_at_at_0 r ;
      '(r1, C', r2) ← re_split_at i' r' ;
      [(re_lit C ⧺ r1, C', r2)]
    end.

  Lemma elem_of_re_split_at s r i c :
    s ∈ r →
    s !! i = Some c →
    ∃ r1 C r2, (r1, C, r2) ∈ re_split_at i r ∧ c ∈ C ∧ (take i s) ∈ r1 ∧ (drop (S i) s) ∈ r2.
  Proof.
    revert s r c. induction i as [|i' IHi'] => s r c Hs ?.
    - edestruct elem_of_re_split_at_at_0 as [C [r' [? [??]]]]; [done | by rewrite head_lookup|].
      exists re_null, C, r'. repeat split; [|done|constructor|done].
      unfold re_split_at. apply elem_of_list_fmap. eexists. split; [|done]. done.
    - destruct s as [|c' s']; [done|]. simplify_list_eq.
      edestruct elem_of_re_split_at_at_0 as [C [r' [? [? Hs']]]]; [done..|].
      specialize (IHi' _ _ c Hs') as [r1 [C' [r2 [? [? [??]]]]]]. { done. }
      exists (re_lit C ⧺ r1), C', r2. repeat split; [|done|..|done].
      + simpl. apply elem_of_list_bind. eexists. split; [|done].
        apply elem_of_list_bind. eexists. split; [|done]. set_solver.
      + by apply elem_of_re_concat_lit.
  Qed.

  Definition re_char_at_in (i : nat) (C : charset) (r : regex) : list regex :=
    '(r1, C1, r2) ← re_split_at i r ;
    let C' := C1 ∩ C in
    if bool_decide (C' ≢ ∅) then [r1 ⧺ re_lit C' ⧺ r2] else [].

  Lemma elem_of_re_char_at_in s r i σ C :
    s ∈ r →
    s !! i = Some σ →
    σ ∈ C →
    s ∈ ⋃ (re_char_at_in i C r).
  Proof.
    intros Hs ??. apply elem_of_union_list.
    eapply elem_of_re_split_at in Hs as [r1 [C1 [r2 [? [? [??]]]]]]; [|done].
    exists (r1 ⧺ re_lit (C1 ∩ C) ⧺ r2). split.
    + unfold re_char_at_in. apply elem_of_list_bind. eexists. split; [|done].
      case_match. simplify_eq. rewrite bool_decide_true; set_solver.
    + rewrite <-(take_drop i) at 1. constructor; [done|].
      rewrite (drop_S _ σ i) by done. apply elem_of_re_concat_lit; [set_solver | done].
  Qed.

End char_at_eq.