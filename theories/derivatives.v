From stdpp Require Import sets.
From flat Require Import regexes.

Fixpoint first_set (r : regex) : charset :=
  match r with
  | re_none => ∅
  | re_null => ∅
  | re_lit C => C
  | re_concat r1 r2 => first_set r1 ∪ (if bool_decide (ε ∈ r1) then first_set r2 else ∅)
  | re_union r1 r2 => first_set r1 ∪ first_set r2
  | re_star r => first_set r
  end.

Lemma elem_of_first_set c s r :
  c :: s ∈ r → c ∈ first_set r.
Proof.
  revert s. induction r => s.
  all: inversion 1 as [|?|?????? Heq|?|?|?|?????? Heq]; subst.
  - done.
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; simpl; apply elem_of_union.
    * right. rewrite bool_decide_true; eauto.
    * left. eauto.
  - simpl. apply elem_of_union. eauto.
  - simpl. apply elem_of_union. eauto.
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; naive_solver.
Qed.

(* Brzozowski derivative *)
Fixpoint d_char (c : char) (r : regex) : regex :=
  match r with
  | re_none => ∅
  | re_null => ∅
  | re_lit C => if bool_decide (c ∈ C) then re_null else ∅
  | re_concat r1 r2 => (d_char c r1 ++ᵣ r2) ∪ (if bool_decide (ε ∈ r1) then d_char c r2 else ∅)
  | re_union r1 r2 => d_char c r1 ∪ d_char c r2
  | re_star r => d_char c r ++ᵣ re_star r
  end.

Lemma elem_of_d_char c s r :
  c :: s ∈ r → s ∈ d_char c r.
Proof.
  revert s. induction r => s.
  all: inversion 1 as [|?|?????? Heq|?|?|?|?????? Heq]; subst.
  - simpl. case_bool_decide; [constructor | congruence].
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; simpl; apply elem_of_union.
    * right. rewrite bool_decide_true; eauto.
    * left. constructor; eauto.
  - simpl. apply elem_of_union. eauto.
  - simpl. apply elem_of_union. eauto.
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; [done|].
    simpl. constructor; eauto.
Qed.

Fixpoint d_all (r : regex) : regex :=
  match r with
  | re_none => ∅
  | re_null => ∅
  | re_lit C => if bool_decide (C ≡ ∅) then ∅ else re_null
  | re_concat r1 r2 => (d_all r1 ++ᵣ r2) ∪ (if bool_decide (ε ∈ r1) then d_all r2 else ∅)
  | re_union r1 r2 => d_all r1 ∪ d_all r2
  | re_star r => d_all r ++ᵣ re_star r
  end.

Lemma elem_of_d_all c s r :
  c :: s ∈ r → s ∈ d_all r.
Proof.
  revert s. induction r => s.
  all: inversion 1 as [|?|?????? Heq|?|?|?|?????? Heq]; subst.
  - simpl. case_bool_decide as Heq.
    * rewrite elem_of_equiv_empty in Heq. naive_solver.
    * constructor.
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; simpl; apply elem_of_union.
    * right. rewrite bool_decide_true; eauto.
    * left. constructor; eauto.
  - simpl. apply elem_of_union. eauto.
  - simpl. apply elem_of_union. eauto.
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; [done|].
    simpl. constructor; eauto.
Qed.

Fixpoint dd_all (r : regex) : list (charset * regex) :=
  match r with
  | re_none => []
  | re_null => []
  | re_lit C => if bool_decide (C ≡ ∅) then [] else [(C, re_null)]
  | re_concat r1 r2 => ((λ '(C, r'), (C, r' ++ᵣ r2)) <$> dd_all r1) ++
      (if bool_decide (ε ∈ r1) then dd_all r2 else [])
  | re_union r1 r2 => dd_all r1 ++ dd_all r2
  | re_star r => (λ '(C, r'), (C, r' ++ᵣ re_star r)) <$> dd_all r
  end.

Lemma elem_of_dd_all c s r :
  c :: s ∈ r →
  ∃ C r', c ∈ C ∧ s ∈ r' ∧ (C, r') ∈ dd_all r.
Proof.
  revert s. induction r as [| |?|? IHr1 ? IHr2|? IHr1 ? IHr2|r IHr] => s.
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
      exists C, (r' ++ᵣ r2). repeat split; [done | by constructor|].
      simpl. apply elem_of_app. left. apply elem_of_list_fmap. naive_solver.
  - edestruct IHr1 as [C [r' [? [??]]]]; eauto.
    exists C, r'. repeat split; [done..|].
    simpl. apply elem_of_app. by left.
  - edestruct IHr2 as [C [r' [? [??]]]]; eauto.
    exists C, r'. repeat split; [done..|].
    simpl. apply elem_of_app. by right.
  - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; [naive_solver|].
    edestruct IHr as [C [r' [? [??]]]]; eauto.
    exists C, (r' ++ᵣ re_star r). repeat split; [done | by constructor|].
    simpl. apply elem_of_list_fmap. naive_solver.
Qed.