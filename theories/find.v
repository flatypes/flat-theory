From stdpp Require Import sets.
From flat Require Import regexes.

Fixpoint cut_by (s : str) (c : char) : option (str * str) :=
  match s with
  | [] => None
  | c' :: s' =>
    if bool_decide (c' = c) then Some (ε, s)
    else '(s'l, s'r) ← cut_by s' c; Some (c' :: s'l, s'r)
  end.

Lemma cut_by_app s1 s2 c :
  cut_by (s1 ++ s2) c =
    match cut_by s1 c with
    | Some (s1l, s1r) => Some (s1l, s1r ++ s2)
    | None => '(s2l, s2r) ← cut_by s2 c; Some (s1 ++ s2l, s2r)
    end.
Proof.
  induction s1 as [|c' s IHs]; simpl.
  - by destruct (cut_by s2 c) as [[? ?]|].
  - case_bool_decide; [done|].
    rewrite IHs.
    destruct (cut_by s c) as [[? ?]|]; [done|].
    by destruct (cut_by s2 c) as [[? ?]|].
Qed.

Fixpoint a_cut_by (r : regex) (c : char) : (list (regex * regex) * regex) :=
  match r with
  | re_none => ([], ∅)
  | re_null => ([], re_null)
  | re_lit C =>
    if bool_decide (c ∈ C) then ([(re_null, re_lit {[c]})], re_lit (C #- c))
    else ([], re_lit C)
  | re_concat r1 r2 =>
    let '(cuts1, r1') := a_cut_by r1 c in
    let '(cuts2, r2') := a_cut_by r2 c in
    (((λ '(r1l, r1r), (r1l, r1r ++ᵣ r2)) <$> cuts1) ++
     ((λ '(r2l, r2r), (r1' ++ᵣ r2l, r2r)) <$> cuts2), r1' ++ᵣ r2')
  | re_union r1 r2 =>
    let '(cuts1, r1') := a_cut_by r1 c in
    let '(cuts2, r2') := a_cut_by r2 c in
    (cuts1 ++ cuts2, r1' ∪ r2')
  | re_star r => 
    let '(cuts, r') := a_cut_by r c in
    ((λ '(rl, rr), (re_star r' ++ᵣ rl, rr ++ᵣ re_star r)) <$> cuts, re_star r')
  end.

Lemma a_cut_by_sound s r c :
  s ∈ r →
  match cut_by s c with
  | Some (s1, s2) => ∃ r1 r2, s1 ∈ r1 ∧ s2 ∈ r2 ∧ (r1, r2) ∈ (a_cut_by r c).1
  | None => s ∈ (a_cut_by r c).2
  end.
Proof.
  induction 1 as [|C c'|r1 r2 s1 s2 ? IHr1 ? IHr2|
    r1 r2 s Hr IHr|r1 r2 s Hr IHr|r|r s1 s2 ? Hr1 IHr1 Hr2 IHr2]; simpl.
  - constructor.
  - case_bool_decide; [|case_bool_decide]; subst; simpl.
    * rewrite bool_decide_true by done. simpl.
      do 2 eexists. repeat split; [..|by apply elem_of_list_singleton]; constructor.
      by apply elem_of_singleton.
    * constructor. by apply elem_of_charset_delete.
    * by constructor.
  - destruct (a_cut_by r1 c) as [? r1']. destruct (a_cut_by r2 c) as [? r2']. simpl.
    rewrite cut_by_app.
    destruct (cut_by s1 c) as [[s1l s1r]|]; [|destruct (cut_by s2 c) as [[s2l s2r]|]]; simpl.
    * destruct IHr1 as [r1l [r1r [? [??]]]]; [done..|].
      exists r1l, (r1r ++ᵣ r2). split; [done|]. split; [by constructor|].
      apply elem_of_app. left.
      apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
    * simpl in IHr1. destruct IHr2 as [r2l [r2r [? [??]]]]; [done..|].
      exists (r1' ++ᵣ r2l), r2r. split; [by constructor|]. split; [done|].
      apply elem_of_app. right.
      apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
    * by constructor.
  - destruct (a_cut_by r1 c) as [? r1']. destruct (a_cut_by r2 c) as [? r2']. simpl.
    destruct (cut_by s c) as [[sl sr]|].
    * destruct IHr as [rl [rr [? [??]]]]; [done..|].
      exists rl, rr. split; [done|]. split; [done|].
      apply elem_of_app. by left.
    * apply elem_of_union. by left.
  - destruct (a_cut_by r1 c) as [? r1']. destruct (a_cut_by r2 c) as [? r2']. simpl.
    destruct (cut_by s c) as [[sl sr]|].
    * destruct IHr as [rl [rr [? [??]]]]; [done..|].
      exists rl, rr. split; [done|]. split; [done|].
      apply elem_of_app. by right.
    * apply elem_of_union. by right.
  - destruct (a_cut_by r c) as [? r']. simpl. constructor.
  - simpl in IHr2. destruct (a_cut_by r c) as [? r'].
    rewrite cut_by_app.
    destruct (cut_by s1 c) as [[s1l s1r]|]; [|destruct (cut_by s2 c) as [[s2l s2r]|]]; simpl.
    * destruct IHr1 as [r1l [r1r [? [??]]]]; [done..|].
      exists (re_star r' ++ᵣ r1l), (r1r ++ᵣ re_star r).
      split. { rewrite <-(app_nil_l s1l). constructor; [constructor | done]. }
      split; [by constructor|].
      apply elem_of_list_fmap. eexists. split; [|done]. naive_solver.
    * simpl in IHr1, IHr2. destruct IHr2 as [r2l [r2r [Hr2l [? IHr2]]]]; [done..|].
      exists r2l, r2r. split; [|done].
      apply elem_of_list_fmap in IHr2 as [[? ?] [IHr2 ?]].
      inversion IHr2; subst; clear IHr2.
      inversion Hr2l; subst; clear Hr2l.
      rewrite app_assoc. constructor; [by constructor | done].
    * simpl in IHr1, IHr2. by constructor.
Qed.
