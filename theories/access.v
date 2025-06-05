From Coq Require Import ssreflect.
From stdpp Require Import list.
From flat Require Import regexes.

Fixpoint re_head_tail (r : regex) : list (charset * regex) :=
  match r with
  | re_none | re_null => []
  | re_lit C => [(C, re_null)]
  | re_concat r1 r2 =>
    let cuts1 := (λ p, match p with (c, r') => (c, re_concat r' r2) end) <$> re_head_tail r1 in
    let cuts2 := if nullable r1 then re_head_tail r2 else [] in
    cuts1 ++ cuts2
  | re_union r1 r2 =>
    re_head_tail r1 ++ re_head_tail r2
  | re_star r1 =>
    (λ p, match p with (c, r') => (c, re_concat r' r) end) <$> re_head_tail r1
  end.

Lemma re_head_tail_spec s r c :
  s ∈ r → head s = Some c →
  ∃ C r', (C, r') ∈ re_head_tail r ∧ c ∈ C ∧ tail s ∈ r'.
Proof.
  move: s.
  induction 1 as [|?|????? IH1 ? IH2|???? IH1|???? IH2|?|???? IH1 ? IH2] => // Hs.
  - inversion Hs; subst; clear Hs.
    exists C, re_null. split; last split; [|done|constructor].
    simpl. by rewrite elem_of_list_singleton.
  - destruct s1.
    + destruct IH2 as [C [r' [? [? ?]]]]; first done.
      exists C, r'. split; last split; [|done..].
      simpl. have -> : nullable r1 = true by rewrite nullable_spec.
      rewrite elem_of_app. by right.
    + destruct IH1 as [C [r' [? [? ?]]]]; first done.
      exists C, (re_concat r' r2). split; last split; [|done|by constructor].
      simpl. rewrite elem_of_app elem_of_list_fmap. left. by exists (C, r').
  - destruct IH1 as [C [r' [? [? ?]]]]; first done.
    exists C, r'. split; last split; [|done..].
    simpl. rewrite elem_of_app. by left.
  - destruct IH2 as [C [r' [? [? ?]]]]; first done.
    exists C, r'. split; last split; [|done..].
    simpl. rewrite elem_of_app. by right.
  - destruct s1.
    + destruct IH2 as [C [r' [? [? ?]]]]; first done.
      exists C, r'. split; last split; done.
    + destruct IH1 as [C [r' [? [? ?]]]]; first done.
      exists C, (re_concat r' (re_star r)). split; last split; [|done|by constructor].
      simpl. rewrite elem_of_list_fmap. by exists (C, r').
Qed.