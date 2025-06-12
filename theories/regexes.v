From stdpp Require Import listset.

Definition char : Type := nat.

Definition charset : Type := listset char.

Definition charset_delete (C : charset) (c : char) : charset :=
  let l := listset_car C in
  {| listset_car := filter (λ x, x ≠ c) l |}.

Notation "C #- c" := (charset_delete C c) (at level 60).

Lemma elem_of_charset_delete c C c' :
  c ∈ C →
  c ≠ c' →
  c ∈ C #- c'.
Proof.
  intros. by apply elem_of_list_filter.
Qed.

(** * Strings *)

Definition str : Type := list char.

Definition ε : str := [].

Definition substr (s: str) (i : nat) (j : nat) : str :=
  if bool_decide (i < j) then take (j - i) (drop i s) else ε.

Fixpoint index_of (s : str) (c : char) : option nat :=
  match s with
  | [] => None
  | c' :: s' => if bool_decide (c' = c) then Some 0 else S <$> (index_of s' c)
  end.

(** * Regular expressions and languages. *)

Inductive regex : Type :=
  | re_none : regex
  | re_null : regex
  | re_lit : charset → regex
  | re_concat : regex → regex → regex
  | re_union : regex → regex → regex
  | re_star : regex → regex
  .
Global Instance regex_empty : Empty regex := re_none.
Global Instance regex_union : Union regex := re_union.
Infix "++ᵣ" := re_concat (right associativity, at level 60).

Fixpoint regex_from_str (s : str) : regex :=
  match s with
  | [] => re_null
  | c :: cs => re_lit {[c]} ++ᵣ regex_from_str cs
  end.
Global Instance regex_singleton : Singleton str regex := regex_from_str.

Inductive elem_of_regex : ElemOf str regex :=
  | elem_of_null :
    ε ∈ re_null
  | elem_of_lit C c :
    c ∈ C → [c] ∈ re_lit C
  | elem_of_concat r1 r2 s1 s2 :
    s1 ∈ r1 → s2 ∈ r2 → s1 ++ s2 ∈ r1 ++ᵣ r2
  | elem_of_union_l r1 r2 s:
    s ∈ r1 → s ∈ r1 ∪ r2
  | elem_of_union_r r1 r2 s :
    s ∈ r2 → s ∈ r1 ∪ r2
  | elem_of_star_zero r :
    ε ∈ re_star r
  | elem_of_star_many r s1 s2 :
    s1 ≠ ε → s1 ∈ r → s2 ∈ re_star r → s1 ++ s2 ∈ re_star r
  .
Global Existing Instance elem_of_regex.

Section regex_lemmas.

  Implicit Type c : char.
  Implicit Type C : charset.
  Implicit Type s : str.
  Implicit Type r : regex.

  Lemma str_app_cons c s :
    c :: s = [c] ++ s.
  Proof. naive_solver. Qed.

  Lemma elem_of_concat_lit c C s r :
    c ∈ C →
    s ∈ r →
    c :: s ∈ re_lit C ++ᵣ r.
  Proof.
    rewrite str_app_cons. constructor; [by constructor | done].
  Qed.

  Lemma regex_elem_of_singleton s1 s2 :
    s1 ∈ regex_from_str s2 ↔ s1 = s2.
  Proof.
    split.
    + revert s1. induction s2 as [|c s] => s1; simpl.
      - by inversion 1.
      - inversion 1 as [|?|???? Hc|?|?|?|?]; subst.
        inversion Hc as [|? ? Hc'|?|?|?|?|?]; subst; clear Hc.
        apply elem_of_singleton in Hc' as ->. naive_solver.
    + intros ->. induction s2.
      - constructor.
      - simpl. rewrite str_app_cons. constructor; [|done].
        constructor. by apply elem_of_singleton.
  Qed.

  Lemma regex_elem_of_union s r1 r2 :
    s ∈ r1 ∪ r2 ↔ s ∈ r1 ∨ s ∈ r2.
  Proof.
    split.
    + inversion 1; eauto.
    + intros [?|?]; by constructor.
  Qed. 

  Global Instance regex_semi_set : SemiSet str regex.
  Proof.
    split.
    + inversion 1.
    + intros. apply regex_elem_of_singleton.
    + intros. apply regex_elem_of_union.
  Qed.

  Fixpoint nullable (r : regex) : bool :=
    match r with
    | re_none => false
    | re_null => true
    | re_lit _ => false
    | re_concat r1 r2 => nullable r1 && nullable r2
    | re_union r1 r2 => nullable r1 || nullable r2
    | re_star _ => true
    end.

  Lemma nullable_spec r :
    nullable r ↔ ε ∈ r.
  Proof.
    split.
    + (* -> *)
      induction r; [done|constructor|done|simpl..|constructor].
      - rewrite andb_True.
        intros [??]. replace ε with (ε ++ ε) by done. constructor; auto.
      - rewrite orb_True.
        intros [?|?]; [apply elem_of_union_l | apply elem_of_union_r]; auto.
    + (* <- *)
      induction r; inversion 1 as [|?|?? s1 s2|?|?|?|?]; subst; simpl; [done|..|done|done].
      - rewrite andb_True. pose (app_eq_nil s1 s2). naive_solver.
      - rewrite orb_True. left. auto.
      - rewrite orb_True. right. auto.
  Qed.

  Global Instance regex_null_dec r : Decision (ε ∈ r).
  Proof.
    destruct (nullable r) eqn:Heq.
    - apply Is_true_true in Heq. left. by apply nullable_spec.
    - apply Is_true_false in Heq. right => ?. by apply Heq, nullable_spec.
  Qed.

End regex_lemmas.