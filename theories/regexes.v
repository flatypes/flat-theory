From stdpp Require Import list well_founded.
From flat Require Export strings.

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
Infix "⧺" := re_concat (right associativity, at level 60).

Fixpoint regex_from_str (s : str) : regex :=
  match s with
  | [] => re_null
  | c :: cs => re_lit {[c]} ⧺ regex_from_str cs
  end.
Global Instance regex_singleton : Singleton str regex := regex_from_str.

Inductive elem_of_regex : ElemOf str regex :=
  | elem_of_null :
    [] ∈ re_null
  | elem_of_lit C c :
    c ∈ C → [c] ∈ re_lit C
  | elem_of_concat r1 r2 s1 s2 :
    s1 ∈ r1 → s2 ∈ r2 → s1 ++ s2 ∈ r1 ⧺ r2
  | elem_of_union_l r1 r2 s:
    s ∈ r1 → s ∈ r1 ∪ r2
  | elem_of_union_r r1 r2 s :
    s ∈ r2 → s ∈ r1 ∪ r2
  | elem_of_star_zero r :
    [] ∈ re_star r
  | elem_of_star_many r s1 s2 :
    s1 ≠ [] → s1 ∈ r → s2 ∈ re_star r → s1 ++ s2 ∈ re_star r
  .
Global Existing Instance elem_of_regex.

Lemma elem_of_re_lit_inv s C :
  s ∈ re_lit C → ∃ c, s = [c] ∧ c ∈ C.
Proof. inv 1. eauto. Qed.

Fixpoint re_power (r : regex) (n : nat) : regex :=
  match n with
  | O => re_null
  | S n' => r ⧺ re_power r n'
  end.

Notation "r ^ n" := (re_power r n).

Fixpoint nullable (r : regex) : bool :=
  match r with
  | re_none => false
  | re_null => true
  | re_lit _ => false
  | re_concat r1 r2 => nullable r1 && nullable r2
  | re_union r1 r2 => nullable r1 || nullable r2
  | re_star _ => true
  end.

Fixpoint re_rev (r : regex) : regex :=
  match r with
  | re_concat r1 r2 => re_rev r2 ⧺ re_rev r1
  | re_union r1 r2 => re_rev r1 ∪ re_rev r2
  | re_star r => re_star (re_rev r)
  | _ => r
  end.

Section regex_lemmas.

  Implicit Type c : char.
  Implicit Type C : charset.
  Implicit Type s : str.
  Implicit Type r : regex.

  Lemma str_app_cons c s :
    [c] ++ s = c :: s.
  Proof. naive_solver. Qed.

  Lemma elem_of_concat_lit c C s r :
    c ∈ C →
    s ∈ r →
    c :: s ∈ re_lit C ⧺ r.
  Proof.
    rewrite <-str_app_cons. constructor; [by constructor | done].
  Qed.

  Lemma elem_of_re_power_app s1 s2 n1 n2 r :
    s1 ∈ r ^ n1 →
    s2 ∈ r ^ n2 →
    s1 ++ s2 ∈ r ^ (n1 + n2).
  Proof.
    revert s1 s2. induction n1; simpl => s1 s2.
    all: inversion 1; subst => ?.
    - by rewrite app_nil_l.
    - rewrite <-app_assoc. constructor; auto.
  Qed.

  Local Definition str_length_ind :=
    well_founded_induction (well_founded_ltof str length).

  Lemma elem_of_re_star_power s r :
    s ∈ re_star r ↔ ∃ n, s ∈ r ^ n.
  Proof.
    split.
    + induction s as [s IHs] using str_length_ind. unfold ltof in IHs.
      inversion 1 as [|?|?|?|?|?|? s1 s2]; subst.
      - exists O. constructor.
      - destruct (nil_or_length_pos s1) as [?|?]; [done|].
        edestruct (IHs s2) as [n ?]; [rewrite length_app; lia | done|].
        exists (S n). simpl. by constructor.
    + intros [n Hs].
      generalize dependent s. induction n as [|n']; inversion 1; subst.
      - constructor.
      - destruct s1; [auto | constructor; eauto].
  Qed.

  Lemma elem_of_re_star_app s1 s2 r :
    s1 ∈ re_star r →
    s2 ∈ re_star r →
    s1 ++ s2 ∈ re_star r.
  Proof.
    rewrite !elem_of_re_star_power. intros [n1 ?] [n2 ?].
    exists (n1 + n2). by apply elem_of_re_power_app.
  Qed.

  Lemma re_elem_of_singleton s1 s2 :
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
      - simpl. rewrite <-str_app_cons. constructor; [|done].
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
    + intros. apply re_elem_of_singleton.
    + intros. apply regex_elem_of_union.
  Qed.

  Lemma nullable_spec r :
    nullable r ↔ [] ∈ r.
  Proof.
    split.
    + (* -> *)
      induction r; [done|constructor|done|simpl..|constructor].
      - rewrite andb_True.
        intros [??]. rewrite <-app_nil_l at 1. constructor; auto.
      - rewrite orb_True.
        intros [?|?]; [apply elem_of_union_l | apply elem_of_union_r]; auto.
    + (* <- *)
      induction r; inversion 1 as [|?|?? s1 s2|?|?|?|?]; subst; simpl; [done|..|done|done].
      - rewrite andb_True. pose (app_eq_nil s1 s2). naive_solver.
      - rewrite orb_True. left. auto.
      - rewrite orb_True. right. auto.
  Qed.

  Global Instance regex_null_dec r : Decision ([] ∈ r).
  Proof.
    destruct (nullable r) eqn:Heq.
    - apply Is_true_true in Heq. left. by apply nullable_spec.
    - apply Is_true_false in Heq. right => ?. by apply Heq, nullable_spec.
  Qed.

  Lemma elem_of_re_rev s r :
    s ∈ r →
    reverse s ∈ re_rev r.
  Proof.
    induction 1; simpl.
    - setoid_rewrite reverse_nil. constructor.
    - rewrite reverse_singleton. by constructor.
    - rewrite reverse_app. by constructor.
    - apply elem_of_union. by left.
    - apply elem_of_union. by right.
    - setoid_rewrite reverse_nil. constructor.
    - rewrite reverse_app. simpl in *.
      apply elem_of_re_star_app; [done|].
      rewrite <-app_nil_r at 1. constructor; [|done|constructor].
      setoid_rewrite <-reverse_nil. naive_solver.
  Qed.

  Global Instance re_empty_dec (r : regex) : Decision (r ≡ ∅).
  Admitted.

  Global Instance re_singleton_dec (r : regex) (c : char) : Decision (r ≡ {[ [c] ]}).
  Admitted.

End regex_lemmas.

(** Brzozowski derivative *)

  Fixpoint d_char (c : char) (r : regex) : regex :=
    match r with
    | re_none => ∅
    | re_null => ∅
    | re_lit C => if bool_decide (c ∈ C) then re_null else ∅
    | re_concat r1 r2 => (d_char c r1 ⧺ r2) ∪ (if bool_decide ([] ∈ r1) then d_char c r2 else ∅)
    | re_union r1 r2 => d_char c r1 ∪ d_char c r2
    | re_star r => d_char c r ⧺ re_star r
    end.

  Lemma elem_of_d_char s c r :
    s ∈ d_char c r ↔ c :: s ∈ r.
  Proof.
    split.
    + revert s. induction r => s; simpl; intros Hr.
      - by apply not_elem_of_empty in Hr.
      - by apply not_elem_of_empty in Hr.
      - case_bool_decide; [|by apply not_elem_of_empty in Hr].
        inv Hr. by constructor.
      - apply elem_of_union in Hr as [Hr|Hr].
        * inv Hr. rewrite app_comm_cons. constructor; [auto|done].
        * case_bool_decide; [|by apply not_elem_of_empty in Hr].
          rewrite <-(app_nil_l (c :: s)). constructor; [done|auto].
      - apply elem_of_union. apply elem_of_union in Hr as [?|?]; auto.
      - inv Hr. rewrite app_comm_cons. constructor; [done|auto|done].
    + revert s. induction r => s.
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

  Fixpoint d_str (t : str) (r : regex) : regex :=
    match t with
    | [] => r
    | c :: t' => d_str t' (d_char c r)
    end.

  Lemma elem_of_d_str t s r :
    s ∈ d_str t r ↔ t ++ s ∈ r.
  Proof.
    revert r. induction t => r; simpl. { done. } by rewrite <-elem_of_d_char.
  Qed.
