From stdpp Require Import list sets well_founded.
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

Inductive elem_of_regex : ElemOf str regex :=
  | elem_of_re_null :
    [] ∈ re_null
  | elem_of_re_lit σ L :
    σ ∈ L → [σ] ∈ re_lit L
  | elem_of_re_concat r1 r2 s1 s2 :
    s1 ∈ r1 → s2 ∈ r2 → s1 ++ s2 ∈ r1 ⧺ r2
  | elem_of_re_union_l r1 r2 s:
    s ∈ r1 → s ∈ r1 ∪ r2
  | elem_of_re_union_r r1 r2 s :
    s ∈ r2 → s ∈ r1 ∪ r2
  | elem_of_re_star_zero r :
    [] ∈ re_star r
  | elem_of_re_star_many r s1 s2 :
    s1 ≠ [] → s1 ∈ r → s2 ∈ re_star r → s1 ++ s2 ∈ re_star r
  .
Global Existing Instance elem_of_regex.

Lemma elem_of_re_concat_lit σ L s r :
  σ ∈ L →
  s ∈ r →
  σ :: s ∈ re_lit L ⧺ r.
Proof.
  intros.
  replace (σ :: s) with ([σ] ++ s) by done.
  constructor; [by constructor | done].
Qed.

Fixpoint str_to_regex (s : str) : regex :=
  match s with
  | [] => re_null
  | σ :: s' => re_lit {[σ]} ⧺ str_to_regex s'
  end.
Global Instance regex_singleton : Singleton str regex := str_to_regex.

Lemma elem_of_str_to_regex s1 s2 :
  s1 ∈ str_to_regex s2 ↔ s1 = s2.
Proof.
  split.
  + revert s1. induction s2 => s1; simpl. { by inv 1. }
    inv 1 as [|?|???? Hc|?|?|?|?]. inv Hc. set_solver.
  + intros ->. induction s2. { constructor. }
    simpl. apply elem_of_re_concat_lit; [set_solver|done].
Qed.

Global Instance regex_semi_set : SemiSet str regex.
Proof.
  split.
  + inv 1.
  + intros. apply elem_of_str_to_regex.
  + intros. split. { inv 1; auto. }
    intros [?|?]; [by apply elem_of_re_union_l | by apply elem_of_re_union_r].
Qed.

Fixpoint re_nullable (r : regex) : bool :=
  match r with
  | re_none => false
  | re_null => true
  | re_lit _ => false
  | re_concat r1 r2 => re_nullable r1 && re_nullable r2
  | re_union r1 r2 => re_nullable r1 || re_nullable r2
  | re_star _ => true
  end.

Lemma re_nullable_spec r :
  [] ∈ r ↔ re_nullable r.
Proof.
  induction r; simpl.
  - split; [inv 1|done].
  - split; [done|constructor].
  - split; [inv 1|done].
  - rewrite andb_True. split.
    + inv 1. pose (app_eq_nil s1 s2). naive_solver.
    + intros [??]. rewrite <-app_nil_l at 1. constructor; naive_solver.
  - rewrite orb_True. split.
    + inv 1; naive_solver.
    + intros [?|?]; apply elem_of_union; naive_solver.
  - split; [done|constructor].
Qed.

Global Instance regex_nullable_dec (r : regex) : Decision ([] ∈ r).
Proof.
  refine (cast_if (decide (re_nullable r))); by rewrite re_nullable_spec.
Qed.

Fixpoint re_rev (r : regex) : regex :=
  match r with
  | re_concat r1 r2 => re_rev r2 ⧺ re_rev r1
  | re_union r1 r2 => re_rev r1 ∪ re_rev r2
  | re_star r => re_star (re_rev r)
  | _ => r
  end.

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

Fixpoint d_str (t : str) (r : regex) : regex :=
  match t with
  | [] => r
  | c :: t' => d_str t' (d_char c r)
  end.

(** Extensions *)

Fixpoint re_power (r : regex) (n : nat) : regex :=
  match n with
  | 0 => re_null
  | S n' => r ⧺ re_power r n'
  end.

Infix "^" := re_power (no associativity).

Section regex_ops_properties.

  Implicit Type (s : str) (σ : char) (L : charset) (r : regex) (n : nat).
  
  Lemma empty_re_concat r1 r2 :
    r1 ≡ ∅ ∨ r2 ≡ ∅ → r1 ⧺ r2 ≡ ∅.
  Proof.
    intros [?|?]; rewrite elem_of_equiv_empty => s Hs; inv Hs; set_solver.
  Qed.

  Fixpoint re_empty (r : regex) : bool :=
    match r with
    | re_none => true
    | re_null => false
    | re_lit L => bool_decide (L ≡ ∅)
    | re_concat r1 r2 => re_empty r1 || re_empty r2
    | re_union r1 r2 => re_empty r1 && re_empty r2
    | re_star _ => false
    end.

  Lemma re_empty_true r :
    re_empty r = true → r ≡ ∅.
  Proof.
    induction r as [| | L | r1 IHr1 r2 IHr2 | r1 IHr1 r2 IHr2 | r];
      simpl; try done; intros Hr.
    - apply bool_decide_eq_true in Hr.
      apply elem_of_equiv_empty => s Hs. inv Hs. set_solver.
    - apply empty_re_concat. apply orb_true_iff in Hr as [?|?]; naive_solver.
    - apply empty_union. apply andb_true_iff in Hr. naive_solver.
  Qed.

  Lemma re_empty_false r :
    re_empty r = false → ∃ s, s ∈ r.
  Proof.
    induction r as [| | L | r1 IHr1 r2 IHr2 | r1 IHr1 r2 IHr2 | r];
      simpl; try done; intros Hr.
    - exists []. constructor.
    - apply bool_decide_eq_false in Hr.
      apply charset_nonempty_exists in Hr as [σ ?]. exists [σ]. by constructor.
    - apply orb_false_iff in Hr as [??].
      destruct IHr1 as [s1 ?]; [done|]. destruct IHr2 as [s2 ?]; [done|].
      exists (s1 ++ s2). by constructor.
    - setoid_rewrite elem_of_union.
      apply andb_false_iff in Hr as [?|?]; naive_solver.
    - exists []. constructor.
  Qed.

  Corollary re_empty_false_nonempty r :
    re_empty r = false → r ≢ ∅.
  Proof.
    intros Hr. apply re_empty_false in Hr as [s ?]. by apply (non_empty_inhabited s).
  Qed.

  Global Instance regex_empty_dec r : Decision (r ≡ ∅).
  Proof.
    refine (cast_if (decide (re_empty r))).
    - rewrite Is_true_true in *. by apply re_empty_true.
    - rewrite Is_true_false in *. by apply re_empty_false_nonempty.
  Qed.

  Global Instance re_singleton_dec r σ : Decision (r ≡ {[ [σ] ]}).
  Admitted.

  Lemma re_power_1 r :
    r ^ 1 ≡ r.
  Proof.
    split; simpl.
    + inv 1. inv H4. by rewrite app_nil_r.
    + intros. simpl. rewrite <-app_nil_r at 1. constructor; [done|constructor].
  Qed.

  Lemma elem_of_re_power_plus s1 s2 n1 n2 r :
    s1 ∈ r ^ n1 →
    s2 ∈ r ^ n2 →
    s1 ++ s2 ∈ r ^ (n1 + n2).
  Proof.
    revert s1 s2. induction n1; simpl => s1 s2.
    all: inversion 1; subst => ?.
    - by rewrite app_nil_l.
    - rewrite <-app_assoc. constructor; auto.
  Qed.

  Local Definition length_ind :=
    well_founded_induction (well_founded_ltof str length).

  Lemma elem_of_re_star_power s r :
    s ∈ re_star r ↔ ∃ n, s ∈ r ^ n.
  Proof.
    split.
    + induction s as [s IHs] using length_ind. unfold ltof in IHs.
      inversion 1 as [|?|?|?|?|?|? s1 s2]; subst.
      - exists 0. constructor.
      - destruct (nil_or_length_pos s1) as [?|?]; [done|].
        edestruct (IHs s2) as [n ?]; [rewrite length_app; lia | done|].
        exists (S n). simpl. by constructor.
    + intros [n Hs].
      generalize dependent s. induction n as [|n']; inversion 1; subst.
      - constructor.
      - destruct s1; [auto | constructor; eauto].
  Qed.

  Lemma elem_of_re_rev s r :
    s ∈ r →
    reverse s ∈ re_rev r.
  Proof.
    induction 1 as [| | | | | |r s1 s2 ?? IHr1 ? IHr2]; simpl.
    - setoid_rewrite reverse_nil. constructor.
    - rewrite reverse_singleton. by constructor.
    - rewrite reverse_app. by constructor.
    - apply elem_of_union. by left.
    - apply elem_of_union. by right.
    - setoid_rewrite reverse_nil. constructor.
    - rewrite reverse_app. apply elem_of_re_star_power.
      simpl in IHr2. apply elem_of_re_star_power in IHr2 as [n ?].
      exists (n + 1). apply elem_of_re_power_plus; [done|].
      by rewrite re_power_1.
  Qed.

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

  Lemma elem_of_d_str t s r :
    s ∈ d_str t r ↔ t ++ s ∈ r.
  Proof.
    revert r. induction t => r; simpl. { done. } by rewrite <-elem_of_d_char.
  Qed.

End regex_ops_properties.
