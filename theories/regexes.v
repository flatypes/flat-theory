From stdpp Require Import list sets well_founded.
From flat Require Export strings.

(** * Regular Languages *)

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
    inv 1 as [|?|???? Hσ|?|?|?|?]. inv Hσ. set_solver.
  + intros ->. induction s2; [constructor|].
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

(** ** Extensions *)

Definition re_plus (r : regex) : regex := r ⧺ re_star r.
Definition re_opt (r : regex) : regex := r ∪ re_null.

Fixpoint re_pow (r : regex) (n : nat) : regex :=
  match n with
  | 0 => re_null
  | S n' => r ⧺ re_pow r n'
  end.
Infix "^" := re_pow.

(** ** Basic Operations *)

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
    + inv 1 as [|?|?? s1 s2|?|?|?|?]. pose (app_eq_nil s1 s2). naive_solver.
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

(** * Properties *)

Section regex_ops_properties.

  Implicit Type (s : str) (σ : char) (L : charset) (r : regex) (n : nat).
  
  (** ** Emptiness *)

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
    induction r; simpl; try done; intros Hr.
    - apply bool_decide_eq_true in Hr.
      apply elem_of_equiv_empty => s Hs. inv Hs. set_solver.
    - apply empty_re_concat. apply orb_true_iff in Hr as [?|?]; naive_solver.
    - apply empty_union. apply andb_true_iff in Hr. naive_solver.
  Qed.

  Lemma re_empty_false r :
    re_empty r = false → ∃ s, s ∈ r.
  Proof.
    induction r as [| |?|r1 IHr1 r2 IHr2|?|?]; simpl; try done; intros Hr.
    - exists []. constructor.
    - apply bool_decide_eq_false in Hr.
      apply non_empty_elem_of in Hr as [σ ?]. exists [σ]. by constructor.
    - apply orb_false_iff in Hr as [??].
      destruct IHr1 as [s1 ?]; [done|]. destruct IHr2 as [s2 ?]; [done|].
      exists (s1 ++ s2). by constructor.
    - setoid_rewrite elem_of_union.
      apply andb_false_iff in Hr as [?|?]; naive_solver.
    - exists []. constructor.
  Qed.

  Lemma re_empty_spec r :
    r ≡ ∅ ↔ re_empty r.
  Proof.
    split.
    + intros. apply Is_true_true. apply not_false_iff_true => Hr.
      apply re_empty_false in Hr. set_solver.
    + intros. apply re_empty_true. by apply Is_true_true.
  Qed.

  Global Instance regex_empty_dec r : Decision (r ≡ ∅).
  Proof.
    refine (cast_if (decide (re_empty r))); by rewrite re_empty_spec.
  Qed.

  (** ** Properties of [re_pow] *)

  Lemma re_pow_1 r :
    r ^ 1 ≡ r.
  Proof.
    split; simpl.
    + inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. inv Hs2. by simplify_list_eq.
    + intros. simpl. rewrite <-app_nil_r at 1. constructor; [done|constructor].
  Qed.

  Lemma elem_of_re_pow_plus s1 s2 r n1 n2 :
    s1 ∈ r ^ n1 →
    s2 ∈ r ^ n2 →
    s1 ++ s2 ∈ r ^ (n1 + n2).
  Proof.
    revert s1 s2. induction n1; simpl => s1 s2; inv 1; intros; simplify_list_eq; [done|].
    constructor; auto.
  Qed.

  Lemma elem_of_re_pow_plus_inv s r n1 n2 :
    s ∈ r ^ (n1 + n2) →
    ∃ s1 s2, s = s1 ++ s2 ∧ s1 ∈ r ^ n1 ∧ s2 ∈ r ^ n2.
  Proof.
    revert s. induction n1 as [|n1' IHn1']; simpl.
    - intros. exists [], s. repeat split; [constructor|done].
    - inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. apply IHn1' in Hs2 as [s2l [s2r [? [??]]]].
      exists (s1 ++ s2l), s2r. simplify_list_eq. repeat split; [by constructor | done].
  Qed.

  Local Definition length_ind :=
    well_founded_induction (well_founded_ltof str length).

  Lemma elem_of_re_star_pow s r :
    s ∈ re_star r ↔ ∃ n, s ∈ r ^ n.
  Proof.
    split.
    + induction s as [s IHs] using length_ind. unfold ltof in IHs.
      inv 1 as [|?|?|?|?|?|? s1 s2].
      { exists 0. constructor. }
      destruct (nil_or_length_pos s1) as [?|?]; [done|].
      edestruct (IHs s2) as [n ?]; [|done|].
      - rewrite length_app. lia.
      - exists (S n). simpl. by constructor.
    + intros [n Hs]. generalize dependent s. induction n as [|n']; inv 1; [constructor|].
      destruct s1; [|constructor]; auto.
  Qed.

  (** ** Property of [re_rev] *)

  Lemma elem_of_re_rev s r :
    s ∈ r →
    reverse s ∈ re_rev r.
  Proof.
    induction 1 as [|?|?|?|?|?|????? IHr1 ? IHr2]; simpl.
    - setoid_rewrite reverse_nil. constructor.
    - rewrite reverse_singleton. by constructor.
    - rewrite reverse_app. by constructor.
    - apply elem_of_union. by left.
    - apply elem_of_union. by right.
    - setoid_rewrite reverse_nil. constructor.
    - rewrite reverse_app. apply elem_of_re_star_pow.
      simpl in IHr2. apply elem_of_re_star_pow in IHr2 as [n ?].
      exists (n + 1). apply elem_of_re_pow_plus; [done|]. by rewrite re_pow_1.
  Qed.

  (** ** Properties of [d_char] and [d_str] *)

  Lemma elem_of_d_char s c r :
    s ∈ d_char c r ↔ c :: s ∈ r.
  Proof.
    split.
    + revert s. induction r => s; simpl; intros Hr.
      - set_solver.
      - set_solver. 
      - case_bool_decide; [|set_solver]. inv Hr. by constructor.
      - apply elem_of_union in Hr as [Hr|Hr].
        * inv Hr. rewrite app_comm_cons. constructor; [auto|done].
        * case_bool_decide; [|set_solver].
          rewrite <-(app_nil_l (c :: s)). constructor; [done|auto].
      - apply elem_of_union. set_solver.
      - inv Hr. rewrite app_comm_cons. constructor; [done|auto|done].
    + revert s. induction r => s.
      all: inversion 1 as [|?|?????? Heq|?|?|?|?????? Heq]; subst.
      - simpl. case_bool_decide; [constructor | congruence].
      - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; simpl; apply elem_of_union.
        * right. rewrite bool_decide_true; eauto.
        * left. constructor; eauto.
      - simpl. set_solver.
      - simpl. set_solver.
      - apply app_eq_cons in Heq as [[-> ->]|[? [-> ->]]]; [done|].
        simpl. constructor; eauto.
  Qed.

  Lemma elem_of_d_str t s r :
    s ∈ d_str t r ↔ t ++ s ∈ r.
  Proof.
    revert r. induction t => r; simpl. { done. } by rewrite <-elem_of_d_char.
  Qed.

End regex_ops_properties.
