From stdpp Require Import list sets well_founded.
From flat Require Export strings intervals.

(** * Regular Languages *)

(** We consider a kind of _extended_ regular expressions (regexes), where the literals
    are charsets: the members of [re_lit L] are singleton strings [[σ]] for [σ ∈ L].
    The traditional character literal [σ] is here encoded as [re_lit {[σ]}],
    where the charset is a singleton containing [σ]. *)
Inductive regex : Type :=
  | re_none : regex                   (* ∅ *)
  | re_null : regex                   (* ε *)
  | re_lit : charset → regex          (* literal *)
  | re_concat : regex → regex → regex (* concatenation: [r1 ⧺ r2] *)
  | re_union : regex → regex → regex  (* union: [r1 ∪ r2] *)
  | re_star : regex → regex           (* Kleene star *)
  .
Global Instance regex_empty : Empty regex := re_none.
Global Instance regex_union : Union regex := re_union.
Infix "⧺" := re_concat (right associativity, at level 60).

(** The usual notion "a string [s] is in the language of [r]" is here inductively defined
    as a relation "[s ∈ r]". *)
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

(** We write [r1 ≡ r2] for the semantic equivalence between [r1] and [r2], 
    i.e., their languages are equivalent, or, [∀ s, s ∈ r1 ↔ s ∈ r2]. *)
(* Check equiv. *)

Lemma elem_of_re_concat_lit σ L s r :
  σ ∈ L →
  s ∈ r →
  σ :: s ∈ re_lit L ⧺ r.
Proof.
  intros. replace (σ :: s) with ([σ] ++ s) by done.
  constructor; [by constructor | done].
Qed.

(** A singleton regex, which represents a singleton language, is constructed from a given string. *)
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

(** The class of regexes forms an axiomatized set that supports union. *)
Global Instance regex_semi_set : SemiSet str regex.
Proof.
  split.
  + inv 1.
  + intros. apply elem_of_str_to_regex.
  + intros. split. { inv 1; auto. }
    intros [?|?]; [by apply elem_of_re_union_l | by apply elem_of_re_union_r].
Qed.

(** ** Extensions *)

(** Kleene plus: repeating at least once. *)
Definition re_plus (r : regex) : regex := r ⧺ re_star r.

(** Optional: repeating at most once. *)
Definition re_opt (r : regex) : regex := r ∪ re_null.

(** Repeating [r] exactly [n] times is encoded as [r ^ n]. Specially, [r ^ 0 = ε]. *)
Fixpoint re_pow (r : regex) (n : nat) : regex :=
  match n with
  | 0 => re_null
  | S n' => r ⧺ re_pow r n'
  end.
Infix "^" := re_pow.

(** Repeating [r] at least [m] and at most [n] times is encoded as [re_loop (m `to` n) r].
    If the upper bound is [∞], [r] is allowed to repeat infinitely ([re_star r]). *)
Definition re_loop (I : interval) (r : regex) : regex :=
  match I with
  | m `to` fin n => r ^ m ⧺ ⋃ ((λ k, r ^ k) <$> seq 0 (n - m + 1))
  | m `to` inf => r ^ m ⧺ re_star r
  end.

(** ** Basic Operations *)

(** Nullability: test if the empty string is a member of [r], i.e., [[] ∈ r]. *)
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

(** Emptiness: test if [r] is semantically equivalent to the empty language, i.e., [r ≡ ∅]. *)
Fixpoint re_empty (r : regex) : bool :=
  match r with
  | re_none => true
  | re_null => false
  | re_lit L => bool_decide (L ≡ ∅)
  | re_concat r1 r2 => re_empty r1 || re_empty r2
  | re_union r1 r2 => re_empty r1 && re_empty r2
  | re_star _ => false
  end.

(** Reverse language. *)
Fixpoint re_rev (r : regex) : regex :=
  match r with
  | re_concat r1 r2 => re_rev r2 ⧺ re_rev r1
  | re_union r1 r2 => re_rev r1 ∪ re_rev r2
  | re_star r => re_star (re_rev r)
  | _ => r
  end.

(** Brzozowski derivatives w.r.t. characters. *)
Fixpoint d_char (σ : char) (r : regex) : regex :=
  match r with
  | re_none => ∅
  | re_null => ∅
  | re_lit L => if bool_decide (σ ∈ L) then re_null else ∅
  | re_concat r1 r2 => (d_char σ r1 ⧺ r2) ∪ (if bool_decide ([] ∈ r1) then d_char σ r2 else ∅)
  | re_union r1 r2 => d_char σ r1 ∪ d_char σ r2
  | re_star r => d_char σ r ⧺ re_star r
  end.

(** Brzozowski derivatives w.r.t. strings. *)
Fixpoint d_str (t : str) (r : regex) : regex :=
  match t with
  | [] => r
  | σ :: t' => d_str t' (d_char σ r)
  end.

(** * Properties *)

Section regex_ops_properties.

  Implicit Type (s : str) (σ : char) (L : charset) (r : regex) (m n : nat).
  
  (** ** Emptiness *)

  Lemma empty_re_concat r1 r2 :
    r1 ≡ ∅ ∨ r2 ≡ ∅ → r1 ⧺ r2 ≡ ∅.
  Proof.
    intros [?|?]; rewrite elem_of_equiv_empty => s Hs; inv Hs; set_solver.
  Qed.

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

  (** Correctness of the decision procedure [re_empty]. *)
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

  (** ** Properties of [re_concat] *)

  Lemma re_concat_assoc r1 r2 r3 :
    r1 ⧺ r2 ⧺ r3 ≡ (r1 ⧺ r2) ⧺ r3.
  Proof.
    intros s. split.
    + inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. inv Hs2.
      rewrite app_assoc. constructor; [|done]. by constructor.
    + inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. inv Hs1.
      rewrite <-app_assoc. constructor; [done|]. by constructor.
  Qed.

  Lemma re_concat_null_l r :
    re_null ⧺ r ≡ r.
  Proof.
    intros s. split.
    + inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. inv Hs1. by rewrite app_nil_l.
    + intros. rewrite <-app_nil_l at 1. constructor; [constructor|done].
  Qed.

  Lemma re_concat_null_r r :
    r ⧺ re_null ≡ r.
  Proof.
    intros s. split.
    + inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. inv Hs2. by rewrite app_nil_r.
    + intros. rewrite <-app_nil_r at 1. constructor; [done|constructor].
  Qed.

  (** This instance allows us to rewrite, say [r ⧺ r1] into [r ⧺ r2]
      using a hypothesis [H : r1 ≡ r2]. *)
  Global Instance re_concat_proper : Proper (equiv ==> equiv ==> equiv) re_concat.
  Proof.
    intros r1 r2 ? r3 r4 ? s. split; inv 1; constructor; set_solver.
  Qed.

  (** ** Properties of [re_pow] and [re_loop] *)

  Lemma re_pow_1 r :
    r ^ 1 ≡ r.
  Proof.
    simpl. by rewrite re_concat_null_r.
  Qed.

  Lemma re_pow_plus r m n :
    r ^ (m + n) ≡ r ^ m ⧺ r ^ n.
  Proof.
    induction m as [|m' IHm']; simpl.
    - by rewrite re_concat_null_l.
    - by rewrite IHm', re_concat_assoc.
  Qed.

  Lemma re_pow_subseteq_star r n :
    r ^ n ⊆ re_star r.
  Proof.
    induction n; simpl.
    - intros s. inv 1. constructor.
    - intros s. inv 1 as [|?|?? s1 s2 Hs1 Hs2|?|?|?|?]. destruct s1.
      * rewrite app_nil_l. set_solver.
      * constructor; [done..|set_solver].
  Qed.

  Local Definition length_ind :=
    well_founded_induction (well_founded_ltof str length).

  (** This lemma provides a view that the [re_star r] is regarded as repeating [r] 
      an arbitrary number of times [n] for some [0 ≤ n]. *)
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
    + intros [n Hs]. apply (elem_of_weaken _ _ _ Hs). apply re_pow_subseteq_star.
  Qed.

  Lemma re_pow_subseteq_loop n I r :
    n ∈ I →
    r ^ n ⊆ re_loop I r.
  Proof.
    intros Hn s Hs. destruct I as [a [b|]]; simpl.
    all: cbv in Hn; replace n with (a + (n - a)) in Hs by lia; rewrite re_pow_plus in Hs.
    all: inv Hs; constructor; [done|].
    - apply elem_of_union_list. eexists. split; [|done]. apply elem_of_list_fmap.
      eexists. split; [done|]. apply elem_of_seq. lia.
    - apply elem_of_re_star_pow. eauto.
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
    - simpl in IHr2. apply elem_of_re_star_pow in IHr2 as [n ?].
      rewrite reverse_app. apply elem_of_re_star_pow.
      exists (n + 1). rewrite re_pow_plus, re_pow_1. by constructor.
  Qed.

  (** ** Properties of [d_char] and [d_str] *)

  Lemma elem_of_d_char s σ r :
    s ∈ d_char σ r ↔ σ :: s ∈ r.
  Proof.
    split.
    + revert s. induction r => s; simpl; intros Hr.
      - set_solver.
      - set_solver. 
      - case_bool_decide; [|set_solver]. inv Hr. by constructor.
      - apply elem_of_union in Hr as [Hr|Hr].
        * inv Hr. rewrite app_comm_cons. constructor; [auto|done].
        * case_bool_decide; [|set_solver].
          rewrite <-app_nil_l at 1. constructor; [done|auto].
      - apply elem_of_union. set_solver.
      - inv Hr. rewrite app_comm_cons. constructor; [done|auto|done].
    + revert s. induction r => s.
      all: inv 1 as [|?|?????? Heq|?|?|?|?????? Heq].
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
