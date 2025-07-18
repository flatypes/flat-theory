From stdpp Require Import list list_numbers.
From flat Require Export charsets.

(** * Strings & String Operations *)

(** A string is a list of characters. *)
Definition str : Type := list char.

Definition char_to_str (σ : char) : str := [σ].
Coercion char_to_str : char >-> str.

(** The following basic string operations are simply list operations:
  - concat: [app] (notation [_ ++ _])
  - reverse: [reverse]
  - length: [length]
 *)

Coercion Z.of_nat : nat >-> Z.
Local Open Scope Z_scope.

(** Auxiliary definitions for string take and drop, by list [take] and [drop]. *)
Definition str_take (s : str) (n : Z) : str := take (Z.to_nat n) s.
Definition str_drop (s : str) (n : Z) : str :=
  if bool_decide (0 ≤ n) then drop (Z.to_nat n) s else [].

(** The substring operation is also defined in terms of [str_take] and [str_drop]. *)
Definition substr (s : str) (i j : Z) : str := str_take (str_drop s i) (j - i).
Notation "s [ i : j ]" := (substr s i j) (at level 2, i at level 50, j at level 50,
  left associativity, format "s [ i : j ]").

(** Relationship between take and drop with substr. *)
Lemma str_take_substr s n :
  str_take s n = s[0:n].
Proof.
  unfold substr, str_take, str_drop.
  rewrite bool_decide_true, drop_0 by lia. f_equal. lia.
Qed.

Lemma str_drop_substr s n :
  str_drop s n = s[n : length s].
Proof.
  unfold substr, str_take, str_drop. case_bool_decide.
  - rewrite take_ge; [done|]. rewrite length_drop. lia.
  - by rewrite take_nil.
Qed.

Notation "s [ : n ]" := (str_take s n) (at level 2, n at level 50, left associativity,
  format "s [ : n ]").
Notation "s [ n : ]" := (str_drop s n) (at level 2, n at level 50, left associativity,
  format "s [ n : ]").

(** The char-at operation is defined in terms of [str_take] and [str_drop]. *)
Definition char_at (s : str) (i : Z) : str := str_take (str_drop s i) 1.
Notation "s [ i ]" := (char_at s i) (at level 2, i at level 50, no associativity, format "s [ i ]").

(** The prefix and suffix operations are defined by list relations 
    [`prefix_of`] and [`suffix_of`]. *)
Definition str_prefix (t s : str) : bool := bool_decide (t `prefix_of` s).
Definition str_suffix (t s : str) : bool := bool_decide (t `suffix_of` s).
Infix "⊑" := str_prefix (at level 70, no associativity).
Infix "⊒" := str_suffix (at level 70, no associativity).

(** The find operation is defined by [list_find]. *)
Definition find (s t : str) : Z :=
  match list_find (λ k : nat, t `prefix_of` s[k:]) (seq 0 (length s)) with
  | Some (k, _) => k
  | None => -1
  end.

(** The infix operation (a.k.a. contains) is defined in terms of [find]. *)
Definition str_infix (t s : str) : bool := bool_decide (0 ≤ find s t).
Infix "`in`" := str_infix (at level 70, no associativity).

(** Auto unfold *)

Local Lemma unfold_str_drop s n :
  0 ≤ n →
  str_drop s n = drop (Z.to_nat n) s.
Proof.
  intros. unfold str_drop. by rewrite bool_decide_true by lia.
Qed.

Local Lemma Z_to_nat_1 :
  Z.to_nat 1 = 1%nat.
Proof. lia. Qed.

Ltac unfold_substr :=
  unfold substr, char_at, str_take in *;
  rewrite ?unfold_str_drop in * by lia;
  rewrite ?Nat2Z.id, ?Z_to_nat_1 in *.

Lemma nat_sub_le n m :
  (n ≤ m)%nat → (n - m = 0)%nat.
Proof. lia. Qed.

Lemma Z_to_nat_sub_le n m :
  n ≤ m → Z.to_nat (n - m) = 0%nat.
Proof. lia. Qed.

Section str_ops_properties.

  Implicit Type (s t : str) (σ : char).

  Lemma str_take_app_l i s1 s2 :
    i ≤ length s1 →
    (s1 ++ s2)[:i] = s1[:i].
  Proof.
    intros. unfold_substr. rewrite take_app, nat_sub_le by lia.
    by rewrite take_0, app_nil_r.
  Qed.

  Lemma str_take_app_r i s1 s2 :
    length s1 ≤ i →
    (s1 ++ s2)[:i] = s1 ++ s2[:i - length s1].
  Proof.
    intros. unfold_substr. rewrite take_app, take_ge by lia.
    do 2 f_equal. lia.
  Qed.

  Lemma str_drop_app_l i s1 s2 :
    0 ≤ i < length s1 →
    (s1 ++ s2)[i:] = s1[i:] ++ s2.
  Proof.
    intros. unfold_substr. rewrite drop_app. f_equal. rewrite nat_sub_le by lia. apply drop_0.
  Qed.

  Lemma str_drop_app_r i s1 s2 :
    length s1 ≤ i →
    (s1 ++ s2)[i:] = s2[i - length s1:].
  Proof.
    intros. unfold_substr. rewrite drop_app, drop_ge, app_nil_l by lia.
    f_equal. lia.
  Qed.

  Lemma substr_alt s i j :
    s[i:j] = s[:j][i:].
  Proof.
    intros. unfold_substr. unfold str_drop. case_bool_decide; [|by rewrite take_nil].
    rewrite take_drop_commute. destruct (Z.le_gt_cases i j) as [?|?].
    - do 2 f_equal. lia.
    - rewrite Z_to_nat_sub_le, Nat.add_0_r by lia.
      rewrite skipn_firstn_comm, Nat.sub_diag, take_0.
      symmetry. apply nil_length_inv. rewrite length_drop, length_take. lia.
  Qed.

  (** Properties of the [char_at] operation *)

  Lemma take_1_eq_singleton {A : Type} (l : list A) x :
    take 1 l = [x] ↔ l !! 0%nat = Some x.
  Proof.
    split.
    + intros Heq. apply (f_equal (λ l, l !! 0%nat)) in Heq.
      by rewrite lookup_take in Heq by lia.
    + intros. apply list_eq. destruct i. { by rewrite lookup_take by lia. }
      simpl. rewrite lookup_nil. apply lookup_ge_None. rewrite length_take. lia.
  Qed.

  (** [s[i] = σ] iff [i] is a valid index of [s] and [σ] is the character at [i]. *)
  Lemma char_at_iff i s σ :
    s[i] = σ ↔ 0 ≤ i ∧ s !! (Z.to_nat i) = Some σ.
  Proof.
    unfold_substr. setoid_rewrite take_1_eq_singleton.
    unfold str_drop. case_bool_decide.
    - rewrite lookup_drop. split.
      + intros <-. split; [|f_equal]; lia.
      + intros [_ <-]. f_equal. lia.
    - split; [done|naive_solver].
  Qed.

  Lemma lookup_Some_char_at i s σ :
    0 ≤ i →
    s !! (Z.to_nat i) = Some σ →
    s[i] = σ.
  Proof.
    intros. by apply char_at_iff.
  Qed.

  Lemma char_at_inv_singleton c i σ :
    [c][i] = σ →
    i = 0 ∧ c = σ.
  Proof.
    intros Hi. apply char_at_iff in Hi as [? Hi].
    apply list_lookup_singleton_Some in Hi as [??]. split; [lia|done].
  Qed.

  Lemma char_at_inv_app i s1 s2 σ :
    (s1 ++ s2)[i] = σ →
    (0 ≤ i < length s1 ∧ s1[i] = σ) ∨ (length s1 ≤ i ∧ s2[i - length s1] = σ).
  Proof.
    intros Hi. apply char_at_iff in Hi as [? Hi].
    apply lookup_app_Some in Hi as [Hi|[? Hi]].
    - left. split. { apply lookup_lt_Some in Hi. lia. }
      by apply char_at_iff.
    - right. split; [lia|].
      apply char_at_iff. split; [lia|]. rewrite <-Hi. f_equal. lia.
  Qed.

  (** Properties of the [find] operation *)

  Local Ltac destruct_find k Heq :=
    unfold find;
    match goal with
    | |- context [ match list_find ?f ?l with _ => _ end ] =>
      destruct (list_find f l) as [[k ?]|] eqn:Heq
    end.

  (** [find s t] returns either [-1] or an index of [s]. *)
  Lemma find_range s t :
    -1 ≤ find s t < length s.
  Proof.
    destruct_find k Heq; [|lia].
    apply list_find_Some in Heq as [Hk _]. apply lookup_seq in Hk. lia.
  Qed.

  (** [find s t] evaluates to an index [i] of [s] iff
      [i] is the index of the _first_ occurrence of [t] in [s]. *)
  Lemma found_iff i s t :
    0 ≤ i < length s →
    find s t = i ↔ t `prefix_of` s[i:] ∧ ∀ k, 0 ≤ k < i → ¬ (t `prefix_of` s[k:]).
  Proof.
    intros. destruct_find k Heq.
    - apply list_find_Some in Heq as [Hk [Htk Hlt_k]].
      apply lookup_seq in Hk as [??]. simplify_eq/=. split.
      + intros <-. split; [done|].
        intros j ?. specialize (Hlt_k (Z.to_nat j) (Z.to_nat j)).
        rewrite Z2Nat.id in Hlt_k by lia. apply Hlt_k; [|lia]. apply lookup_seq. lia.
      + intros [Hti Hlt_i]. destruct (Z.lt_total k i) as [?|[?|?]]; [|done|].
        * apply Hlt_i in Htk; [done|lia].
        * specialize (Hlt_k (Z.to_nat i) (Z.to_nat i)). rewrite Z2Nat.id in Hlt_k by lia.
          apply Hlt_k in Hti; [done| |lia]. apply lookup_seq. lia.
    - split; [lia|]. intros [Ht _].
      rewrite list_find_None, Forall_forall in Heq.
      specialize (Heq (Z.to_nat i)). rewrite Z2Nat.id in Heq by lia.
      apply Heq in Ht; [done|]. apply elem_of_seq. lia.
  Qed.

  Lemma found_occur i s t :
    0 ≤ i →
    find s t = i →
    t `prefix_of` s[i:].
  Proof.
    intros. pose (find_range s t). apply found_iff; [lia|done].
  Qed.

  Lemma found_not_occur i s t k :
    0 ≤ i →
    find s t = i →
    0 ≤ k < i →
    ¬ (t `prefix_of` s[k:]).
  Proof.
    intros. pose (find_range s t). eapply found_iff; [|done|]; lia.
  Qed.
  
  (** [find s t] is nonnegative iff [t] occurs in [s]. *)
  Lemma find_nonneg_iff s t :
    0 ≤ find s t ↔ (∃ i, 0 ≤ i < length s ∧ t `prefix_of` s[i:]).
  Proof.
    split.
    + intros. exists (find s t). pose (find_range s t).
      split; [lia | by apply found_occur].
    + intros [i [? Ht]]. destruct_find k Heq.
      - apply list_find_Some in Heq as [Hk _]. apply lookup_seq in Hk. lia.
      - rewrite list_find_None, Forall_forall in Heq.
        specialize (Heq (Z.to_nat i)). rewrite Z2Nat.id in Heq by lia.
        apply Heq in Ht; [done|]. apply elem_of_seq. lia.
  Qed.

  Lemma found_char i s σ :
    0 ≤ i →
    find s σ = i →
    s[i] = σ ∧ σ ∉ s[:i].
  Proof.
    intros ? Hf. split.
    + apply found_occur in Hf; [|lia]. destruct Hf as [? Hs].
      unfold_substr. by rewrite Hs.
    + intros Hin. unfold_substr. apply elem_of_take in Hin as [k [Hk ?]].
      apply (found_not_occur _ _ _ k) in Hf; [|lia..]. apply Hf.
      unfold_substr. apply drop_S in Hk. rewrite Hk. by eexists.
  Qed.

  Lemma found_empty s :
    find s ([]) = if bool_decide (s = []) then -1 else 0.
  Proof.
    case_bool_decide; [by simplify_eq|]. apply found_iff; [|split].
    + split; [done|]. destruct s; naive_solver.
    + apply prefix_nil.
    + lia.
  Qed.

End str_ops_properties.