From stdpp Require Import list list_numbers.
From flat Require Export charsets.

(** We represent strings as character lists. *)
Definition str : Type := list char.

Definition char_to_str (σ : char) : str := [σ].
Coercion char_to_str : char >-> str.

(** We reuse standard list operations for string concatenation, reverse, and length: *)
(* Check app.     *)
(* Check reverse. *)
(* Check length.  *)

(** We define prefix and suffix tests via list [prefix] and [suffix]: *)
Definition str_prefix (t s : str) : bool := bool_decide (t `prefix_of` s).
Definition str_suffix (t s : str) : bool := bool_decide (t `suffix_of` s).
Infix "⊑" := str_prefix (at level 70, no associativity).
Infix "⊒" := str_suffix (at level 70, no associativity).

(** * Char-At *)

(** We define the char-at operation via list [take] and [drop]: *)
Definition char_at (s : str) (i : nat) : str := take 1 (drop i s).
Notation "s [ i ]" := (char_at s i)
  (at level 2, i at level 50, no associativity, format "s [ i ]").

Implicit Type (s t : str) (i j k : nat) (σ : char).

Lemma take_1_eq_singleton s σ :
  take 1 s = [σ] ↔ s !! 0 = Some σ.
Proof.
  split.
  + intros Heq. apply (f_equal (λ s, s !! 0)) in Heq. simpl in Heq.
    rewrite <-Heq. setoid_rewrite lookup_take; [done|lia].
  + intros. apply list_eq. destruct i. { by rewrite lookup_take by lia. }
    simpl. rewrite lookup_nil. apply lookup_ge_None. rewrite length_take. lia.
Qed.

(** This operation [s[i]] returns a _singleton_ string containing the character [σ] at index [i] 
    of [s], i.e., [s !! i = Some σ]: *)
Lemma char_at_lookup s i σ :
  s[i] = σ ↔ s !! i = Some σ.
Proof.
  unfold char_at. setoid_rewrite take_1_eq_singleton.
  setoid_rewrite lookup_drop. by rewrite Nat.add_0_r.
Qed.
(** Thus we see the definition of [s[i]] is _consistent_ with the usual semantics of char-at. *)

Lemma char_at_inv_app i s1 s2 σ :
  (s1 ++ s2)[i] = σ →
  (i < length s1 ∧ s1[i] = σ) ∨ (length s1 ≤ i ∧ s2[i - length s1] = σ).
Proof.
  rewrite ->char_at_lookup, lookup_app_Some. intros [Hi|Hi].
  - left. split. { by apply lookup_lt_Some in Hi. } by apply char_at_lookup.
  - right. by rewrite char_at_lookup.
Qed.

(** * Substring *)

(** We define the substring operation via list [take] and [drop]: *)
Definition substr (s : str) (i j : nat) : str := take (j - i) (drop i s).
Notation "s [ i : j ]" := (substr s i j)
  (at level 2, i at level 50, j at level 50, left associativity, format "s [ i : j ]").

(** This operation [s[i:j]] returns the substring of [s] starting from [i] and ending until [j]: *)
Lemma substr_lookup s i j k :
  k < length s[i:j] →
  s[i:j] !! k = s !! (i + k).
Proof.
  unfold substr. rewrite length_take, length_drop. intros.
  setoid_rewrite lookup_take; [|lia]. apply lookup_drop.
Qed.
(** Thus we see the definition of [s[i:j]] is _consistent_ with the usual semantics of
    substring. *)

(** The substring until [j], i.e., [s[0:j]], is just [take j s]: *)
Lemma substr_until_take s j :
  s[0:j] = take j s.
Proof.
  unfold substr. rewrite drop_0. f_equal. lia.
Qed.
(** Thus we define [s[:j] = s[0:j]] by [take j s]: *)
Notation "s [ : j ]" := (take j s)
  (at level 2, j at level 50, left associativity, format "s [ : j ]").

(** The substring from [i], i.e., [s[i : length s]], is just [drop i s]: *)
Lemma substr_from_drop s i :
  s[i : length s] = drop i s.
Proof.
  unfold substr. rewrite take_ge; [done|]. rewrite length_drop. lia.
Qed.
(** Thus we define [s[i:] = s[i : length s]] by [drop i s]. *)
Notation "s [ i : ]" := (drop i s)
  (at level 2, i at level 50, left associativity, format "s [ i : ]").

Lemma nat_le_sub n m :
  n ≤ m → n - m = 0.
Proof. lia. Qed.

(** Alternatively, we can define [s[i:j]] by first [take] and then [drop]: *)
Lemma substr_alt s i j :
  s[i:j] = s[:j][i:].
Proof.
  unfold substr. destruct (Nat.lt_ge_cases i j) as [?|?].
  - rewrite take_drop_commute. do 2 f_equal. lia.
  - rewrite nat_le_sub, take_0 by lia.
    symmetry. apply nil_length_inv. rewrite length_drop, length_take. lia.
Qed.

Lemma take_app_l i s1 s2 :
  i ≤ length s1 →
  (s1 ++ s2)[:i] = s1[:i].
Proof.
  intros. by rewrite take_app, nat_le_sub, take_0, app_nil_r by lia.
Qed.

Lemma take_app_r i s1 s2 :
  length s1 ≤ i →
  (s1 ++ s2)[:i] = s1 ++ s2[:i - length s1].
Proof.
  intros. by rewrite take_app, take_ge by lia.
Qed.

Lemma drop_app_l i s1 s2 :
  0 ≤ i < length s1 →
  (s1 ++ s2)[i:] = s1[i:] ++ s2.
Proof.
  intros. by rewrite drop_app, nat_le_sub, drop_0 by lia.
Qed.

Lemma drop_app_r i s1 s2 :
  length s1 ≤ i →
  (s1 ++ s2)[i:] = s2[i - length s1:].
Proof.
  intros. by rewrite drop_app, drop_ge, app_nil_l by lia.
Qed.

(** * Find *)

(** We define the find operation via [list_find]: *)
Definition find (s t : str) : option nat :=
  if bool_decide (t = []) then Some 0
  else (λ '(k, _), k) <$> list_find (λ k, t `prefix_of` s[k:]) (seq 0 (length s)).

Lemma find_Some_le s t i :
  find s t = Some i →
  i + length t ≤ length s.
Proof.
  unfold find. case_bool_decide. { inv 1. simpl. lia. }
  rewrite fmap_Some. intros [[k ?] [Heq ->]].
  apply list_find_Some in Heq as [Hk [Hp ?]]. apply lookup_seq in Hk as [-> ?].
  simpl in Hp. destruct Hp as [s2 Hs2].
  rewrite <-(take_drop k s), length_app, Hs2, length_app, length_take. lia.
Qed.

(** On the one hand, if this operation [find s t] returns _some_ index [i],
    then [t] occurs in [s] at [i]: *)
Lemma find_Some_occur s t i :
  find s t = Some i →
  t `prefix_of` s[i:].
Proof.
  unfold find. case_bool_decide. { inv 1. apply prefix_nil. }
  rewrite fmap_Some. intros [[??] [Heq <-]].
  apply list_find_Some in Heq as [Hi [??]]. by apply lookup_seq in Hi as [-> ?].
Qed.

(** Moreover, [i] is the _first_ occurrence of [t] in [s], that is, for any [k < i],
    [t] cannot be a prefix of [s[k:]]: *)
Lemma find_Some_not_occur s t i k :
  find s t = Some i →
  k < i →
  ¬ (t `prefix_of` s[k:]).
Proof.
  unfold find. case_bool_decide. { inv 1. lia. }
  rewrite fmap_Some. intros [[??] [Heq <-]] ?.
  apply list_find_Some in Heq as [Hi [? Hlt]]. apply lookup_seq in Hi as [-> ?].
  apply (Hlt k); [|lia]. apply lookup_seq. lia.
Qed.

Lemma length_nonempty_str s :
  s ≠ [] →
  0 < length s.
Proof.
  destruct s; simpl; [done|lia].
Qed.

(** On the other hand, if [i] is the first occurrence of [t] in [s], then [find s t = Some i]: *)
Lemma find_eq_Some i s t :
  i + length t ≤ length s →
  t `prefix_of` s[i:] →
  (∀ k, k < i → ¬ (t `prefix_of` s[k:])) →
  find s t = Some i.
Proof.
  intros ?? Hlt. unfold find. case_bool_decide as Ht.
  { f_equal. simplify_eq/=. destruct (Nat.eq_0_gt_0_cases i); [lia|].
    pose (@prefix_nil char). naive_solver. }
  rewrite fmap_Some. exists (i, i). split; [|done].
  apply list_find_Some. repeat split; [|done|].
  + apply lookup_seq. apply length_nonempty_str in Ht. lia.
  + intros j ? Hj ?. apply Hlt. apply lookup_seq in Hj. lia.
Qed.
(** Putting the above together, we see the definition of [find s t] is _consistent_ with the
    usual semantics of the find operation. *)

Lemma find_is_Some i s t :
  i + length t ≤ length s →
  t `prefix_of` s[i:] →
  is_Some (find s t).
Proof.
  intros. apply not_eq_None_Some. unfold find. case_bool_decide as Ht; [done|].
  intros Heq. rewrite fmap_None, list_find_None, Forall_forall in Heq.
  apply (Heq i); [|done]. apply elem_of_seq.
  apply length_nonempty_str in Ht. lia.
Qed.

Lemma find_char_Some s σ i :
  find s σ = Some i →
  s[i] = σ ∧ σ ∉ s[:i].
Proof.
  intros Hf. split.
  + apply find_Some_occur in Hf as [? Hs]. unfold char_at. by rewrite Hs.
  + intros Hin. apply elem_of_take in Hin as [k [Hk ?]]. apply drop_S in Hk.
    eapply find_Some_not_occur; [done..|]. rewrite Hk. by eexists. 
Qed.

(** Finding the empty pattern always succeeds with the index [0]: *)
Lemma find_empty s :
  find s ([]) = Some 0.
Proof.
  apply find_eq_Some; simpl; [lia | apply prefix_nil | lia].
Qed.

(** * Infix *)

(** We define the infix test (a.k.a. contains) via [find]: *)
Definition str_infix (t s : str) : bool := bool_decide (is_Some (find s t)).
Infix "`in`" := str_infix (at level 70, no associativity).

(** This operation [t `in` s] returns [true] iff [t] is an infix of [s], i.e.,
    [s = s1 ++ t ++ s2] for some [s1] and [s2]: *)
Lemma str_infix_infix t s :
  t `in` s ↔ ∃ s1 s2, s = s1 ++ t ++ s2.
Proof.
  setoid_rewrite bool_decide_spec. split.
  + intros [i Hi]. apply find_Some_occur in Hi as [s2 Hs2].
    exists s[:i], s2. by rewrite <-Hs2, take_drop.
  + intros [s1 [s2 ->]]. apply (find_is_Some (length s1)).
    { rewrite !length_app. lia. }
    exists s2. by rewrite drop_app, drop_ge, nat_le_sub, drop_0 by lia.
Qed.
(** Thus we see the definition of [t `in` s] is _consistent_ with the usual semantics of
    infix. *)