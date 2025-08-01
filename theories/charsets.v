From stdpp Require Import listset.

Section set_ext.

  Context {A C : Type} `{FinSet A C}.
  Implicit Type (X : C) (x : A).

  Lemma empty_iff_elements X :
    X ≡ ∅ ↔ elements X = [].
  Proof.
    split.
    + intros HX. apply Permutation_nil.
      apply NoDup_Permutation; [apply NoDup_nil_2 | apply NoDup_elements |].
      intros y. rewrite elem_of_elements. set_solver.
    + intros HX y. rewrite <-elem_of_elements, HX. set_solver.
  Qed.

  Global Instance set_empty_dec X : Decision (X ≡ ∅).
  Proof.
    refine (cast_if (decide (elements X = []))); by rewrite empty_iff_elements.
  Qed.

  Lemma non_empty_elem_of X :
    X ≢ ∅ → ∃ x, x ∈ X.
  Proof.
    rewrite empty_iff_elements, <-head_is_Some.
    intros [x ?]. exists x. by apply elem_of_elements, head_Some_elem_of.
  Qed.

  Lemma singleton_iff_elements X x :
    X ≡ {[x]} ↔ elements X = [x].
  Proof.
    split.
    + intros HX. apply Permutation_length_1_inv.
      apply NoDup_Permutation; [apply NoDup_singleton | apply NoDup_elements |].
      intros y. rewrite elem_of_elements. set_solver.
    + intros HX y. rewrite <-elem_of_elements, HX. set_solver.
  Qed.

  Global Instance set_singleton_dec X x : Decision (X ≡ {[x]}).
  Proof.
    refine (cast_if (decide (elements X = [x]))); by rewrite singleton_iff_elements.
  Qed.

End set_ext.

(** We represent characters by their code points (encoded as [nat]). *)
Definition char : Type := nat.

(** We encode a character set as a [listset], which is an instance of [FinSet]. *)
Definition charset : Type := listset char.
