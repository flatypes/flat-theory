From stdpp Require Import list.
From flat Require Import regexes.

Lemma cons_app {A: Type} (x : A) (l : list A) :
  x :: l = [x] ++ l.
Proof. naive_solver. Qed.

Lemma head_drop {A: Type} (l : list A) n :
  head (drop n l) = l !! n.
Proof.
  revert n. induction l => n.
  - by rewrite drop_nil.
  - destruct n; [done| by rewrite skipn_cons, lookup_cons].
Qed.

Lemma tail_app {A: Type} (l1 l2 : list A) :
  tail (l1 ++ l2) = if bool_decide (l1 = []) then tail l2 else tail l1 ++ l2.
Proof. by destruct l1. Qed.

Fixpoint big_union {C : Type} `{Empty C, Union C} (Xs : list C) : C :=
  match Xs with
  | [] => ∅
  | X :: Xs => X ∪ big_union Xs
  end.

Lemma elem_of_big_union {A C} `{SemiSet A C} (X : C) (Xs : list C) (x : A) :
  X ∈ Xs →
  x ∈ X →
  x ∈ big_union Xs.
Proof.
  induction Xs.
  - inversion 1.
  - intros HX ?. simpl. apply elem_of_union. apply elem_of_cons in HX as [?|?].
    * left. congruence.
    * right. auto.
Qed.
