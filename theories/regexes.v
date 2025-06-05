From Coq Require Import ssreflect.
From stdpp Require Import list.

Definition char : Type := nat.

Definition charset : Type := char → Prop.

Instance empty_charset : Empty charset := λ _, False.

Instance elem_of_charset : ElemOf char charset := λ c C, C c.

Instance union_charset : Union charset := λ C1 C2 c, C1 c ∨ C2 c.

(** * Strings *)

Definition str : Type := list char.

(** * Regular expressions and languages. *)

Inductive regex : Type :=
  | re_none : regex
  | re_null : regex
  | re_lit : charset → regex
  | re_concat : regex → regex → regex
  | re_union : regex → regex → regex
  | re_star : regex → regex
  .

Inductive elem_of_regex : ElemOf str regex :=
  | elem_of_null :
    [] ∈ re_null
  | elem_of_lit C c :
    c ∈ C → [c] ∈ re_lit C
  | elem_of_concat r1 r2 s1 s2 :
    s1 ∈ r1 → s2 ∈ r2 → s1 ++ s2 ∈ re_concat r1 r2
  | elem_of_union_l r1 r2 s:
    s ∈ r1 → s ∈ re_union r1 r2
  | elem_of_union_r r1 r2 s :
    s ∈ r2 → s ∈ re_union r1 r2
  | elem_of_star_zero r :
    [] ∈ re_star r
  | elem_of_star_many r s1 s2 :
    s1 ∈ r → s2 ∈ re_star r → s1 ++ s2 ∈ re_star r
  .
Existing Instance elem_of_regex.

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
  nullable r = true ↔ [] ∈ r.
Proof.
  split.
  + (* -> *)
    induction r => //= Hr.
    - constructor.
    - rewrite andb_true_iff in Hr.
      destruct Hr as [??].
      have -> : [] = [] ++ [] by done.
      constructor; auto.
    - rewrite orb_true_iff in Hr. 
      destruct Hr as [?|?]; [apply elem_of_union_l | apply elem_of_union_r]; auto.
    - constructor.
  + (* <- *)
    induction r => //= Hr.
    all: inversion Hr; subst => //=.
    - rewrite andb_true_iff.
      apply app_eq_nil in H as [??]. naive_solver.
    - rewrite orb_true_iff. left. naive_solver.
    - rewrite orb_true_iff. right. naive_solver.
Qed.
