From stdpp Require Import base.
From flat Require Import regexes.

Fixpoint alphabet (r : regex) : charset :=
  match r with
  | re_none => ∅
  | re_null => ∅
  | re_lit C => C
  | re_concat r1 r2 => (alphabet r1) ∪ (alphabet r2)
  | re_union r1 r2 => (alphabet r1) ∪ (alphabet r2)
  | re_star r => alphabet r
  end.
