From Coq Require Import ZArith.
From sys_verif Require Import options.

Record interval :=
  mkInterval { low: Z; high: Z }.

(*| Making this definition an `Instance` of `ElemOf` allows us to extend the `∈`
notation to have a meaning for our intervals, "overloading" its more common
meaning as element-of for sets. *)
Instance in_interval : ElemOf Z interval :=
  (* this gets printed as [low i ≤ x ≤ high i], which is just a notation *)
  λ x i, low i <= x ∧ x <= high i.

(* Here's an example of what it looks like to use `in_interval` in a theorem.
Notice that we unfold `elem_of`, which is what the `∈` notation is defined as,
and then we can unfold `in_interval`.

This unfolding is required for `lia` to work, since otherwise it doesn't
understand that `x ∈ i` is a useful arithmetic fact.
*)
Lemma in_interval_fact x (i: interval) :
  x ∈ i → low i <= x.
Proof.
  rewrite /elem_of. (* {GOAL} *)
  rewrite /in_interval.
  lia.
Qed.

Definition union (i1 i2: interval): interval :=
  {| low := Z.min (low i1) (low i2);
     high := Z.max (high i1) (high i2);
  |}.

Definition intersect (i1 i2: interval): interval :=
  {| low := Z.max (low i1) (low i2);
     high := Z.min (high i1) (high i2);
  |}.

Lemma union_spec x i1 i2 :
  x ∈ i1 ∨ x ∈ i2 → x ∈ union i1 i2.
Proof.
  rewrite /union /elem_of /in_interval /=.
  intros Hin.
  destruct Hin as [Hin1 | Hin2].
  - lia.
  - lia.
Qed.

Lemma intersect_spec x i1 i2 :
  x ∈ intersect i1 i2 → x ∈ i1 ∧ x ∈ i2.
Proof.
  rewrite /intersect /elem_of /in_interval /=.
  intros Hin.
  split.
  - lia.
  - lia.
Qed.

Definition is_empty (i: interval): Prop :=
  i.(low) > i.(high).

(* [x ∉ i] is just notation for [~ (x ∈ i)] (and this is notation for [x ∉ i →
False]) *)
Lemma is_empty_spec i :
  is_empty i ↔ (∀ x, x ∉ i).
Proof.
  rewrite /is_empty /elem_of /in_interval.
  split.
  - lia.
  - intros H.
    assert (~ low i <= low i <= high i).
    { apply H. }
    lia.
Qed.

Definition contains i1 i2 :=
  low i2 <= low i1 ∧ high i1 <= high i2.

Lemma contains_spec i1 i2 :
  low i1 <= high i1 →
  contains i1 i2 ↔ (∀ x, x ∈ i1 → x ∈ i2).
Proof.
  intros Hvalid.
  rewrite /contains /elem_of /in_interval.
  split.
  - lia.
  - intros H.
    pose proof (H (low i1)).
    pose proof (H (high i1)).
    lia.
Qed.
