From sys_verif Require Import options.
From stdpp Require Import list.

Open Scope Z_scope.

Definition list_sorted (l: list Z) :=
  ∀ (i1 i2: nat) (x1 x2: Z),
  l !! i1 = Some x1 →
  l !! i2 = Some x2 →
  (i1 ≤ i2)%nat →
  (x1 ≤ x2)%Z.

(* l2 is a sorted version of l1 *)
Definition sorted (l1 l2: list Z) :=
  (* not quite complete: should really say the count of each element is the same *)
  (∀ (x: Z), x ∈ l1 ↔ x ∈ l2) ∧
    length l1 = length l2 ∧
    list_sorted l2.

Fixpoint insert_sorted (l: list Z) y :=
  match l with
  | [] => [y]
  | x :: l => if decide (y ≤ x) then y :: x :: l
              else x :: insert_sorted l y
  end.

Lemma list_sorted_cons x l :
  list_sorted (x :: l) ↔
    (∀ y, l !! 0%nat = Some y → x ≤ y) ∧ list_sorted l.
Proof.
  split.
  - intros Hsorted.
    split.
    + intros y Hget.
      apply (Hsorted 0%nat 1%nat); auto.
    + intros i1 i2 x1 x2 Hget1 Hget2 Hle.
      apply (Hsorted (1 + i1)%nat (1 + i2)%nat); auto.
      lia.
  - intros [Hx Hsorted].
    intros i1 i2 x1 x2 Hget1 Hget2 Hle.

    apply lookup_cons_Some in Hget1.
    apply lookup_cons_Some in Hget2.
    destruct Hget1 as [ [? ?] | [? Hget1] ];
      destruct Hget2 as [ [? ?] | [? Hget2] ];
      subst.
    + lia.
    + assert (is_Some (l !! 0%nat)) as [y Hget1].
      { apply lookup_lt_Some in Hget2.
        apply lookup_lt_is_Some.
        lia. }
      transitivity y.
      { apply Hx; auto. }
      apply (Hsorted 0%nat (i2-1)%nat); auto; try lia.
    + lia.
    + apply (Hsorted (i1-1)%nat (i2-1)%nat); auto; try lia.
Qed.

Lemma insert_sorted_preserves_sorted l y :
  list_sorted l →
  list_sorted (insert_sorted l y).
Proof.
  induction l as [|x l IHl]; simpl.
  { intros Hsorted.
    rewrite /list_sorted. intros i1 i2 x1 x2 Hget1 Hget2 Hle.
    apply list_lookup_singleton_Some in Hget1. destruct Hget1; subst.
    apply list_lookup_singleton_Some in Hget2. destruct Hget2; subst.
    lia. }
  intros Hsorted.

  destruct (decide (y ≤ x)).
  - rewrite list_sorted_cons.
    split; [ | done ].
    simpl. intros y' H; inversion H; subst.
    lia.
  - assert (list_sorted (insert_sorted l y)).
    { apply IHl.
      apply list_sorted_cons in Hsorted.
      intuition auto. }
    rewrite list_sorted_cons.
    split; [ | done ].
    assert (x < y) by lia.
    intros y0 Hget1.
    (* FIXME: depends on [insert_sorted] having the same elements as [l] *)
    admit.
Admitted.
