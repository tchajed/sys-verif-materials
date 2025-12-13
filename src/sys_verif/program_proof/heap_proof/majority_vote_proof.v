From stdpp Require Import list decidable.
From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init.

(** The proof of the FindMajority algorithm comes from _Program Proofs_ by K.
Rustan M. Leino, chapter 13.7. *)

Section count_occurrence.

Context `{EqDecision A}.
Implicit Types (xs: list A) (x a: A) (lo hi: nat).

Fixpoint list_count xs a : Z :=
  match xs with
  | [] => 0
  | x :: xs =>
      (if decide (x = a) then 1 else 0) + list_count xs a
  end.

Lemma list_count_app xs1 xs2 x :
  list_count (xs1 ++ xs2) x = list_count xs1 x + list_count xs2 x.
Proof.
  induction xs1; simpl; lia.
Qed.

Definition list_sub_count `{EqDecision A} (xs: list A) (lo hi: nat) (x: A) :=
  list_count (subslice lo hi xs) x.

Lemma split_sub_count `{EqDecision A} (xs: list A) (lo mid hi: nat) (x: A) :
  (lo ≤ mid ∧ mid ≤ hi ∧ hi ≤ length xs)%nat →
  list_sub_count xs lo mid x + list_sub_count xs mid hi x =
    list_sub_count xs lo hi x.
Proof.
  intros H.
  rewrite /list_sub_count.
  rewrite -(subslice_app_contig lo mid hi xs); [ lia | ].
  rewrite list_count_app //.
Qed.

Lemma distinct_list_count xs x y :
  x ≠ y →
  list_count xs x + list_count xs y ≤ length xs.
Proof.
  intros Hne.
  induction xs; simpl.
  - lia.
  - destruct (decide _), (decide _); subst; try lia.
    congruence.
Qed.

Lemma distinct_sub_count xs lo hi x y :
  (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ length xs)%nat →
  x ≠ y →
  list_sub_count xs lo hi x + list_sub_count xs lo hi y ≤ hi - lo.
Proof.
  intros H Hne.
  rewrite /list_sub_count.
  transitivity (length (subslice lo hi xs)).
  - apply distinct_list_count; auto.
  - rewrite subslice_length; lia.
Qed.

Definition has_majority xs x := length xs < 2 * list_count xs x.
Definition sub_has_majority xs lo hi x := hi - lo < 2 * list_sub_count xs lo hi x.

Lemma has_majority_to_sub xs x :
  has_majority xs x →
  sub_has_majority xs 0 (length xs) x.
Proof.
  rewrite /has_majority /sub_has_majority.
  rewrite /list_sub_count.
  rewrite -subslice_complete.
  lia.
Qed.

End count_occurrence.

Section goose.

Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

Lemma wp_FindMajority (a_s: slice.t) q (xs: list w32) (K: w32) :
  {{{ is_pkg_init heap.heap ∗ a_s ↦*{q} xs ∗ ⌜has_majority xs K⌝
  }}}
    @! heap.heap.FindMajority #a_s
  {{{ RET #K; a_s ↦*{q} xs }}}.
Proof.
  wp_start as "[Ha %Hmajority]".
  assert (1 ≤ length xs)%nat as Hlen_nz.
  { rewrite /has_majority in Hmajority.
    destruct xs; simpl in *; lia. }
  list_elem xs 0 as x0.
  iDestruct (own_slice_len with "Ha") as %Hsz.
  wp_auto.
  wp_pure.
  { word. }
  wp_apply (wp_load_slice_elem with "[$Ha]").
  { word. }
  { eauto. }
  iIntros "Ha".
  wp_auto.
  iPersist "a l".

  iAssert (∃ (k0: w32) (lo hi c: w64),
          "Ha" ∷ own_slice a_s q xs ∗
          "k" ∷ k_ptr ↦ k0 ∗
          "lo" ∷ lo_ptr ↦ lo ∗
          "hi" ∷ hi_ptr ↦ hi ∗
          "c" ∷ c_ptr ↦ c ∗
          "%Hbound" ∷ ⌜uint.Z lo ≤ uint.Z hi ≤ Z.of_nat (length xs)⌝ ∗
          "%Hc" ∷ ⌜uint.Z c = list_sub_count xs (uint.nat lo) (uint.nat hi) k0⌝ ∗
          "%Hmajority_range" ∷ ⌜sub_has_majority xs (uint.nat lo) (uint.nat hi) k0⌝ ∗
          "%Hmajority_all" ∷ ⌜sub_has_majority xs (uint.nat lo) (length xs) K⌝)%I
    with "[-HΦ]" as "HI".
  { iFrame.
    iPureIntro.
    change (uint.Z (W64 0)) with 0.
    change (uint.Z (W64 1)) with 1.
    change (Z.to_nat 0) with 0%nat.
    change (Z.to_nat 1) with 1%nat.
    assert (list_sub_count xs 0 1 x0 = 1) as Hsub_count.
    { rewrite /list_sub_count /=.
      destruct xs as [|x0' xs']; [ simpl in *; lia | ].
      simpl in *.
      destruct (decide _); [ lia | congruence ].
    }
    split_and!; auto; try word.
    + rewrite /sub_has_majority.
      lia.
    + apply has_majority_to_sub; auto. }
  wp_for "HI".
  wp_if_destruct.
  - list_elem xs (sint.Z hi) as hi_elem.
    wp_pure.
    { word. }
    wp_apply (wp_load_slice_elem with "[$Ha]") as "Ha"; [ word | by eauto | ].
    admit.
  - iDestruct ("HΦ" with "Ha") as "HΦ".
    iExactEq "HΦ".
    repeat f_equal.
    admit.
Abort.

End goose.
