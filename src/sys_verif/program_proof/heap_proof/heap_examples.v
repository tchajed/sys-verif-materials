From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import heap_init.

Section proof.
Context `{hG: !heapGS Σ} {sem : go.Semantics} {package_sem : FILLME.Assumptions}.

Lemma wp_Swap (l1 l2: loc) (x y: w64) :
  {{{ is_pkg_init heap.heap ∗ l1 ↦ x ∗ l2 ↦ y }}}
    @! heap.heap.Swap #l1 #l2
  {{{ RET #(); l1 ↦ y ∗ l2 ↦ x }}}.
Proof.
  wp_start as "Hpre".
  iDestruct "Hpre" as "[Hx Hy]".

  wp_auto.
  iApply "HΦ".
  iFrame.
Qed.

End proof.
