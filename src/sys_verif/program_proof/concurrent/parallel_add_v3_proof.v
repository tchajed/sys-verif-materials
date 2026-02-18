From iris.algebra Require Import frac_auth.

From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import concurrent_init.
From sys_verif.program_proof Require Import demos.barrier_proof.
From Perennial.algebra Require Import ghost_var.

Open Scope Z_scope.

Module parallel_add_v3.
Section proof.
  Context `{hG: !heapGS Σ} {sem : go.Semantics} {package_sem : concurrent.Assumptions}.
  Collection W := sem + package_sem.
  Set Default Proof Using "W".

  (* "plain" ghost variables ghost state, of type Z *)
  Context `{ghost_varG0: ghost_varG Σ Z}.

  Definition lock_inv γ1 γ2 l : iProp _ :=
    ∃ (x: w64) (x1 x2: Z),
      "Hx1" :: ghost_var γ1 (DfracOwn (1/2)) x1 ∗
      "Hx2" :: ghost_var γ2 (DfracOwn (1/2)) x2 ∗
      "x" ∷ l ↦ x ∗
      "%Hsum" ∷ ⌜x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = (x1 + x2)%Z⌝.

  Lemma wp_ParallelAdd3 :
    {{{ is_pkg_init concurrent }}}
      @! concurrent.ParallelAdd3 #()
    {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
  Proof using All.
    wp_start as "_".
    iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".
    wp_auto.
    wp_alloc mu_ptr as "Hmu"; wp_auto.
    iMod (init_Mutex (lock_inv γ1 γ2 i_ptr) with "Hmu [$i $Hv1_1 $Hv2_1]") as "#Hlock".
    { iPureIntro. done. }
    iPersist "m".
    wp_apply (std.wp_Spawn (ghost_var γ1 (DfracOwn (1/2)) 2) with "[Hx1_2]").
    {
      clear Φ.
      iIntros (Φ) "HΦ".
      wp_auto.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
      wp_auto.
      iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
      iMod (ghost_var_update_2 2 with "Hx1_2 Hx1") as "[Hx1_2 Hx1]".
      { rewrite dfrac_op_own Qp.half_half //. }
      wp_apply (wp_Mutex__Unlock with "[-HΦ Hx1_2 $Hlock $locked]").
      { iFrame.
        iPureIntro. split_and!; try word. }
      iApply "HΦ". iFrame.
    }
    iIntros (h_1_ptr) "Hjh1".
    wp_auto.
    wp_apply (std.wp_Spawn (ghost_var γ2 (DfracOwn (1/2)) 2) with "[Hx2_2]").
    {
      clear Φ.
      iIntros (Φ) "HΦ".
      wp_auto.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
      wp_auto.
      iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
      iMod (ghost_var_update_2 2 with "Hx2_2 Hx2") as "[Hx2_2 Hx2]".
      { rewrite dfrac_op_own Qp.half_half //. }
      wp_apply (wp_Mutex__Unlock with "[-HΦ Hx2_2 $Hlock $locked]").
      { iFrame.
        iPureIntro. split_and!; try word. }
      iApply "HΦ". iFrame.
    }
    iIntros (h_2_ptr) "Hjh2".
    wp_auto.
    wp_apply (wp_JoinHandle__Join with "[$Hjh1]"). iIntros "Hx1_2".
    wp_auto.
    wp_apply (wp_JoinHandle__Join with "[$Hjh2]"). iIntros "Hx2_2".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"). iIntros "[locked Hinv]". iNamed "Hinv".
    wp_auto.
    iDestruct (ghost_var_agree with "Hx1_2 Hx1") as %Heq; subst.
    iDestruct (ghost_var_agree with "Hx2_2 Hx2") as %Heq; subst.
    wp_apply (wp_Mutex__Unlock with "[$locked $Hlock Hx1 Hx2 x]").
    { iFrame. iPureIntro. split_and!; word. }
    iApply "HΦ".
    iPureIntro. word.
  Qed.

End proof.
End parallel_add_v3.
