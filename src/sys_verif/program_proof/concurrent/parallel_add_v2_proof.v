From iris.base_logic.lib Require Import ghost_var.
From iris.algebra Require Import frac_auth.

From sys_verif.program_proof Require Import prelude empty_ffi.
From sys_verif.program_proof Require Import concurrent_init.
From sys_verif.program_proof Require Import demos.barrier_proof.

Module parallel_add_v2.
Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

  Context `{barrierG0: barrier.barrierG Σ}.
  Context `{inG0: !inG Σ (frac_authR ZR)}.

  Definition lock_inv γ l : iProp _ :=
    ∃ (x: w64),
      "x" ∷ l ↦ x ∗
      "Hauth" ∷ own γ (●F (uint.Z x)).

  Lemma wp_ParallelAdd2 :
    {{{ is_pkg_init concurrent }}}
      @! concurrent.ParallelAdd2 #()
    {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
  Proof using All.
    wp_start as "_".
    iMod (own_alloc (●F 0 ⋅ ◯F 0)) as (γ) "[Hauth [Hfrag1 Hfrag2]]".
    { apply frac_auth_valid. done. }
    wp_auto.
    wp_alloc mu_ptr as "Hmu"; wp_auto.
    iMod (init_Mutex (lock_inv γ x_ptr) with "Hmu [$x $Hauth]") as "#Hlock".
    iPersist "m".
    wp_apply barrier.wp_New as "%b_l %γbar [#Hbar Hrecv]".
    iPersist "b".
    wp_apply (barrier.wp_Barrier__Add1 (own γ (◯F{1/2} 2)%I)
             with "[$Hbar $Hrecv]").
    iIntros "[Hsend1 Hrecv]".
    wp_auto.
    wp_apply (barrier.wp_Barrier__Add1 (own γ (◯F{1/2} 2)%I)
             with "[$Hbar $Hrecv]").
    iIntros "[Hsend2 Hrecv]".
    wp_auto.
    wp_bind (Fork _).
    iApply (wp_fork with "[Hfrag1 Hsend1]").
    { iModIntro.
      wp_auto.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"); iIntros "[Hlocked Hinv]".
      iNamed "Hinv".
      wp_auto.
      wp_apply wp_SumAssumeNoOverflow. iIntros (Hno_overflow). wp_auto.
      iMod (own_update_2 _ _ _ (●F (uint.Z x + 2) ⋅ ◯F{1/2} 2) with "Hauth Hfrag1") as "[Hauth Hfrag]".
      { apply frac_auth_update, Z_local_update. word. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $x Hauth]").
      { iModIntro. rewrite /named.
        iExactEq "Hauth".
        repeat (f_equal; try word). }
      wp_apply (barrier.wp_Barrier__Done with "[$Hbar $Hsend1 Hfrag]").
      { iFrame. }
      done. }

    iModIntro; wp_auto.
    wp_bind (Fork _).
    iApply (wp_fork with "[Hfrag2 Hsend2]").
    { iModIntro.
      wp_auto.
      wp_apply (wp_Mutex__Lock with "[$Hlock]"); iIntros "[Hlocked Hinv]".
      wp_auto.
      iNamed "Hinv".
      wp_auto.
      wp_apply wp_SumAssumeNoOverflow. iIntros (Hno_overflow). wp_auto.
      iMod (own_update_2 _ _ _ (●F (uint.Z x + 2) ⋅ ◯F{1/2} 2) with "Hauth Hfrag2") as "[Hauth Hfrag]".
      { apply frac_auth_update, Z_local_update. word. }
      wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $x Hauth]").
      { iModIntro. rewrite /named.
        iExactEq "Hauth".
        repeat (f_equal; try word). }
      wp_apply (barrier.wp_Barrier__Done with "[$Hbar $Hsend2 Hfrag]").
      { iFrame. }
      done. }

    iModIntro.
    wp_auto.
    wp_apply (barrier.wp_Barrier__Wait with "[$Hbar $Hrecv]").
    iIntros "[Hdone _]".
    iDestruct "Hdone" as "((_ & Hfrag1) & Hfrag2)". iCombine "Hfrag1 Hfrag2" as "Hfrag".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]"); iIntros "[Hlocked Hinv]".
    iNamed "Hinv".

    iDestruct (own_valid_2 with "Hauth Hfrag") as %Hx_eq.
    apply frac_auth_agree_L in Hx_eq. rewrite Hx_eq.
    wp_auto.
    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked $x Hauth]").
    { iModIntro. rewrite /named.
      iExactEq "Hauth". repeat (f_equal; try word). }
    wp_pures.
    iApply "HΦ".
    iPureIntro.
    word.
  Qed.

End proof.
End parallel_add_v2.
