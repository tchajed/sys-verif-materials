From iris.base_logic.lib Require Import ghost_var.
From sys_verif.program_proof Require Import prelude empty_ffi.
From New.generatedproof.sys_verif_code Require Import concurrent.

From New.proof Require Import std.
From sys_verif.program_proof.concurrent Require Import atomic_int_proof.

Module parallel_add_v1.
Section proof.
  Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

  (* we need "plain ghost variable" ghost state *)
  Context `{ghost_varG0: ghost_varG Σ Z}.

  #[local] Definition int_rep γ1 γ2 (x: w64): iProp _ :=
    ∃ (x1 x2: Z),
      "Hx1" ∷ ghost_var γ1 (1/2) x1 ∗
      "Hx2" ∷ ghost_var γ2 (1/2) x2 ∗
      "%Hsum" ∷ ⌜x1 ≤ 2 ∧ x2 ≤ 2 ∧ uint.Z x = (x1 + x2)%Z⌝.

  Lemma wp_ParallelAdd1 :
    {{{ is_pkg_init concurrent }}}
      @! concurrent.ParallelAdd1 #()
    {{{ (x: w64), RET #x; ⌜uint.Z x = 4⌝ }}}.
  Proof using ghost_varG0.
    wp_start as "_".
    wp_auto.
    iMod (ghost_var_alloc 0) as (γ1) "[Hv1_1 Hx1_2]".
    iMod (ghost_var_alloc 0) as (γ2) "[Hv2_1 Hx2_2]".
    wp_apply (atomic_int.wp_NewAtomicInt (int_rep γ1 γ2)
             with "[Hv1_1 Hv2_1]") as "%l #Hint".
    { iExists 0, 0. iFrame.
      iPureIntro.
      split; [ lia | ].
      split; [ lia | ].
      reflexivity. }

    iPersist "i".
    wp_apply (std.wp_Spawn (ghost_var γ1 (1/2) 2) with "[Hx1_2]").
    { clear Φ.
      iRename "Hx1_2" into "Hx".
      iIntros (Φ) "HΦ".
      wp_auto.
      wp_apply (atomic_int.wp_AtomicInt__Inc _ _
                  (λ _, ghost_var γ1 (1/2) 2) with "[$Hint Hx]").
      { iIntros (x) "Hrep".
        iNamed "Hrep".
        iDestruct (ghost_var_agree with "Hx1 Hx") as %->.
        iMod (ghost_var_update_2 2 with "Hx1 Hx") as "[Hx1 Hx]".
        { rewrite Qp.half_half //. }
        iModIntro.
        iFrame.
        iPureIntro.
        split; [ lia | ].
        split; [ lia | ].
        word. }
      iIntros (_) "Hx". wp_pures.
      iApply "HΦ". iFrame. }
    iIntros (h1) "Hh1".
    wp_auto.
    wp_apply (std.wp_Spawn (ghost_var γ2 (1/2) 2) with "[Hx2_2]").
    { clear Φ.
      iRename "Hx2_2" into "Hx".
      iIntros (Φ) "HΦ".
      wp_auto.
      wp_apply (atomic_int.wp_AtomicInt__Inc _ _
                  (λ _, ghost_var γ2 (1/2) 2) with "[$Hint Hx]").
      { iIntros (x) "Hrep".
        iNamed "Hrep".
        iDestruct (ghost_var_agree with "Hx2 Hx") as %->.
        iMod (ghost_var_update_2 2 with "Hx2 Hx") as "[Hx Hx2_2]".
        { rewrite Qp.half_half //. }
        iModIntro.
        iFrame.
        iPureIntro.
        split; [ lia | ].
        split; [ lia | ].
        word. }
      iIntros (_) "Hx". wp_pures.
      iApply "HΦ". iFrame. }
    iIntros (h2) "Hh2".
    wp_auto.
    wp_apply (wp_JoinHandle__Join with "[$Hh1]") as "Hx1_2".
    wp_apply (wp_JoinHandle__Join with "[$Hh2]") as "Hx2_2".
    wp_apply (atomic_int.wp_AtomicInt__Get _ _
                (λ x, ⌜uint.Z x = 4⌝)%I
             with "[$Hint Hx1_2 Hx2_2]").
     { iIntros (x) "Hrep".
       iNamed "Hrep".
       iDestruct (ghost_var_agree with "Hx1 Hx1_2") as %->.
       iDestruct (ghost_var_agree with "Hx2 Hx2_2") as %->.
       iModIntro.
       iFrame.
       iPureIntro.
       repeat split; try word. }
     iIntros (x Hx).
     wp_auto.
     iApply "HΦ".
     auto.
  Qed.

End proof.

#[global] Typeclasses Opaque int_rep.
#[global] Opaque int_rep.

End parallel_add_v1.
