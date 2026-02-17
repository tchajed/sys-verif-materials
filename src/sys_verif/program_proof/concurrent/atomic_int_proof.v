From sys_verif.program_proof Require Import prelude empty_ffi.

From sys_verif.program_proof Require Import concurrent_init.

Module atomic_int.
Section proof.
  Context `{hG: !heapGS Σ} {sem : go.Semantics} {package_sem : FILLME.Assumptions}.

  Definition lock_inv (l: loc) (P: w64 → iProp Σ) : iProp _ :=
    ∃ (x: w64),
        "Hx" ∷ l.[concurrent.AtomicInt.t, "x"] ↦ x ∗
        "HP" ∷ P x.

  (* The namespace of the lock invariant is only relevant when the lock is
  acquired _from within an invariant_, which is an exceptional circumstance.
  Hence we can just take the root namespace. *)
  Definition N: namespace := nroot.

  Definition is_atomic_int (l: loc) (P: w64 → iProp Σ): iProp _ :=
    ∃ (mu_l: loc),
    "mu" ∷ l.[concurrent.AtomicInt.t, "mu"] ↦□ mu_l ∗
    "Hlock" ∷ is_Mutex (mu_l) (lock_inv l P).

  (* This proof is automatic; we just assert it here. *)
  #[global] Instance is_atomic_int_persistent l P : Persistent (is_atomic_int l P).
  Proof. apply _. Qed.

  Lemma wp_NewAtomicInt (P: w64 → iProp Σ) :
    {{{ is_pkg_init concurrent ∗ P (W64 0) }}}
      @! concurrent.NewAtomicInt #()
    {{{ (l: loc), RET #l; is_atomic_int l P }}}.
  Proof.
    wp_start as "HP".
    wp_alloc m_ptr as "m"; wp_auto.
    wp_alloc l as "Hint".
    iApply struct_fields_split in "Hint". iNamed "Hint".
    cbn [concurrent.AtomicInt.x' concurrent.AtomicInt.mu'].
    iPersist "Hmu".
    iMod (init_Mutex (lock_inv l P)
           with "m [HP Hx]") as "Hlock".
    { iFrame. }
    wp_auto.
    iApply "HΦ".
    iFrame "#∗".
  Qed.

  Lemma wp_AtomicInt__Get l (P: w64 → iProp _) (Q: w64 → iProp Σ) :
    {{{ is_pkg_init concurrent ∗ is_atomic_int l P ∗ (∀ x, P x -∗ |={⊤}=> Q x ∗ P x) }}}
      l @! (go.PointerType concurrent.AtomicInt) @! "Get" #()
    {{{ (x: w64), RET #x; Q x }}}.
  Proof.
    wp_start as "[#Hint Hfupd]".
    iNamed "Hint".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hinv]". iNamed "Hinv".
    (* note that this step goes over the actual critical section where we load
    the x field *)
    (* TODO: explain the confusion between the x field of AtomicInt and the
    local x variable *)
    wp_auto.

    (* before we release the lock, we need to "fire" the user's fupd *)
    iMod ("Hfupd" with "HP") as "[HQ HP]".

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP Hx]").
    { iFrame. }

    iApply "HΦ".
    iFrame.
  Qed.

  Lemma wp_AtomicInt__Inc l (P: w64 → iProp _) (Q: w64 → iProp Σ) (y: w64) :
    {{{ is_pkg_init concurrent ∗ is_atomic_int l P ∗
          (∀ x, P x -∗ |={⊤}=> Q x ∗ P (word.add x y)) }}}
      l @! (go.PointerType concurrent.AtomicInt) @! "Inc" #y
    {{{ (x: w64), RET #(); Q x }}}.
  Proof.
    wp_start as "[#Hint Hfupd]". iNamed "Hint".
    wp_auto.
    wp_apply (wp_Mutex__Lock with "[$Hlock]") as "[Hlocked Hinv]". iNamed "Hinv".

    (* critical section *)
    wp_auto.

    (* before we release the lock, we "fire" the user's fupd *)
    iMod ("Hfupd" with "HP") as "[HQ HP]".

    wp_apply (wp_Mutex__Unlock with "[$Hlock $Hlocked HP Hx]").
    { (* re-prove the lock invariant; this only works because the fupd changed
         [P] to [P (word.add x y)], and this matches the physical state of the
         variable. *)
      iFrame. }

    iApply "HΦ".
    iFrame.
  Qed.

End proof.
End atomic_int.

#[global] Typeclasses Opaque atomic_int.is_atomic_int.
