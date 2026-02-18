From sys_verif.program_proof Require Import prelude.
From New.proof Require Export std.
From New.generatedproof.sys_verif_code Require Export functional.
From Perennial Require Import base.

Section proof.
Context `{hG: heapGS Σ} `{!ffi_semantics _ _}
  {sem : go.Semantics} {package_sem : functional.Assumptions}.
Collection W := sem + package_sem.

#[global] Instance : IsPkgInit (iProp Σ) functional := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf (iProp Σ) functional := build_get_is_pkg_init_wf.

End proof.
