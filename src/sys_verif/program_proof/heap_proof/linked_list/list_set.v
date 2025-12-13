From sys_verif.program_proof Require Import prelude empty_ffi.
From New.generatedproof.sys_verif_code Require Import linked_list.


Section proof.
Context `{hG: !heapGS Σ} `{!globalsGS Σ} {go_ctx: GoContext}.

#[global] Instance : IsPkgInit linked_list := define_is_pkg_init True%I.
#[global] Instance : GetIsPkgInitWf linked_list := build_get_is_pkg_init_wf.

(* We abbreviate "linked list" to "ll" in some of these definitions to keep
specs and other theorem statements concise. *)

(* Notice we don't have to mention the actual sequence of elements in the linked
list in this proof. This is because the operations we implement for the linked
list all treat it as a set. *)
Definition ll_rep_pre (ll_rep: loc -d> gset w64 -d> iProp Σ) :
  loc -d> gset w64 -d> iProp Σ :=
  (λ l els,
      (⌜l = null ∧ els = ∅⌝) ∨
      (⌜l ≠ null⌝ ∧
         ∃ (x: w64) (next_l: loc) (next_els': gset w64),
            "Helem" :: l ↦s[linked_list.Node :: "elem"] x ∗
            "Hnext" :: l ↦s[linked_list.Node :: "next"] next_l ∗
            "%Hnext_els'" :: ⌜els = next_els' ∪ {[x]}⌝ ∗
            "Hnext_l" :: ▷ ll_rep next_l next_els'))%I.

#[global] Instance ll_rep_pre_contractive : Contractive ll_rep_pre.
Proof. solve_contractive. Qed.

Definition ll_rep := fixpoint ll_rep_pre.

Lemma ll_rep_unfold : ∀ l els, ll_rep l els ⊣⊢ ll_rep_pre ll_rep l els.
Proof. apply (fixpoint_unfold ll_rep_pre). Qed.

(* We need to use the two cases of [ll_rep] enough in this development that it's
worth having "unfolding" lemmas specific to the two cases. *)

Definition ll_rep_null l els :
  l = null →
  ll_rep l els ⊣⊢ ⌜els = ∅⌝.
Proof.
  intros Hnull.
  rewrite ll_rep_unfold /ll_rep_pre.
  iSplit.
  - iIntros "[ % | [% Hl]]"; intuition eauto.
  - eauto 10.
Qed.

Definition ll_rep_non_null l els :
  l ≠ null →
  ll_rep l els ⊣⊢
    ∃ (x: w64) (next_l: loc) (next_els': gset w64),
      "Helem" :: l ↦s[linked_list.Node :: "elem"] x ∗
      "Hnext" :: l ↦s[linked_list.Node :: "next"] next_l ∗
      "%Hnext_els'" :: ⌜els = next_els' ∪ {[x]}⌝ ∗
      "Hnext_l" :: ▷ ll_rep next_l next_els'.
Proof.
  intros Hnon_null.
  rewrite ll_rep_unfold /ll_rep_pre.
  iSplit.
  - iIntros "[ % | [% Hl]]"; intuition eauto.
  - eauto 10.
Qed.

Lemma wp_New :
  {{{ is_pkg_init linked_list }}}
    @! linked_list.New #()
  {{{ (l: loc), RET #l; ll_rep l ∅ }}}.
Proof.
  wp_start as "_".
  iApply "HΦ".
  iApply ll_rep_null; auto.
Qed.

Lemma wp_Node__Insert (l: loc) (els: gset w64) (elem: w64) :
  {{{ is_pkg_init linked_list ∗ ll_rep l els }}}
    l @ (ptrT.id linked_list.Node.id) @ "Insert" #elem
  {{{ (l': loc), RET #l'; ll_rep l' ({[elem]} ∪ els) }}}.
Proof.
  wp_start as "Hl".
  wp_auto.
  wp_alloc l' as "Hl2".
  iDestruct (typed_pointsto_not_null with "Hl2") as %Hnot_null.
  { reflexivity. }
  iApply struct_fields_split in "Hl2".
  iNamed "Hl2". cbn [linked_list.Node.elem' linked_list.Node.next'].
  wp_auto.
  iApply "HΦ".

  iApply ll_rep_non_null; [ done | ].
  iExists _, _, _; iFrame.
  iPureIntro.
  (* META: The ∪ in the postcondition is (intentionally) the reverse of what's in the
  representation predicate. The set reasoning needed is easily handled by
  [set_solver]. *)
  set_solver.
Qed.

(* META: not an exercise (Node__Pop should only be verified in a proof where the
abstract representation is a `list`) *)
(* SOLUTION *)
Lemma wp_Node__Pop (l: loc) (els: gset w64) :
  {{{ is_pkg_init linked_list ∗ ll_rep l els }}}
    l @ (ptrT.id linked_list.Node.id) @ "Pop" #()
  {{{ (x: w64) (l': loc) (ok: bool), RET (#x, #l', #ok);
      if ok then
        ⌜x ∈ els⌝ ∗
        (* not true: if x appears multiple times, then popping it once will not
        remove it from the list *)
        ll_rep l' (els ∖ {[x]})
      else ⌜els = ∅⌝
  }}}.
Proof.
  wp_start as "Hl".
  wp_auto.
  wp_if_destruct.
  - iApply "HΦ".
    iApply ll_rep_null in "Hl"; auto.
  - iApply ll_rep_non_null in "Hl"; auto.
    iNamed "Hl".
    wp_auto.
    iApply "HΦ".
    subst.
    iSplit; [ iPureIntro; set_solver | ].
    iExactEq "Hnext_l".
    f_equal.
Abort.
(* /SOLUTION *)

Lemma wp_Node__Contains (l: loc) (els: gset w64) (elem: w64) :
  {{{ is_pkg_init linked_list ∗ ll_rep l els }}}
    l @ (ptrT.id linked_list.Node.id) @ "Contains" #elem
  {{{ RET #(bool_decide (elem ∈ els)); ll_rep l els }}}.
Proof.
  wp_start as "Hl".
  wp_auto.

  iAssert (∃ els_left (n: loc),
                "n" :: n_ptr ↦ n ∗
                "Hn" :: ll_rep n els_left ∗
                "%Hels_left" :: (∃ els_done, ⌜els = els_done ∪ els_left ∧
                                              (elem ∉ els_done)⌝) ∗
                (* this part of the loop invariant is pretty tricky *)
                "Hrestore" :: (ll_rep n els_left -∗ ll_rep l els))%I
    with "[$n $Hl]" as "HI".
  { iSplit.
    { iPureIntro; simpl. exists ∅. set_solver.  }
    auto. }
  wp_for "HI".
  destruct (bool_decide_reflect (n = null)); subst.
  - rewrite decide_False.
    { inv 1. }
    rewrite decide_True //.
    iDestruct (ll_rep_null with "Hn") as %?; subst.
    { done. }
    wp_auto.
    destruct Hels_left as [els_done [-> Hnot_found]].
    iDestruct ("Hrestore" with "Hn") as "Hl".
    iDestruct ("HΦ" with "Hl") as "HΦ".
    iExactEq "HΦ". repeat f_equal.
    rewrite bool_decide_eq_false_2 //.
    set_solver.
  - rewrite decide_True //.
    iApply ll_rep_non_null in "Hn"; [ done | ].
    iNamed "Hn".
    wp_auto.
    wp_if_destruct.
    + wp_for_post.
      destruct Hels_left as [els_done [-> Hnot_found]].
      iDestruct ("Hrestore" with "[Hnext_l Helem Hnext]") as "Hl".
      { iApply ll_rep_non_null; auto. iFrame; eauto. }
      iDestruct ("HΦ" with "Hl") as "HΦ".
      iExactEq "HΦ". repeat f_equal.
      rewrite bool_decide_eq_true_2 //.
      set_solver.
    + wp_for_post.
      iFrame.
      iSplit.
      { destruct Hels_left as [els_done [-> Hnot_found]].
        iPureIntro.
        exists (els_done ∪ {[x]}).
        set_solver. }
      iIntros "Hl".
      iApply "Hrestore".
      iApply ll_rep_non_null; auto. iFrame; eauto.
Qed.

Lemma wp_Node__Delete l els (elem: w64) :
  {{{ is_pkg_init linked_list ∗ ll_rep l els }}}
    l @ (ptrT.id linked_list.Node.id) @ "Delete" #elem
  {{{ (l': loc), RET #l'; ll_rep l' (els ∖ {[elem]}) }}}.
Proof.
  iLöb as "IH" forall (l els).
  wp_start as "Hl".
  (* [wp_rec] isn't normally needed but in this case will take the first step of
  unfolding [Node__Delete]. *)
  wp_auto.
  wp_if_destruct.
  - (* base case: delete from an empty list *)
    iDestruct (ll_rep_null with "Hl") as %?; [ done | ]. subst.
    iApply "HΦ".
    replace (∅ ∖ {[elem]}) with (∅: gset w64) by set_solver.
    by iFrame.
  - (* recursive case: delete at head and recurse *)
    iApply ll_rep_non_null in "Hl"; [ done | ].
    iNamed "Hl".
    wp_auto.
    wp_if_destruct.
    + wp_apply ("IH" with "[$Hnext_l]").
      iIntros (l') "Hl".
      wp_auto.
      iApply "HΦ".
      iExactEq "Hl".
      f_equal.
      (* this is a case where we know the element was present before *)
      set_solver.
    + wp_apply ("IH" with "[$Hnext_l]").
      iIntros (l') "Hl'".
      wp_auto.
      iApply "HΦ".
      (* the original [Node] struct is being fully reused, but with a different
      [next] field, so we need to re-prove an [ll_rep] *)
      iApply ll_rep_non_null; [ done | ].
      iExists _, _, _; iFrame.
      iPureIntro.
      set_solver.
Qed.

(* Think carefully about how this spec relates to the implementation. Notice
that we are able to return [ll_rep l1 els1] in the postcondition, because
(unlike Delete) this implementation creates new nodes for the new list, copying
over each element from the first list. However, [ll_rep l2 els2] is consumed in
the process because in the base case [listAppend] creates a pointer to the
second list, so [ll_rep l2 els2] is contained within the new [ll_rep l2'
...]. *)
Lemma wp_Node__Append l1 els1 l2 els2 :
  {{{ is_pkg_init linked_list ∗ ll_rep l1 els1 ∗ ll_rep l2 els2 }}}
    l1 @ (ptrT.id linked_list.Node.id) @ "Append" #l2
  {{{ (l2': loc), RET #l2'; ll_rep l1 els1 ∗ ll_rep l2' (els1 ∪ els2) }}}.
Proof.
  iLöb as "IH" forall (l1 els1).
  wp_start as "[Hl1 Hl2]".
  wp_auto.
  wp_if_destruct.
  - iApply "HΦ".
    iDestruct (ll_rep_null with "Hl1") as %Hempty; [ done | ]. subst.
    iFrame.
    iExactEq "Hl2".
    f_equal.
    set_solver.
  - iApply ll_rep_non_null in "Hl1"; [ done | ].
    iNamed "Hl1".
    wp_auto.
    wp_apply ("IH" with "[Hnext_l Hl2]").
    { iFrame. }
    iIntros (l2') "[Hl1_next Hl2]".
    wp_pures.
    wp_alloc l2'' as "Hl2_new".
    iDestruct (typed_pointsto_not_null with "Hl2_new") as %Hnot_null2.
    { reflexivity. }
    iApply struct_fields_split in "Hl2_new".
    iDestruct "Hl2_new" as "(elem2 & next2)".
    wp_auto.
    iApply "HΦ".
    iSplitL "Helem Hnext Hl1_next".
    { iApply ll_rep_non_null; [ done | ].
      iFrame.
      iPureIntro.
      set_solver. }
    iApply ll_rep_non_null; [ done | ].
    iFrame.
    iPureIntro.
    set_solver.
Qed.

(* Here's an alternate spec for [Node__Append]. There's no
promise here that [ll_rep l1 els1] is retained.

  We might want to provide (and use) such a specification if later the
  implementation might change to modify [l1] in place. In general it's okay for
  a specification to hide details, like the fact that [ll_rep l1 els1] is
  preserved in this case.
 *)
Lemma wp_Node__Append' l1 els1 l2 els2 :
  {{{ is_pkg_init linked_list ∗ ll_rep l1 els1 ∗ ll_rep l2 els2 }}}
    l1 @ (ptrT.id linked_list.Node.id) @ "Append" #l2
  {{{ (l2': loc), RET #l2'; ll_rep l2' (els1 ∪ els2) }}}.
Proof.
  iIntros (Φ) "[#Hinit [Hl1 Hl2]] HΦ".
  wp_apply (wp_Node__Append with "[$Hl1 $Hl2]").
  iIntros (l2') "[Hl1 Hl2]".
  iApply "HΦ".
  iFrame.
Qed.

End proof.
