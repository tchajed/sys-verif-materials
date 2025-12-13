From sys_verif Require Import options.
From stdpp Require Import fin_maps fin_sets gmap.

Open Scope Z_scope.

Section map.
  Context {V: Type}.
  Implicit Types (k: Z) (v: V) (m: gmap Z V) (s: gset Z).

  Lemma map_lookup_delete_insert (m: gmap Z V) (k: Z) (v: V) :
    delete k (<[ k := v ]> m) !! k = None.
  Proof.
    Search ((delete _ _) !! _).
    (* {OUTPUT} *)
    rewrite lookup_delete //.
  Qed.

  Lemma map_delete_insert (m: gmap Z V) (k: Z) (v: V) :
    delete k (<[ k := v ]> m) = delete k m.
  Proof.
    apply map_eq.
    (* {GOAL} *)
    intros k'.
    destruct (decide (k' = k)); subst.
    - (* EXERCISE: admit. *)
      (* SOLUTION *) rewrite !lookup_delete //. (* /SOLUTION *)

  (* ADMITTED *)
    - rewrite -> !lookup_delete_ne by auto.
      rewrite -> lookup_insert_ne by auto.
      auto.
  Qed.
  (* /ADMITTED *)

  Lemma set_property_manual_proof s1 s2 k :
    (s1 ∪ s2) ∖ {[k]} = (s1 ∖ {[k]}) ∪ (s2 ∖ {[k]}).
  Proof.
    (*| Set lemmas can be quite hard to use. Here's a manual proof, where we
    happen to find exactly the required lemma: |*)
    Search "∪" "∖".
    (* {OUTPUT} *)
    (*| The set library is highly general and we will need the `_L` variants of
    the lemmas for the `rewrite` tactic to work. |*)
    rewrite difference_union_distr_l_L //.
  Qed.

  (*| We can use much more powerful automation for this proof. |*)
  Lemma set_property s1 s2 k :
    (s1 ∪ s2) ∖ {[k]} = (s1 ∖ {[k]}) ∪ (s2 ∖ {[k]}).
  Proof.
    set_solver.
  Qed.

  Lemma set_property2 s1 s2 k :
    k ∉ s1  →
    (s1 ∪ s2) ∖ {[k]} = s1 ∪ (s2 ∖ {[k]}).
  Proof.
    set_solver.
  Qed.

  Lemma set_property3 s1 s2 :
    (∀ x, x ∈ s1 → 3 < x) →
    (s1 ∪ s2) ∖ {[2]} = s1 ∪ (s2 ∖ {[2]}).
  Proof.
  (* EXERCISE: Admitted. *)
    (* SOLUTION *)
    intros Helem.
    assert (2 ∉ s1).
    { intros Hin.
      apply Helem in Hin.
      lia. }
    set_solver.
  Qed.
  (* /SOLUTION *)

End map.
