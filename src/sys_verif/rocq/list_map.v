From sys_verif Require Import options.

From stdpp Require Import decidable.

Definition list_map (K: Type) {H: EqDecision K} (V: Type) :=
  list (K * V).

Section list_map.

  Context {K: Type} {H: EqDecision K} {V: Type}.

  Definition empty_list_map : list_map K V := [].

  Fixpoint find (x: K) (m: list_map K V) : option V :=
    match m with
    | [] => None
    | (x', v) :: m' => if decide (x = x') then Some v else find x m'
    end.

  Definition update (x : K) (v: V) (m: list_map K V) : list_map K V :=
    (x, v) :: m.

  Lemma find_empty_list_map x :
    find x empty_list_map = None.
  Proof. reflexivity. Qed.

  Lemma find_update_eq (m: list_map K V) x v :
    find x (update x v m) = Some v.
  Proof.
    rewrite /update. simpl.
    rewrite -> decide_True by auto.
    reflexivity.
  Qed.

  Lemma find_update_neq (m: list_map K V) x y o :
    x ≠ y → find x (update y o m) = find x m.
  Proof.
    intros Hne.
    rewrite /update. simpl.
    rewrite -> decide_False by auto.
    reflexivity.
  Qed.

End list_map.
