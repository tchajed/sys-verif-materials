(*| # Ltac reference
|*)

Set Default Goal Selector "!".

(*| A "backwards" proof, working from the goal to the premises. |*)
Lemma propositional_demo_1 (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros HPQ HQR HP.
  apply HQR. (* {GOAL DIFF} *)
  apply HPQ.
  apply HP.
Qed.

(*| A "forwards" proof, working from the premises to the goal. |*)
Lemma propositional_demo_2 (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros HPQ HQR HP.
  apply HPQ in HP. (* {GOAL DIFF} *)
  apply HQR in HP.
  assumption.
Qed.

(*| An automated proof using a solver. |*)
Lemma propositional_demo_3 (P Q R : Prop) :
  (P -> Q) -> (Q -> R) -> P -> R.
Proof. (* {GOAL} *)
  intuition auto.
Qed.

Lemma many_goals (P Q R : Prop) :
  P /\ Q /\ R.
Proof.
  repeat split. (* {GOALS 3} *)
  - admit.
  - idtac. (* {GOAL} *)
    admit.
  - admit.
Abort.
