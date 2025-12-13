From sys_verif Require Import options.

(* META: The definition of binary numbers is based on the Software Foundation's
binary number exercise. *)

Inductive binary :=
| Z
| B0 (b: binary)
| B1 (b: binary)
.

Fixpoint to_nat (b: binary): nat :=
  match b with
  | Z => 0
  | B0 b => 2 * (to_nat b)
  | B1 b => 1 + 2 * (to_nat b)
  end.

Fixpoint add1 (b: binary): binary :=
  match b with
  | Z => B1 Z
  | B0 b => B1 b
  | B1 b => B0 (add1 b)
  end.

Fixpoint from_nat (n: nat): binary :=
  match n with
  | O => Z
  | S n => add1 (from_nat n)
  end.

Lemma to_nat_add1 b :
  to_nat (add1 b) = S (to_nat b).
Proof.
  induction b; simpl.
  - reflexivity.
  - rewrite PeanoNat.Nat.add_0_r.
    reflexivity.
  - lia.
Qed.

Lemma to_from_nat (n: nat) :
  to_nat (from_nat n) = n.
Proof.
  induction n; simpl.
  - reflexivity.
  - rewrite to_nat_add1. lia.
Qed.

(* To make the following definitions easier to read and write, we'll use some
notations, an idea taken from
https://coq.inria.fr/doc/V8.19.2/stdlib/Coq.PArith.BinPosDef.html. The notations
mimic the look of big-endian binary numbers, with each digit written in
sequence; this is the standard way of writing numbers with the most significant
digit at the front. Because of our [binary] inductive all numbers have to start
with a leading 0, which we give the special notation [0b0]. *)

#[local] Notation "p ~ 1" := (B1 p)
  (at level 7, left associativity, format "p '~' '1'").
#[local] Notation "p ~ 0" := (B0 p)
  (at level 7, left associativity, format "p '~' '0'").
#[local] Notation "0b0" := (Z).

(* this is what the notation looks like for an example number: *)
Lemma notation_example_1 :
  to_nat (0b0~1~0~0) = 4.
Proof. reflexivity. Qed.

Lemma notation_example_2 :
  to_nat (0b0~1~1~0~1) = 13. (* 0b1101 = 8+4+1 = 13 decimal *)
Proof. reflexivity. Qed.

(* To add two binary numbers, we'll use an auxilliary function [bin_add_carry]
which adds two numbers and increments by one to incorporate a "carry bit". These
two functions need to call each other recursively, which Coq supports using the
[with] syntax below, a feature called "mutual recursion". While this feature
looks complicated - and checking that a mutually recursive function is
terminating is indeed a bit complicated - you can think of it as defining a
single function which takes a boolean indicating whether a carry is needed or
not. *)
Fixpoint bin_add b1 b2 :=
  match b1, b2 with
  | p~1, q~1 => (bin_add_carry p q)~0
  | p~1, q~0 => (bin_add p q)~1
  | p~0, q~1 => (bin_add p q)~1
  | p~0, q~0 => (bin_add p q)~0
  | 0b0, q => q
  | p, 0b0 => p
  end
with bin_add_carry b1 b2 :=
       match b1, b2 with
       | p~1, q~1 => (bin_add_carry p q)~1
       | p~1, q~0 => (bin_add_carry p q)~0
       | p~0, q~1 => (bin_add_carry p q)~0
       | p~0, q~0 => (bin_add p q)~1
       | 0b0, q => add1 q
       | p, 0b0 => add1 p
       end.

(* This theorem gives a spec for both [bin_add] and [bin_add_carry]. Since the
two functions are defined mutually recursively, we'll need to prove them
mutually. This is needed so when we're reasoning about [bin_add] the induction
hypothesis includes something about [bin_add_carry] and vice versa, without
which we couldn't prove anything interesting about either function. *)
Lemma bin_add_carry_spec :
  ∀ b1 b2, to_nat (bin_add b1 b2) =
    to_nat b1 + to_nat b2 ∧
  to_nat (bin_add_carry b1 b2) =
    S (to_nat b1 + to_nat b2).
Proof.
  (* The proof is actually not that interesting, now that we've set everything
  up correctly and proven [to_nat_add1] already. It just requires considering
  every case in turn, and a little code to help Coq use the induction hypothesis
  correctly. *)
  induction b1; simpl.
  - intros.
    rewrite to_nat_add1. auto.
  - intros b2.
    split.
    + destruct b2 as [|b2'|b2']; simpl.
      * auto.
      * destruct (IHb1 b2') as [? ?]; lia.
      * destruct (IHb1 b2') as [? ?]; lia.
    + destruct b2 as [|b2'|b2']; simpl.
      * auto.
      * destruct (IHb1 b2') as [? ?]; lia.
      * destruct (IHb1 b2') as [? ?]; lia.
  - intros b2.
    destruct b2 as [|b2'|b2']; simpl.
    + rewrite to_nat_add1; lia.
    + destruct (IHb1 b2') as [? ?]; lia.
    + destruct (IHb1 b2') as [? ?]; lia.
Qed.

Lemma bin_add_spec b1 b2 :
  to_nat (bin_add b1 b2) = to_nat b1 + to_nat b2.
Proof.
  pose proof (bin_add_carry_spec b1 b2).
  intuition auto.
Qed.
