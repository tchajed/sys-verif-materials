From stdpp Require Import numbers.
From sys_verif Require Import options.

Definition digit := Z.
Definition big_int := list digit.

(*| Now we need some operations to do things with `big_int`s. |*)

Definition zero : big_int := [].
(* This is only intended to work when `0 ≤ x < 10`. *)
Definition from_digit (x: digit) : big_int := [x].

(*| The next operation that will be part of the "public interface" is
`big_int_add`, but defining that operation requires some helper functions. |*)

Definition digit_sum_carry (d1 d2: digit): (digit * digit) :=
  (d1 + d2 `mod` 10, d1 + d2 `div` 10).

Fixpoint add_one (b : big_int) (d : digit) : big_int :=
  match b with
  | [] => if decide (d = 0) then [] else [d]
  | h :: t =>
      let (sum, carry) := digit_sum_carry h d in
      sum :: add_one t carry
  end.

Fixpoint add_with_carry (b1 b2 : big_int) (carry : digit) : big_int :=
  match b1, b2 with
  | [], [] => if decide (carry = 0) then [] else [carry]
  | d1 :: t1, [] => add_one (d1 :: t1) carry
  | [], d2 :: t2 => add_one (d2 :: t2) carry
  | d1 :: t1, d2 :: t2 =>
      let (sum, new_carry) := digit_sum_carry d1 d2 in
      add_one (sum :: add_with_carry t1 t2 new_carry) carry
  end.

Definition big_int_add (b1 b2 : big_int) : big_int :=
  add_with_carry b1 b2 0.

(*| Finally, we'll provide a comparison function for big integers: *)

Definition big_int_le (b1 b2: big_int) : bool.
Admitted. (* exercise for the reader *)

(*| To summarize, the interface to the code we export to the client (which we'll
have to write a spec for) consists of the following signatures:

```rocq
Definition big_int : Type.

Definition zero : big_int.
(** requires [0 ≤ x < 10] *)
Definition from_digit (x: Z) : big_int.

Definition big_int_add: big_int -> big_int -> big_int.
Definition big_int_le : big_int -> big_int -> bool.
```

The user of this implementation should not need to know the definitions of any
of these.

|*)

(*| The core idea of a _model-based specification_ is to relate this code to a
spec based on a model of `big_int`. In this case, the natural model is that a
`big_int` represents an integer. We can view all of the operations as
manipulating this abstract integer (even if it never appears in the code), and
that's exactly what the spec will show.

The specification needs to pick a consistent way to relate a `big_int` to the
abstract `Z` it represents, which we call an _abstraction function_. The
function uses the suffix `_rep` for "representation" since it gives what a `i:
big_int` represents in the abstract model.

|*)

Definition rep_type := Z.
Fixpoint big_int_rep (i: big_int) : rep_type :=
  match i with
  | [] => 0
  | d :: i => d + 10 * big_int_rep i
  end.

(*| After picking an abstraction function, we relate all of the code to
specifications using `Z` and its related functions. The pattern might be easiest
to pick out from the example, but we'll shortly present it generically as well.
|*)

Lemma zero_spec : big_int_rep zero = 0.
Proof. reflexivity. Qed.

Lemma from_digit_spec x :
  0 ≤ x < 10 →
  big_int_rep (from_digit x) = x.
Proof.
  intros. simpl. (* {GOAL} *) lia.
Qed.

(* I've written this using `Z.add` rather than infix `+` just to make the
pattern more obvious. *)
Lemma big_int_add_spec : forall i1 i2,
  big_int_rep (big_int_add i1 i2) = Z.add (big_int_rep i1) (big_int_rep i2).
Proof.
Admitted.

Lemma big_int_le_spec : forall i1 i2,
  big_int_le i1 i2 = bool_decide (big_int_rep i1 ≤ big_int_rep i2).
Proof.
Admitted.
