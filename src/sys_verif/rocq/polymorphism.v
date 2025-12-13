(*| # Lists and polymorphism |*)
(* META: this turned out to be mostly redundant and not as clean as Software
Foundations chapter:
https://softwarefoundations.cis.upenn.edu/lf-current/Poly.html *)

From sys_verif Require Import options.
From stdpp Require Import fin_maps fin_sets gmap.

Open Scope Z_scope.

(*| ### Option datatype |*)

(*| One of the core datatypes used in functional programming is the "option"
data type.

Sometimes, we can sometimes compute a result, but other times we want to return
"nothing"; hence we want to return an optional result. For example, division by
zero might return nothing, but a numerical result in all other cases.  For
positive numbers `a` and `b`, `a - b` normally returns a number, but if `b < a`
then it returns nothing. Let's see how we might encode the subtraction function:
 |*)

Inductive SubtractionResult :=
| Result (v: nat)
| Underflow.

Definition pos_subtract (a b: nat): SubtractionResult :=
  if decide (a ≤ b)%nat then Result (b - a)%nat else Underflow.

(*| This is nice, but for division we might need a new (very similar) datatype
that holds an optional `Z` value: |*)

Inductive DivisionResult :=
| DivResult (v: Z)
| DivideByZero.

Definition div_err (a b: Z): DivisionResult :=
  if decide (b ≠ 0) then DivResult (a / b) else DivideByZero.

(*| The typical solution in functional programming is to use a single
_polymorphic_ option datatype that covers the use case of both
`SubtractionResult` and `DivisionResult`. We show the definition here in a
module, but then will go back to using the definition from Rocq: |*)

Module option_def.
  Inductive option (A: Type) :=
  | Some (v: A)
  | None.
End option_def.

(*| This is like the above definitions, but we've used generally useful names,
and instead of the value in the "result" case being a specific type, it's now of
type `A` which is a parameter to `option`.

What is this `option` thing we've created? A good way to think about it is that
`option` is a _function_ from a `Type` (which we call `A`) to another type
(`option A`). We can see that this is exactly how Rocq sees it:
 |*)

Check option : Type -> Type.



Module lists.

(*| Rocq has a built-in datatype for lists. Let's see some examples of computing
with lists: |*)

Definition ex_list_a: list Z := [3; 2; 5].
Definition ex_list_b: list Z := [4].

(*| We can append lists, which has notation `l1 ++ l2`. |*)

Definition ex_app : ex_list_a ++ ex_list_b = [3; 2; 5; 4].
Proof. reflexivity. Qed.

(*| We can get the "head" or first element of a list. This returns [Some 3]
rather than just 3 because it has to  |*)

Definition ex_head: head ex_list_a = Some 3.
Proof. reflexivity. Qed.

Definition ex_list_a_at_1 : ex_list_a !! 1%nat = Some 2.
Proof. reflexivity. Qed.

End lists.
