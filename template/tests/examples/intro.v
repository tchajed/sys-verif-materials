(*| ---
category: lecture-note
---

# Introduction to Rocq
|*)

(** META: This is a meta comment, which is not output to either the lecture or the
solution source. *)

(* META *)
(* This file is an example of a literate Coq file for lecture and demo
notes. *)
(* /META *)

(*| In this lecture, we'll get an introduction to functional programming and see
how Rocq supports both writing and verifying functional programs.

To write functional programs, we'll start by defining some data types for
our functions to operate on. |*)

Inductive day : Type :=
| monday
| tuesday
| wednesday
| thursday
| friday
| saturday
| sunday.

(*| Now what we have `day`, we can define functions on days: |*)

(* META: the following coqdoc comment will be inserted as Coq input rather
than surrounding text *)
(** next_weekday is a simple example of a function operating on [day] *)
Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_weekday friday). (* {OUTPUT} *)

Lemma test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  (* The simpl tactic computes functions in the goal. *)
  simpl. (* {GOAL} *)
  reflexivity.
Qed.
