From sys_verif Require Import options.

Unset Printing Records.

(*| A queue is a standard data structure you're likely familiar with. The
logical state of a queue is a list of elements. The type of the elements doesn't
affect the implementation, so we'll make our queues polymorphic in the value
type, which will be called `V` throughout. A `queue V` has three main
operations:

- `empty: queue V` creates an empty queue
- `push: V -> queue V -> queue V` adds an element to the queue
- `pop: queue V -> option V * queue V` removes the oldest element in the
  queue, returning `None` if the queue was empty, and returns a new queue.
|*)

(*| ## Queue specification |*)

(* We'll start by representing the queue directly as a list, which will be slow
but works. This will be called the "spec" since we'll use it as the reference
model of the more efficient queue below. *)
Module spec.
  (* the order of this list will be the _pop_ order *)
  Definition queue V := list V.

  Definition empty V : queue V := [].

  Definition push {V} (v: V) (q: queue V) : queue V :=
    q ++ [v].

  Definition pop {V} (q: queue V): option V * queue V :=
    match q with
    | [] => (None, q)
    | x :: q' => (Some x, q')
    end.
End spec.

(*| ## Efficient implementation |*)

(*| The above implementation works, but push is actually quite slow: building
that appended list requires iterating over all the existing elements of the
queue. It turns out we can do better even with functional programming.

This class isn't about performance, let alone performance of functional
programs; if you're interested, read _Purely Functional Data Structures_ by
Chris Okasaki, the standard reference for this kind of thing. However, we can
still write down this efficient implementation and prove that it has the right
behavior.
|*)

Module impl.

  (*| The idea is to split the queue into two parts: we'll push onto
  `back_rev` with a simple cons operation, and pop from `front`. As the names
  imply, `back_rev` has elements in the wrong order: it's the push order and not
  the pop (dequeue) order. When `front` is empty, `pop` will reverse `back_rev`,
  make that the new front, and then proceed.

  Aside: You may have seen a queue implemented with two stacks; this is
  essentially the functional version of that implementation.

  The reason this is more efficient is a bit subtle: we have to do an amortized
  analysis. While the reverse may seem expensive, we can "pay" for it by banking
  an additional O(1) cost for every `push` operation, so both `push` and `pop`
  have amortized constant time. Again, not something to worry about in verifying
  it.
  |*)
  Record queue V := mkQueue {
      back_rev: list V;
      front: list V;
  }.
  (* We want the [V] argument to be implicit, so fix that up. *)
  Arguments mkQueue {V} _ _.
  Arguments back_rev {V} _.
  Arguments front {V} _.

  (*| `Record` types are new, so let me explain the syntax. The command above
      creates a new inductive type `queue` with a single constructor `mkQueue`, and
      that constructor takes two arguments for the fields `back_rev` and `front`.

    It also defines _projections_ to get the fields from a queue, functions
    `back_rev` and `front`.

    Rocq has special syntax for both creating records and using the projections,
    but for the sake of this example I won't use them.
  |*)

  Lemma example_queue_projections_1 {V} (v1 v2 v3: V) :
    back_rev (mkQueue [v1] [v2; v3]) = [v1].
  Proof. reflexivity. Qed.
  Lemma example_queue_projections_2 {V} (v1 v2 v3: V) :
    front (mkQueue [v1] [v2; v3]) = [v2; v3].
  Proof. reflexivity. Qed.

  Definition empty V : queue V :=
    mkQueue [] [].

  Definition push {V} (v: V) (q: queue V) : queue V :=
    mkQueue (v :: back_rev q) (front q).

  Definition pop {V} (q: queue V) : option V * queue V :=
    match front q with
    | x :: front' =>
        (* easy case: front has an element *)
        (Some x, mkQueue (back_rev q) front')
    | [] =>
        (* [new_front] will replace the back of the queue *)
        let new_front := rev (back_rev q) in
            match new_front with
            | [] => (None, q) (* queue was empty *)
            | x :: new_front' => (Some x, mkQueue [] new_front')
            end
    end.

  (*| Now let's state and prove the correctness of the queue.

      The first and most important step in the proof is to figure out how the
      state of our implementation maps to the state of the spec. This can be
      written as an abstraction function in this case. Remember that the spec
      kept a list in dequeue order, so that's what we need to produce here for
      the proof to go through.
 |*)

  Definition absr {V} (q: queue V) : spec.queue V :=
    front q ++ rev (back_rev q).

  Lemma empty_spec {V} :
    absr (empty V) = spec.empty V.
  Proof.
    reflexivity.
  Qed.

  Lemma push_spec {V} (v: V) (q: queue V) :
    absr (push v q) = spec.push v (absr q).
  Proof.
    rewrite /absr.
    destruct q as [b_rev f]; simpl.
    rewrite /spec.push.
    rewrite app_assoc //.
  Qed.

  Lemma pop_spec {V} (q: queue V) :
    (* this spec is a little trickier to setup: we want the returned element to
    be the same but have to more carefully relate the queues since they don't
    even have the same type. *)
    let (el, q') := pop q in
    let (spec_el, spec_q') := spec.pop (absr q) in
    el = spec_el ∧
    absr q' = spec_q'.
  Proof.
    rewrite /absr.
    destruct q as [b_rev f]; simpl.
    rewrite /pop; simpl.

    destruct f as [|x f']; simpl.
    - rewrite /spec.pop.
      destruct (rev b_rev) eqn:Hb_rev; simpl.
      + auto.
      + rewrite app_nil_r //.
    - auto.
  Qed.

End impl.
