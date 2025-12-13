From sys_verif Require Import options.
From stdpp Require Import gmap decidable countable.
From RecordUpdate Require Import RecordUpdate.
From Perennial Require Import CountableTactics.
From Perennial Require Import ListZ.

Import listZ.

Open Scope Z.

Inductive color := red | yellow | green | blue | white.
#[global] Instance color_inhabited : Inhabited color := populate red.
#[global] Instance color_eq_dec : EqDecision color.
Proof. solve_decision. Defined.
#[global] Instance color_countable : Countable color.
Proof. solve_countable color_rec 5. Qed.

Definition COLORS := [red; yellow; green; blue; white].

Inductive rank := one | two | three | four | five.
#[global] Instance rank_inhabited : Inhabited rank := populate one.
#[global] Instance rank_eq_dec : EqDecision rank.
Proof. solve_decision. Defined.
#[global] Instance rank_countable : Countable rank.
Proof. solve_countable rank_rec 5. Qed.

Module card.
  (* every card.t is a valid card *)
  Record t := mk { col: color; rnk: rank; }.
  #[global] Instance inhabited : Inhabited t := populate (mk inhabitant inhabitant).
  #[global] Instance eq_dec : EqDecision t.
  Proof. solve_decision. Defined.
  #[global] Instance countable : Countable t.
  Proof.
    refine (inj_countable'
              (λ c, (col c, rnk c))
              (λ '(col, rnk), mk col rnk) _).
    intros []; auto.
  Qed.
End card.

Module game.
Record t := {
    deck: list card.t; (* unique *)
    hands: list (list card.t);
    discarded: gset card.t;
    hints_remaining: Z; (* [0, 8] *)
    fuse_remaining: Z; (* [0, 3] *)
    next_player: Z; (* [0, 2] *)
    played: color → list rank; (* lists are sorted *)
}.
End game.

Definition color_stack_to_cards (c: color) (rs: list rank): list card.t :=
   (λ r, card.mk c r) <$> rs.

Definition played_cards (played: color → list rank) : list (card.t) :=
  flat_map
      (λ c, color_stack_to_cards c (played c))
      COLORS.

Definition all_cards (s: game.t) :=
  s.(game.deck) ++
      concat (s.(game.hands)) ++
      elements s.(game.discarded) ++
      played_cards s.(game.played)
      .

Definition INIT_DECK: list card.t :=
  flat_map (λ c,
      flat_map (λ '(count, r), replicate count (card.mk c r))
      [(3, one); (2, two); (2, three); (2, four); (1, five)]
    ) COLORS.

Definition PLAYERS := 3.
Definition HAND_SIZE := 5.

Definition init (s: game.t): Prop :=
  Permutation INIT_DECK (all_cards s) ∧
  length s.(game.hands) = PLAYERS ∧
  (∀ p_idx, 0 ≤ p_idx < PLAYERS → length (s.(game.hands) !!! p_idx) = HAND_SIZE) ∧
  s.(game.discarded) = ∅ ∧
  s.(game.played) = (fun c => []) ∧
  s.(game.hints_remaining) = 8 ∧
  s.(game.fuse_remaining) = 3 ∧
  s.(game.next_player) = 0.

Inductive HintInfo :=
| HintColor (c: color)
| HintRank (r: rank).

#[global] Instance HintInfo_inhabitant : Inhabited HintInfo := populate (HintColor inhabitant).
#[global] Instance HintInfo_eq_dec : EqDecision HintInfo.
Proof. solve_decision. Qed.
#[global] Instance HintInfo_countable : Countable HintInfo.
Proof.
  refine (inj_countable'
            (λ i, match i with
                  | HintColor c => inl c
                  | HintRank r => inr r
                  end)
            (λ i, match i with
                  | inl c => HintColor c
                  | inr r => HintRank r
                  end) _).
  destruct x; auto.
Qed.

Inductive move :=
| Hint (dst_player: Z) (info: HintInfo) (count: Z)
| Discard (card_idx: Z)
| Play (card_idx: Z).
#[global] Instance move_inhabitant : Inhabited move := populate (Play inhabitant).
#[global] Instance move_eq_dec : EqDecision move.
Proof. solve_decision. Qed.

Definition game_over (s: game.t) :=
  (* 1. last fuse is used *)
  s.(game.fuse_remaining) = 0 ∨
  (* 2. all cards have been played *)
  (∀ c, length (s.(game.played) c) = 5) ∨
  (* 3. every player has played in the last round *)
  (s.(game.deck) = [] ∧
   ∀ p_idx, 0 ≤ p_idx < PLAYERS → length (s.(game.hands) !!! p_idx) = PLAYERS-1).

(* is r2 one higher than r1? *)
Definition rnk_succ (r1 r2: rank) : Prop :=
  match r1 with
  | one => r2 = two
  | two => r2 = three
  | three => r2 = four
  | four => r2 = five
  | five => False
  end.

Definition is_playable (c: card.t) (played: color → list rank): Prop :=
  match played c.(card.col) with
  | [] => c.(card.rnk) = one
  | top_rnk :: _ => rnk_succ c.(card.rnk) top_rnk
  end.

Definition fun_get {A} `{EqDecision A} {B} (x: A) (f: A → B) := f x.
#[global] Instance fun_get_set {A} `{EqDecision A} {B} (x0: A) :
  Setter (fun_get (A:=A) (B:=B) x0) :=
  λ update f, λ x, if decide (x = x0) then update (f x) else f x0.

Definition list_get {A} `{!Inhabited A} (idx: Z) (l: list A) := l !!! idx.
#[global] Instance set_list {A} `{!Inhabited A} (idx: Z) : Setter (list_get (A:=A) idx) :=
  λ update l, <[ idx := update (l !!! idx) ]> l.

Definition add_played (c': card.t) (played: color → list rank) : color → list rank :=
  played <| fun_get c'.(card.col) ::= cons c'.(card.rnk) |>.

Definition play_transition (s: game.t) (s': game.t) (m: move) :=
  ∃ card_idx,
    0 ≤ card_idx ≤ HAND_SIZE ∧
    m = Play card_idx ∧
    ∃ top_card deck', s.(game.deck) = top_card :: deck' ∧
    is_playable top_card s.(game.played) ∧
    s' = s
           <| game.played ::= add_played top_card |>
           <| game.deck := deck' |>
           <| game.hands; list_get s.(game.next_player); list_get card_idx := top_card |>
           <| game.next_player ::= λ p, (p + 1) `mod` PLAYERS |>
    (* TODO: give hint back *)
    .
