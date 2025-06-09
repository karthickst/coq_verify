Require Import String.
Require Import List.

(* Define the TradePosition type *)
Record TradePosition := {
  symbol: string;
  entry_price: nat;
  quantity: nat
}.

(* Define the TradePositionSystem type *)
Record TradePositionSystem := {
  positions: list (string * TradePosition);
  position_id_counter: nat
}.

(* Define the open_position function *)
Definition open_position (tps: TradePositionSystem) (symbol: string) (entry_price: nat) (quantity: nat) : TradePositionSystem * string :=
  let new_position_id := string_of_nat (S (position_id_counter tps)) in
  let new_positions := (new_position_id, {| symbol := symbol; entry_price := entry_price; quantity := quantity |}) :: positions tps in
  ({| positions := new_positions; position_id_counter := S (position_id_counter tps) |}, new_position_id).

(* Define the close_position function *)
Definition close_position (tps: TradePositionSystem) (position_id: string) : option TradePositionSystem :=
  match find (fun x => fst x =? position_id) (positions tps) with
  | Some _ => Some {| positions := filter (fun x => fst x <>? position_id) (positions tps); position_id_counter := position_id_counter tps |}
  | None => None
  end.

(* Define the get_positions function *)
Definition get_positions (tps: TradePositionSystem) : list (string * TradePosition) :=
  positions tps.

(* Theorem 1: Opening a new position always returns a unique identifier *)
Theorem open_position_unique_id :
  forall (tps: TradePositionSystem) (symbol: string) (entry_price: nat) (quantity: nat),
    let (new_tps, new_position_id) := open_position tps symbol entry_price quantity in
    ~ In new_position_id (map fst (positions tps)).
Proof.
  intros. unfold open_position. simpl.
  apply not_in_map_fst_intro. auto.
Qed.

(* Theorem 2: Closing a position always removes it from the system *)
Theorem close_position_removes :
  forall (tps: TradePositionSystem) (position_id: string),
    match close_position tps position_id with
    | Some new_tps => ~ In position_id (map fst (positions new_tps))
    | None => True
    end.
Proof.
  intros. unfold close_position.
  destruct (find (fun x : string * TradePosition => fst x =? position_id) (positions tps)) eqn:find_eq.
  - apply not_in_map_fst_intro. apply filter_In. auto.
  - auto.
Qed.

(* Theorem 3: The system never allows closing a non-existent position *)
Theorem close_position_non_existent :
  forall (tps: TradePositionSystem) (position_id: string),
    ~ In position_id (map fst (positions tps)) ->
    close_position tps position_id = None.
Proof.
  intros. unfold close_position.
  rewrite find_eq_None_iff. auto.
Qed.
