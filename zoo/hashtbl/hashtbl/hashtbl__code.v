From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From hashtbl Require Import
  hashtbl__types.
From zoo Require Import
  options.

Parameter hashtbl٠eq : val.

Parameter hashtbl٠hash : val.

Definition hashtbl٠index : val :=
  fun: "k" "n" =>
    hashtbl٠hash "k" `rem` "n".

Definition hashtbl٠create : val :=
  fun: "n" =>
    { array٠make "n" §Nil, 0 }.

Definition hashtbl٠add' : val :=
  fun: "arr" "k" "v" =>
    let: "n" := array٠size "arr" in
    let: "i" := hashtbl٠index "k" "n" in
    array٠set "arr" "i" ‘Cons( "k", "v", array٠get "arr" "i" ).

Definition hashtbl٠bucket_iter_right : val :=
  rec: "bucket_iter_right" "b" "f" =>
    match: "b" with
    | Nil =>
        ()
    | Cons "k" "v" "b'" =>
        "bucket_iter_right" "b'" "f" ;;
        "f" "k" "v"
    end.

Definition hashtbl٠iter_aux : val :=
  fun: "buckets" "f" =>
    for: "i" := 0 to array٠size "buckets" begin
      hashtbl٠bucket_iter_right (array٠get "buckets" "i") "f"
    end.

Definition hashtbl٠iter_rev : val :=
  fun: "h" "f" =>
    hashtbl٠iter_aux "h".{buckets} "f".

Definition hashtbl٠resize : val :=
  fun: "h" =>
    let: "len" := array٠size "h".{buckets} * 2 in
    let: "new_buckets" := array٠make "len" §Nil in
    hashtbl٠iter_aux
      "h".{buckets}
      (fun: "k" "v" => hashtbl٠add' "new_buckets" "k" "v") ;;
    "h" <-{buckets} "new_buckets".

Definition hashtbl٠population : val :=
  fun: "h" =>
    "h".{size}.

Definition hashtbl٠inc_pop : val :=
  fun: "h" =>
    "h" <-{size} "h".{size} + 1 ;;
    let: "pop" := hashtbl٠population "h" in
    let: "cap" := array٠size "h".{buckets} * 2 in
    if: "pop" > "cap" then (
      hashtbl٠resize "h"
    ).

Definition hashtbl٠add : val :=
  fun: "h" "k" "v" =>
    hashtbl٠add' "h".{buckets} "k" "v" ;;
    hashtbl٠inc_pop "h".
