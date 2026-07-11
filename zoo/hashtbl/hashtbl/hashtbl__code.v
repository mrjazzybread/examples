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

Definition hashtbl٠remove_assoc : val :=
  rec: "remove_assoc" "k" "b" =>
    match: "b" with
    | Nil =>
        (false, §Nil)
    | Cons "k'" "v" "t" =>
        if: hashtbl٠eq "k'" "k" then (
          (true, "t")
        ) else (
          let: "r", "t" := "remove_assoc" "k" "t" in
          ("r", ‘Cons( "k'", "v", "t" ))
        )
    end.

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

Definition hashtbl٠iter : val :=
  fun: "h" "f" =>
    for: "i" := 0 to array٠size "h".{buckets} begin
      hashtbl٠bucket_iter_right (array٠get "h".{buckets} "i") "f"
    end.
