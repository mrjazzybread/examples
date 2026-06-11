From zoo Require Import
  prelude.
From zoo.language Require Import
  typeclasses
  notations.
From zoo_std Require Import
  array.
From zoo Require Import
  options.

Notation "'Nil'" := (
  in_type "hashtbl.hashtbl.bucket" 0
)(in custom zoo_tag
).
Notation "'Cons'" := (
  in_type "hashtbl.hashtbl.bucket" 1
)(in custom zoo_tag
).

Notation "'buckets'" := (
  in_type "hashtbl.hashtbl.t" 0
)(in custom zoo_field
).
Notation "'size'" := (
  in_type "hashtbl.hashtbl.t" 1
)(in custom zoo_field
).
