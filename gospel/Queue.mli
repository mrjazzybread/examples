(*@ open Sequence *)

type 'a t
(** The type of queues containing elements of type ['a]. *)
(*@ mutable model : val sequence *)

val create : unit -> 'a t
(** Return a new queue, initially empty. *)
(*@ q = create ()
    ensures q = [] *)

val clear : 'a t -> unit
(** Discard all elements from a queue. *)
(*@ clear q
    modifies q
    ensures q = [] *)
