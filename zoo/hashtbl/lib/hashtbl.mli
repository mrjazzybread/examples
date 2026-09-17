(*@ open Fin_maps *)

type ('k, 'v) t
(*@ model : (val, val sequence) fin_map *)

val create : int -> ('k, 'v) t
(*@ h = create n
    ensures h = ∅ *)

val population : ('k, 'v) t -> int
(*@ n = population h
    ensures n = Fin_maps.population h *)

val add : ('k, 'v) t -> 'k -> 'v -> unit
(*@ add h k v
    modifies h
    ensures h = add k (Sequence.cons v (old (h[k]))) (old h) *)
