type ('k, 'v) t
(*@ model : ('k, 'v sequence) fmap *)

val eq : 'k -> 'k -> bool
(*@ b = eq k1 k2
    ensures b <-> k1 = k2 *)

val create : int -> t
(*@ h = create n
    ensures h = ∅ *)

val population : t -> int
(*@ n = population h
    ensures n = cardinality h *)

val add : ('k, 'v) t -> 'k -> 'v -> unit
(*@ add h k v
    ensures h = <[k:= cons v (h !!! k)]> *)
