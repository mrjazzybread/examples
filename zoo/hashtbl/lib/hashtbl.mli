(*@ open Fin_maps *)

type ('k, 'v) t
(*@ model : ('k, 'v sequence) fin_map *)

val create : int -> ('k, 'v) t
(*@ h = create n
    requires n > 0
    ensures h = ∅ *)

val add : ('k, 'v) t -> 'k -> 'v -> unit
(*@ add h k v
    consumes k
    consumes v
    modifies h @ ('K, 'V) T
    ensures h = old (add k (Sequence.cons v (h[k])) h) *)

val find : ('k, 'v) t -> 'k -> 'v
(*@ v = find h k
    preserves h @ ('K, 'V) T
    preserves k @ 'K
    ensures Sequence.hd (h[k]) = v *)

(*@ function cardinality (m : ('k, 'v sequence) fin_map) : integer =
      fold (λ k s acc -> acc + Sequence.length s) 0 m *)

val population : ('k, 'v) t -> int
(*@ n = population h
    ensures n = cardinality h *)

val iter_rev : ('k, 'v) t -> ('k -> 'v -> unit) -> unit

(* @ predicate permitted *)
(*     (m : fin_map val (val sequence)) (h : ('k * 'v) sequence) *)

(* val iter : *)
(* (\*@ iter_rev h f m, *)
(*     ITER *)
(*     ~permitted:(permitted m) *)
(*     ~complete:(complete m) *)
(*     ~step:(fun x => let (k, v) = x in f k v) *\) *)
