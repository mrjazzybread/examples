let[@zoo.opaque] eq _ _ = assert false
let[@zoo.opaque] hash _ = assert false

type ('k, 'v) bucket = Nil | Cons of 'k * 'v * ('k, 'v) bucket

type ('k, 'v) tbl = {
  mutable buckets : ('k, 'v) bucket array;
  mutable size : int;
}

type ('k, 'v) t = ('k, 'v) tbl

let index k n = hash k mod n
let create (n : int) = { buckets = Array.make n Nil; size = 0 }

let add' (arr : ('k, 'v) bucket array) (k : 'k) (v : 'v) =
  let n = Array.size arr in
  let i = index k n in
  arr.(i) <- Cons (k, v, arr.(i))

let rec bucket_iter_right (b : ('k, 'v) bucket) f : unit =
  match b with
  | Nil -> ()
  | Cons (k, v, b') ->
      bucket_iter_right b' f;
      f k v

let iter_aux (buckets : ('k, 'v) bucket array) f =
  for i = 0 to Array.size buckets - 1 do
    bucket_iter_right buckets.(i) f
  done

let iter_rev (h : ('k, 'v) tbl) f = iter_aux h.buckets f

let resize (h : ('k, 'v) tbl) =
  let len = Array.size h.buckets * 2 in
  let new_buckets = Array.make len Nil in
  iter_aux h.buckets (fun k v -> add' new_buckets k v);
  h.buckets <- new_buckets

let population (h : ('k, 'v) tbl) = h.size

let inc_pop (h : ('k, 'v) tbl) =
  h.size <- h.size + 1;
  let pop = population h in
  let cap = Array.size h.buckets * 2 in
  if pop > cap then resize h

let add (h : ('k, 'v) tbl) (k : 'k) (v : 'v) =
  add' h.buckets k v;
  inc_pop h
