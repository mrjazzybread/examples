(* Based on:
   https://github.com/ocaml-multicore/picos/blob/fa1da88bf3643fa18af2357a426e74ea2ac31072/lib/picos_aux.htbl/picos_aux_htbl.ml
*)

type ('k, 'v) bucket = 
  | Nil 
  | Cons of 'k * 'v * ('k, 'v) bucket

type ('k, 'v) t = {
  mutable buckets : ('k, 'v) bucket array;
  mutable size : int;
}

let[@zoo.opaque] eq _ _ = assert false
let[@zoo.opaque] hash _ = assert false

let index k n = hash k mod n

let rec remove_assoc (k : 'k) (b : ('k, 'v) bucket) =
  match b with
  | Nil -> (false, Nil)
  | Cons (k', v, t) ->
      if eq k' k then (true, t)
      else
        let r, t = remove_assoc k t in
        (r, Cons (k', v, t))

let create (n : int) = { 
    buckets = Array.make n Nil;
    size = 0 
  }

let add' (arr : (('k, 'v) bucket) array) (k : 'k) (v : 'v) =
  let n = Array.size arr in
  let i = index k n in
  arr.(i) <- Cons(k, v, arr.(i))

let rec bucket_iter_right (b : ('k, 'v) bucket) f : unit =
  match b with
  |Nil -> ()
  |Cons(k, v, b') ->
    bucket_iter_right b' f;
    f k v

let iter (h : ('k, 'v) t) f =
  for i = 0 to Array.size h.buckets - 1 do
    bucket_iter_right h.buckets.(i) f
  done
