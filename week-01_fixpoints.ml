(* week-01_fixpoints.ml *)
(* FPP 2020 - YSC3236 2020-2011, Sem1 *)
(* Olivier Danvy <danvy@yale-nus.edu.sg> *)
(* Version of 20 Aug 2020, with an attuned definition of infinite_self_composition *)
(* was: *)
(* Version of 19 Aug 2020 *)
(* was: *)
(* Version of 18 Aug 2020 *)

(* Your name: Koo Zhengqun
   Your e-mail address: zhengqun.koo@u.nus.edu
   Your student number: A0164207L
*)

(* Your name: Bobbie Soedirgo
   Your e-mail address: sram-b@comp.nus.edu.sg
   Your student number: A0181001A
*)

(* Your name: Kuan Wei Heng
   Your e-mail address: kuanwh@u.nus.edu
   Your student number: A0121712X
*)

(* ********** *)

let rec infinite_self_composition s =
  fun v -> s (infinite_self_composition s) v;;

(* ********** *)

(* Exercise 8 *)

let test_fib candidate =
  (candidate 0 = 0) &&
  (candidate 1 = 1) &&
  (candidate 2 = 1) &&
  (candidate 3 = 2) &&
  (candidate 4 = 3) &&
  (candidate 5 = 5) &&
  (let n = Random.int 20
   in candidate n = (candidate (n - 1)) + (candidate (n - 2)))
  (* etc. *);;

let test_rev candidate =
  (candidate [] = []) &&
  (candidate [0] = [0]) &&
  (candidate [0; 1] = [1; 0]) &&
  (* The reverse of a reverse of a list is the list itself *)
  (let vs = [0; 1; 2; 3; 4; 5]
   in candidate (candidate vs) = vs)
  (* etc. *);;

let test_concat candidate =
  (candidate [] [] = []) &&
  (candidate [0] [] = [0]) &&
  (candidate [] [0] = [0]) &&
  (candidate [0; 1; 2] [3; 4; 5] = [0; 1; 2; 3; 4; 5])
  (* etc. *);;

(* As with the function `fac` from the lecture, applying `infinite_self_composition` on the inner function gives us the fixed-point of the inner function (let's call it `foo_oo`), defined as:
 *
 * foo_oo n = 0                                if n = 0,
 *          | 1                                if n = 1,
 *          | foo_oo (n - 1) + foo_oo (n - 2)  otherwise.
 *
 * This gives us the fibonacci function, as is evident when we unit-test `foo` with `test_fib`. *)
let foo n =
  assert (n >= 0);
  infinite_self_composition (fun foo n -> if n = 0 then 0 else if n = 1 then 1 else foo (n - 1) + foo (n - 2)) n;;

let () = assert (test_fib foo);;

(* Following the same steps, we get:
 *
 * bar_oo vs = []                if vs = []
 *           | bar_oo vs' @ [v]  otherwise.
 *
 * This gives us the reverse list function, as is evident when we unit-test `bar` with `test_rev`. *)
let bar vs =
  infinite_self_composition (fun bar vs -> match vs with | [] -> [] | v :: vs' -> bar vs' @ [v]) vs;;

let () = assert (test_rev bar);;

(* This is the same as bar, except at each step, we destructure `vs` and accumulate the reversed elements in `a`. *)
let baz vs =
  infinite_self_composition (fun baz vs a -> match vs with | [] -> a | v :: vs' -> baz vs' (v :: a)) vs [];;

let () = assert (test_rev baz);;

(* This one destructures `vs` at each step, prepending v to `yip vs' ws`. We end up with a concatenation of vw and ws, as evidenced using the unit-test `test_concat`. *)
let yip vs ws =
  infinite_self_composition (fun yip vs ws-> match vs with | [] -> ws | v :: vs' -> v :: yip vs' ws) vs ws;;

let () = assert (test_concat yip);;

(* This one isn't part of Exercise 8, but included just for fun. `bar` reverses a list with the `@` operator, `baz` does it without `@` but with an accumulator. This version does it with neither `@` nor an accumulator, but with `yip` which we just defined: *)
let quux vs =
  infinite_self_composition (fun quux vs -> match vs with | [] -> [] | v :: vs' -> yip (quux vs') [v]) vs;;

let () = assert (test_rev quux);;

(* ********** *)

(* end of week-01_fixpoints.ml *)
