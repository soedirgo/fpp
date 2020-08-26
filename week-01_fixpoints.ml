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
  (let vs = [0; 1; 2; 3; 4; 5]
   in candidate (candidate vs) = vs)
  (* etc. *);;

let test_concat candidate =
  (candidate [] [] = []) &&
  (candidate [0] [] = [0]) &&
  (candidate [] [0] = [0]) &&
  (candidate [0; 1; 2] [3; 4; 5] = [0; 1; 2; 3; 4; 5])
  (* etc. *);;

(* Fibonacci *)
let foo n =
  assert (n >= 0);
  infinite_self_composition (fun foo n -> if n = 0 then 0 else if n = 1 then 1 else foo (n - 1) + foo (n - 2)) n;;

let () = assert (test_fib foo);;

(* Reverse list *)
let bar vs =
  infinite_self_composition (fun bar vs -> match vs with | [] -> [] | v :: vs' -> bar vs' @ [v]) vs;;

let () = assert (test_rev bar);;

(* Reverse list, but using cons ("::") instead of the list concatenation operator ("@") *)
let baz vs =
  infinite_self_composition (fun baz vs a -> match vs with | [] -> a | v :: vs' -> baz vs' (v :: a)) vs [];;

let () = assert (test_rev baz);;

(* List concatenation *)
let yip vs ws =
  infinite_self_composition (fun yip vs ws-> match vs with | [] -> ws | v :: vs' -> v :: yip vs' ws) vs ws;;

let () = assert (test_concat yip);;

(* Bonus: Reverse list, but with yip *)
let quux vs =
  infinite_self_composition (fun quux vs -> match vs with | [] -> [] | v :: vs' -> quux (yip vs' [v])) vs;;

let () = assert (test_rev quux);;

(* ********** *)

(* end of week-01_fixpoints.ml *)
