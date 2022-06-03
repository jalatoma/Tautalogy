(* 

Jacynda Alatoma Project 1 CSCI 2041 
Due: November 1st, 2021

*)

type proposition = 
    False |
    True |
    Var of string |
    And of proposition * proposition |
    Or of proposition * proposition |
    Not of proposition |
    Imply of proposition * proposition |
    Equiv of proposition * proposition |
    If of proposition * proposition * proposition ;;

let rec ifify p =
    match p 
    with And(something, something2) -> If(ifify something, ifify something2, False) |
        Or(something, something2) -> If(ifify something, True, ifify something2) |
        Not(something) -> If(ifify something, False, True) |
        Imply(something, something2) -> If(ifify something, ifify something2, True) |
        Equiv(something, something2) -> If(ifify something, ifify something2, (If (ifify something2, False, True))) |
        _ -> p ;; 


let rec normalize c = 
    match c
    with If(If(something, something2, something3), something4, something5) -> normalize (If(something, 
        (If(something2, something4, something5)),(If(something3, something4, something5)))) |
        If(something, something2, something3) -> If(normalize something, normalize something2, normalize something3) |
        _ -> c ;;

let rec substitute c v b = 
  match c 
  with Var name ->
    if Var name = v
      then b
    else Var name |
    If(something, something2, something3) ->
    If(substitute something v b, substitute something2 v b, substitute something3 v b) |
    _ -> c;;

let rec simplify c =
  match c
  with  If(True, something, something2) -> simplify something |
        If(False, something, something2) -> simplify something2 |
        If(something, True, False) -> simplify something |
        If(something, something2, something3) ->
          if something2 = something3
          then simplify something2
          else
          (* I tried to do with a case for False but did not work, works with just a True case for me (I think) *)
          simplify (substitute c something True) |
        _ -> c ;;

let tautology p = 
  simplify (normalize (ifify p)) = True ;;

(* Test cases and output for ifify (to show that function alone works): 
let test = ifify(Var"a") ;;
let test2 = ifify(Not(Var"a")) ;;
let test3 = ifify(And(Var"a", Var"b")) ;;
let test4 = ifify(Or(Var"a", Var"b")) ;;
let test5 = ifify(And(Not(Var"a"), Var"b")) ;;
let test6 = ifify(Equiv(Var"a", Var"b")) ;;
let test7 = ifify(Imply(Not(And(Var"p", Var"q")), Or(Not(Var"p"), Not(Var"q")))) ;;

Results for ifify: 
val test : proposition = Var "a"
val test2 : proposition = If (Var "a", False, True)
val test3 : proposition = If (Var "a", Var "b", False)
val test4 : proposition = If (Var "a", True, Var "b")
val test5 : proposition = If (If (Var "a", False, True), Var "b", False)
val test6 : proposition = If (Var "a", Var "b", If (Var "b", False, True))
val test7 : proposition =
  If (If (If (Var "p", Var "q", False), False, True),
   If (If (Var "p", False, True), True, If (Var "q", False, True)), True) 

Tests and Output for normalize (to show function alone works) : 
let test8 = ifify(Imply(Not(And(Var"p", Var"q")), Or(Not(Var"p"), Not(Var"q")))) ;;
let norm = normalize test8 ;; 

Results for normalize: 
val norm : proposition =
  If (Var "p",
   If (Var "q",
    If (False,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True),
    If (True,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True)),
   If (False,
    If (False,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True),
    If (True,
     If (Var "p", If (False, True, If (Var "q", False, True)),
      If (True, True, If (Var "q", False, True))),
     True))) 


Tests and output for simplify (to show function alone works):
let test9 = ifify(Imply(Var"p", Var"q"));;
let norm = normalize test9 ;;
let simp = simplify norm ;; 

let test10 = ifify (Or(Or(Var"p", Var"q"), Not(Var"p"))) ;;
let norm2 = normalize test10 ;;
let simp2 = simplify norm2 ;; 

let test11 = ifify(And(Not(Var"a"), Var"b")) ;;
let norm3 = normalize test11 ;;
let simp3 = simplify norm3 ;; 

Results for simplify and substitute (to show that they work) :
val simp : proposition = Var "q"
val simp2 : proposition = True
val simp3 : proposition = False *)


(*Tests and ouput for tautology - found these examples online:
(*Should be false*)
let taut = tautology(And(Not(Var"a"), Var"b")) ;; 
(*Should be true*)
let taut2 = tautology(Imply(Not(And(Var"p", Var"q")), Or(Not(Var"p"), Not(Var"q")))) ;; 
(*Should be false*)
let taut3 = tautology(Imply(Var"p", Var"q"));;
(*Should be false*)
let taut4 = tautology(Not(Var"p")) ;;
(*Should be true*)
let taut5 = tautology(Or(Or(Var"p", Var"q"), Not(Var"p"))) ;;  *)

(* Output for tautology:
val taut : bool = false
val taut2 : bool = true
val taut3 : bool = false
val taut4 : bool = false
val taut5 : bool = true
*)
