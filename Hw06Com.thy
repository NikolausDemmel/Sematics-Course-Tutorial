(* Modified for Homework 06 *)

header "IMP --- A Simple Imperative Language"

theory Hw06Com imports BExp begin

datatype
  com = SKIP 
      | Assign name aexp         ("_ ::= _" [1000, 61] 61)
      | Semi   com  com          ("_; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)

end
