header "Exercises Sheet 3"

theory Ex03 
imports BExp
begin



subsection "Exercise 3.1"

(* Compared to "bexp" we have no And and Not, but an If instead. *)
datatype ifexp = B bool | If ifexp ifexp ifexp | Less aexp aexp

(* We define the intuitive semantics *)
fun ifval :: "ifexp => state => bool" where
"ifval (B b) _ = b" |
"ifval (If cond e1 e2) st = 
  (if ifval cond st then 
    ifval e1 st else 
    ifval e2 st)" |
"ifval (Less e1 e2) st = (aval e1 st < aval e2 st)"

(* Purely for readability: *)
abbreviation "or a b == Not (And (Not a) (Not b))" 

(* Express an if statement in terms of OR, AND and NOT. *)
fun translate :: "ifexp => bexp" where
"translate (B b) = bexp.B b" |
"translate (If cond e1 e2) = or (And (translate cond) (translate e1)) 
                                (And (Not (translate cond)) (translate e2))" |
"translate (Less a1 a2) = bexp.Less a1 a2"

(* translate does not change semantics of a program. Proof is simple enough. *)
theorem "bval (translate exp) st = ifval exp st"
apply (induct exp)
apply (auto)
done



subsection "Exercise 3.2"

(* Added the minus for natural numbers *)
datatype aexp = N nat | V name | Plus aexp aexp | Minus aexp aexp

fun aval :: "aexp => state => nat" where
"aval (N n) _ = n" |
"aval (V x) st = st x" |
"aval (Plus e1 e2) st = aval e1 st + aval e2 st" |
"aval (Minus e1 e2) st = aval e1 st - aval e2 st"

(* Straight forward extension for the minus *)
fun asimp_const :: "aexp => aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) =
  (case (asimp_const e1, asimp_const e2) of
    (N n1, N n2) => N(n1+n2) |
    (e1',e2') => Plus e1' e2')" |
"asimp_const (Minus e1 e2) =
  (case (asimp_const e1, asimp_const e2) of
    (N n1, N n2) => N(n1-n2) |
    (e1',e2') => Minus e1' e2')"

(* Proof does not change *)
theorem aval_asimp_const[simp]:
  "aval (asimp_const a) st = aval a st"
apply(induct a)
apply (auto split: aexp.split)
done

fun plus :: "aexp => aexp => aexp" where
"plus (N 0) e = e" |
"plus e (N 0) = e" |
"plus (N n1) (N n2) = N(n1+n2)" |
"plus e1 e2 = Plus e1 e2"

(* Do the same thing as with plus *)
fun minus :: "aexp => aexp => aexp" where
"minus (N 0) e = (N 0)" |
"minus e (N 0) = e" |
"minus (N n1) (N n2) = N(n1-n2)" |
"minus e1 e2 = Minus e1 e2"

lemma aval_plus[simp]:
  "aval (plus e1 e2) st = aval e1 st + aval e2 st"
apply(induct e1 e2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

(* Like aval_plus *)
lemma aval_minus[simp]:
  "aval (minus e1 e2) st = aval e1 st - aval e2 st"
apply (induct e1 e2 rule: minus.induct)
apply auto
done

(* Again, just added the minus in straightforward way. *)
fun asimp :: "aexp => aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus e1 e2) = plus (asimp e1) (asimp e2)" |
"asimp (Minus e1 e2) = minus (asimp e1) (asimp e2)"

(* This proof does not change either *)
theorem aval_simp_const0[simp]:
  "aval (asimp a) st = aval a st"
apply(induct a)
apply simp_all
done


end