header "Homework Sheet 3"

theory Hw03 imports AExp begin

datatype lexp = N nat | V name | Plus lexp lexp | Let name lexp lexp

subsection "(a)"

fun lval :: "lexp => state => nat" where
"lval (N n) _ = n" |
"lval (V v) s = s v" |
"lval (Plus e1 e2) s = lval e1 s + lval e2 s" |
"lval (Let v e1 e2) s = lval e2 (s(v := lval e1 s))"

value "lval (Plus (V 1) (Let 0 (N 3) (Plus (V 0) (V 1)))) (nth [1, 2])" 

(* Substitute all occurences of variable v in e2 with expression e1 *)
fun subst_var v e1 e2 :: "name => aexp => aexp" where


fun lval2aval :: "lexp => aexp" where
"lval2aval (N n) = (aexp.N n)" |
"lval2aval (V v) = (aexp.V v)" |
"lval2aval (Plus e1 e2) = (aexp.Plus (lval2aval e1) (lval2aval e2))" |
"lval2aval (Let v e1 e2) = subst_var v (lval2aval e1) (lval2aval e2)"

end