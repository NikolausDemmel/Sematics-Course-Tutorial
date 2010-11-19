header "Homework Sheet 3"

theory Hw03 
imports AExp 
begin


(* Like aexp from the lecture, but additional constructor Let *)
datatype lexp = N nat | V name | Plus lexp lexp | Let name lexp lexp


subsection "Part (a)"

(* Straight forward semantics. Use function update like suggested in the hint. *)
fun lval :: "lexp => state => nat" where
"lval (N n) _ = n" |
"lval (V v) s = s v" |
"lval (Plus e1 e2) s = lval e1 s + lval e2 s" |
"lval (Let v vexp subexp) s = lval subexp (s(v := lval vexp s))"

(* Should yield 6 *)
value "lval (Plus (V 0) (Let 0 (N 3) (Plus (V 0) (V 1)))) (nth [1, 2])"


subsection "Part (b)"

(* Substitute all occurences of a variable x in an expression with e *)
fun subst_var :: "name => aexp => aexp => aexp" where
"subst_var _ (aexp.N n) _ = (aexp.N n)" |
"subst_var x (aexp.V v) e = (if v = x then e else aexp.V v)" |
"subst_var x (aexp.Plus e1 e2) e = aexp.Plus (subst_var x e1 e) (subst_var x e2 e)"

(* subst_var is an alternative to updating the state. *)
lemma subst_var: "aval (subst_var v subexp e) st = aval subexp (st(v := aval e st))"
apply (induct subexp)
apply auto
done

(* Transform an lexp into an equivalent aexp (without lets). *)
fun lexp2aexp :: "lexp => aexp" where
"lexp2aexp (N n) = (aexp.N n)" |
"lexp2aexp (V v) = (aexp.V v)" |
"lexp2aexp (Plus e1 e2) = (aexp.Plus (lexp2aexp e1) (lexp2aexp e2))" |
"lexp2aexp (Let v vexp subexp) = subst_var v (lexp2aexp subexp) (lexp2aexp vexp)"

(* Should be (aexp.N 1) *)
value "lexp2aexp (Let 0 (N 1) (V 0))"

(* Translation to let free expression preserves semantics. *)
theorem "aval (lexp2aexp e) st = lval e st"
apply (induct e arbitrary: st)
apply (auto simp add: subst_var)
done


subsection "Part (c)"

(* Returns True is a variable is free in a given expression *)
fun is_free :: "name => lexp => bool" where
"is_free _ (N n) = True" |
"is_free v (V x) = (v = x)" |
"is_free v (Plus e1 e2) = (is_free v e1 | is_free v e2)" |
"is_free v (Let x e1 e2) = (is_free v e1 | ((~ v = x) & is_free v e2))"

(* Updating non-free variabels in the state does never change the outcome. *)
(* I found it was essential to use the ==> implication instead of -->,
   otherwise simp (called by auto) would hang on the 3rd subgoal. *) 
lemma not_free_vars: "~ is_free x e ==> (lval e st = lval e (st(x := n)))" 
apply (induct e arbitrary: st) 
apply auto 
apply (metis fun_upd_twist fun_upd_upd)
done

(* Optimization depending on the freeness of variables *)
fun lsimp :: "lexp => lexp" where
"lsimp (N n) = (N n)" |
"lsimp (V v) = (V v)" |
"lsimp (Plus e1 e2) = Plus (lsimp e1) (lsimp e2)" |
"lsimp (Let x e1 e2) = (if is_free x e2 then (Let x (lsimp e1) (lsimp e2)) else (lsimp e2))"

(* With our lemma it is now simple to prove, that the optimization is correct *)
theorem "lval (lsimp e) st = lval e st"
apply (induct e arbitrary: st)
apply (auto simp add: not_free_vars)
done

end