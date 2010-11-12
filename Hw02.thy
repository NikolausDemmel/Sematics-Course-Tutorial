theory Hw02
imports Main
begin

fun pow :: "nat => nat => nat" where
"pow n 0 = 1" |
"pow n m = n * (pow n (m - 1))"

(* testing *)
value "pow 3 2"
value "pow 4 0"
value "pow 2 10"

lemma pow_plus: "pow x (m+n) = pow x m * pow x n"
apply(induct m)
apply(auto)
done

theorem pow_pow: "pow x (m*n) = pow (pow x m) n"
apply(induct n)
apply(auto simp add: pow_plus)
done

datatype tree = Leaf | Node tree tree

fun count :: "tree => nat" where
"count Leaf = 1" |
"count (Node a b) = 1 + count a + count b"

fun explode :: "nat => tree => tree" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"


(* Some testing: *)

fun foo :: "tree => nat => nat" where
"foo t n = count (explode n t)"

value "map (foo (Node Leaf (explode 1 (Node Leaf Leaf)))) [0,1,2,3,4,5,6,7,8,9,10]"

fun bar :: "nat => nat => nat" where
"bar a n = (1+a) * pow 2 n - 1"

value "map (bar 9) [0,1,2,3,4,5,6,7,8,9,10]"


(* recursive relationship. I think this is not needed for the homework but i did it anyway :-)  *)
lemma count_explode: "count (explode (n+1) t) = 2*(count (explode n t)) + 1"
apply(induct n t rule: explode.induct)
apply(auto)
done

(* direct formula. I think this is what the exercise asks for *)
theorem count_explode_pow: "count (explode n t) = (1 + count t) * pow 2 n - 1"
apply(induct n t rule: explode.induct)
apply(auto simp add: algebra_simps)
done

end