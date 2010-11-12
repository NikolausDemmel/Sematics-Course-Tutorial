theory Hw2
imports Main
begin

fun pow :: "nat => nat => nat" where
"pow n 0 = 1" |
"pow n m = n * (pow n (m - 1))"

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

theorem count_explode_pow: "count (explode n t) = (1 + count t) * pow 2 n - 1"
apply(induct n t rule: explode.induct)
apply(auto simp add: algebra_simps)
done

end