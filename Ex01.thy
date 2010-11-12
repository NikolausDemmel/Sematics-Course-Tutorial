theory Ex01
imports Main
begin

(* 1.1 *)
value "2 + (2::nat)"
value "(2::nat) * (5 + 3)"
value "(3::nat) * 4 - 2 * (7 + 1)"

(* 1.2 *)
lemma com: "(x::nat) + y = y + x"
apply(auto)
done

lemma assoc:
fixes a::nat
shows "(a + b) + c = a + (b + c)"
apply(simp)
done


(* 1.3 *)
fun count :: "'a list => 'a => nat" where 
"count [] a = 0" |
"count (x#xs) a = count xs a + (if x = a then 1 else 0)"

value "count [] x"
value "count [1, 2, 3] (2::nat)"
value "count [0, 0, 1, 2, 0] (0::nat)"

lemma "count [0, 0, 1, 2, 0] (0::nat) = 3"
apply(auto)
done

theorem count_le_lenght: "count xs x <= length xs"
apply(induct xs)
apply(auto)
done

(* 1.4 *)

fun snoc :: "'a list => 'a => 'a list" where
"snoc [] a = [a]" |
"snoc (x#xs) a = x#(snoc xs a)"

value "snoc [] c"

lemma "snoc [] c = [c]"
apply auto
done

lemma snoc_append: "snoc (xs) a = xs @ [a]"
apply(induct xs)
apply(auto)
done

theorem "rev (x # xs) = snoc (rev xs) x"
apply(induct xs)
apply(auto simp add: snoc_append)
done

(* 1.5 *)

datatype 'a tree = Leaf 'a | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree => 'a tree" where
"mirror (Leaf x) = Leaf x" |
"mirror (Node t1 x t2) = Node (mirror t2) x (mirror t1)"

fun pre_order :: "'a tree => 'a list" where
"pre_order (Leaf x) = [x]" |
"pre_order (Node t1 x t2) = x # (pre_order t1) @ (pre_order t2)"

fun post_order :: "'a tree => 'a list" where
"post_order (Leaf x) = [x]" |
"post_order (Node t1 x t2) = (post_order t1) @ (post_order t2) @ [x]"

theorem "pre_order (mirror t) = rev (post_order t)"
apply(induct t)
apply auto
done

end