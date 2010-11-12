theory Ex02
imports Main
begin

section {* Homework -- Power function and binary trees *}

fun pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"pow x 0 = 1" |
"pow x (Suc m) = x * pow x m"

lemma [simp]: "pow x (m + n) = pow x m * pow x n"
apply (induct m)
apply auto
done

theorem "pow x (m * n) = pow (pow x m) n"
apply (induct n)
apply auto
done

datatype tree = Tip | Node tree tree

fun count :: "tree \<Rightarrow> nat" where
"count Tip = 1" |
"count (Node l r) = 1 + count l + count r"

fun explode :: "nat \<Rightarrow> tree \<Rightarrow> tree" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

lemma "count (explode n t) = (count t + 1) * pow 2 n - 1"
apply (induct n arbitrary: t)
apply (auto simp add: algebra_simps)
done

end
