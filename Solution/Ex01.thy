theory Ex01
imports Main
begin

section {* Exercise 1 -- Calculating with natural numbers *}

value "2 + (2::nat)"  -- {* 4 *}
value "(2::nat) * (5 + 3)"  -- {* 16 *}
value "(3::nat) * 4 - 2 * (7 + 1)"  -- {* 0 *}

text {*
The last result is 0, because natural numbers are nonnegative
and by convention natural subtraction yields 0 for undefined
results (more precisely: the logic is total and natural
subtraction must be defined for all arguments).
*}


section {* Exercise 2 -- Natural number laws *}

lemma "x + y = y + (x::nat)"
apply auto
done

lemma "x + (y + z) = (x + y) + (z::nat)"
apply auto
done


section {* Exercise 3 -- Counting elements of a list *}

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] _ = 0" |
"count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"

value "count [] (3::nat)"  -- {* 0 *}
value "count [3, 2] (3::nat)"  -- {* Suc 0 (equals 1) *}
value "count [3, 3] (3::nat)"  -- {* 2 *}

theorem "count xs x \<le> length xs"
apply (induct xs)
apply auto
done


section {* Exercise 4 -- Adding elements to the end of a list *}

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

value "snoc [] c"  -- {* [c] *}

lemma "snoc [] c = [c]"
apply auto
done

lemma[simp]: "snoc xs x = xs @ [x]"
apply (induct xs)
apply auto
done

theorem "rev (x # xs) = snoc (rev xs) x"
apply (induct xs)
apply auto
done


section {* Exercise 5 -- Tree traversal *}

datatype 'a tree = Tip "'a" | Node "'a tree" "'a" "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror (Tip x) = Tip x" |
"mirror (Node l x r) = Node (mirror r) x (mirror l)"

fun pre_order :: "'a tree \<Rightarrow> 'a list" where
"pre_order (Tip x) = [x]" |
"pre_order (Node l x r) = x # pre_order l @ pre_order r"

fun post_order :: "'a tree \<Rightarrow> 'a list" where
"post_order (Tip x) = [x]" |
"post_order (Node l x r) = snoc (post_order l @ post_order r) x"

theorem "pre_order (mirror t) = rev (post_order t)"
apply (induct t)
apply auto
done


section {* Homework -- Leaves of a tree *}

datatype ntree = Leaf nat | Branch ntree ntree

fun leaves :: "ntree \<Rightarrow> nat list" where
"leaves (Leaf x) = [x]" |
"leaves (Branch l r) = leaves l @ leaves r"

fun leaf_count :: "ntree \<Rightarrow> nat" where
"leaf_count (Leaf _) = 1" |
"leaf_count (Branch l r) = leaf_count l + leaf_count r"

theorem "length (leaves t) = leaf_count t"
apply (induct t)
apply auto
done

fun treesum :: "ntree \<Rightarrow> nat" where
"treesum (Leaf x) = x" |
"treesum (Branch l r) = treesum l + treesum r"

lemma "listsum (leaves t) = treesum t"
apply (induct t)
apply auto
done


end
