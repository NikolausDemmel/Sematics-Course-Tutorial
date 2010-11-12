theory Hw1
imports Main
begin

(* No value for "empty tree" with the following definition, but we don't mind. *)
datatype ntree = Leaf nat | Node "ntree" "ntree"

fun leaves :: "ntree => nat list" where
"leaves (Leaf x) = [x]" |
"leaves (Node t1 t2) = leaves t1 @ leaves t2"

fun leaf_count :: "ntree => nat" where
"leaf_count (Leaf x) = 1" |
"leaf_count (Node t1 t2) = leaf_count t1 + leaf_count t2"

theorem "length (leaves t) = leaf_count t"
apply(induct t)
apply(auto)
done

fun treesum :: "ntree => nat" where
"treesum (Leaf x) = x" |
"treesum (Node t1 t2) = treesum t1 + treesum t2"

lemma "listsum (leaves t) = treesum t"
apply(induct t)
apply(auto)
done

end