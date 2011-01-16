(* Author: Tobias Nipkow *)

theory Util imports Main
begin

subsection "From functions to lists"

value "[0 ..< 3]"

value "map f [0 ..< 3]"

definition list :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
"list s n = map s [0 ..< n]"

value "list f 3"

end
