theory Dependency
imports "../../Semantics/Big_Step" "../../Semantics/Vars"
begin


text {* From Homework 5 *}
primrec assigned :: "com \<Rightarrow> name \<Rightarrow> bool" where
  "assigned SKIP x \<longleftrightarrow> False"
| "assigned (x ::= a) y \<longleftrightarrow> (x = y)"
| "assigned (c1; c2) x \<longleftrightarrow> assigned c1 x \<or> assigned c2 x"
| "assigned (IF b THEN c1 ELSE c2) x \<longleftrightarrow> assigned c1 x \<or> assigned c2 x"
| "assigned (WHILE b DO c) x \<longleftrightarrow> assigned c x"

lemma unassigned_implies_equal:
  "\<lbrakk> (c, s) \<Rightarrow> t; \<not> assigned c x \<rbrakk> \<Longrightarrow> s x = t x"
by (induct c s t rule: big_step_induct) auto


text {* The dependency relation *}

inductive influences :: "name \<Rightarrow> com \<Rightarrow> name \<Rightarrow> bool"
where
  Skip[intro]: "influences v SKIP v"
| Seq[intro]: 
  "\<lbrakk>influences x c1 y; influences y c2 z\<rbrakk>
   \<Longrightarrow> influences x (c1 ; c2) z"
| Assign_same[intro]: 
  "x \<in> vars a \<Longrightarrow> influences x (z ::= a) z"
| Assign_other[intro]: 
  "x \<noteq> z \<Longrightarrow> influences z (x ::= a) z"
| If1[intro]:
  "influences x c1 y
   \<Longrightarrow> influences x (IF b THEN c1 ELSE c2) y"
| If2[intro]:
  "influences x c2 y
   \<Longrightarrow> influences x (IF b THEN c1 ELSE c2) y"
| If_assigned[intro]:
  "\<lbrakk> assigned c1 y \<or> assigned c2 y; x \<in> vars b \<rbrakk>
   \<Longrightarrow> influences x (IF b THEN c1 ELSE c2) y"
| While1[intro]:
  "influences x (WHILE b DO c) x"
| While2:
  "\<lbrakk> influences x c y; influences y (WHILE b DO c) z\<rbrakk>
   \<Longrightarrow> influences x (WHILE b DO c) z"
| While_assigned[intro]:
  "\<lbrakk> assigned c y; x \<in> vars b \<rbrakk>
   \<Longrightarrow> influences x (WHILE b DO c) y"


text {* All dependencies of a variable *}
abbreviation deps :: "com \<Rightarrow> name \<Rightarrow> name set" where
"deps c x == {y. influences y c x}"


text {* A simple lemma that is useful later *}

lemma deps_unassigned_keep:
  "\<not> assigned c x \<Longrightarrow> x \<in> deps c x"
oops

text {* Main theorem *}

lemma deps_sound:
  "\<lbrakk> (c, s) \<Rightarrow> t; s = s' on deps c x; (c, s') \<Rightarrow> t' \<rbrakk>
   \<Longrightarrow> t x = t' x"
oops


end
