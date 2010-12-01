header "Homework Sheet 5 - Nikolaus Demmel"

theory Hw05
imports Big_Step
begin



section "Lemmas from tutorial"

lemma Semi_cong: "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> c1; c2 \<sim> c1'; c2'"
by auto

lemma If_cong: "\<lbrakk>\<And>s. bval b s = bval b' s; c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk>
   \<Longrightarrow> IF b THEN c1 ELSE c2 \<sim> IF b' THEN c1' ELSE c2'"
by auto

lemma While_cond: "\<lbrakk> (c1, s) \<Rightarrow> t; c1 = WHILE b DO c; \<And>s. bval b s = bval b' s; c \<sim> c' \<rbrakk>
  \<Longrightarrow> (WHILE b' DO c', s) \<Rightarrow> t"
by (induct c1 s t rule: big_step_induct) auto

lemma While_cong: "\<lbrakk> \<And>s. bval b s = bval b' s; c \<sim> c' \<rbrakk>
  \<Longrightarrow> WHILE b DO c \<sim> WHILE b' DO c'"
by (auto intro: While_cond)



section "Part (a)"

(* assigned for a program c and a variable x is true, iff x is (syntactically) assigned somewhere in c *)
fun assigned :: "com \<Rightarrow> name \<Rightarrow> bool" where
  "assigned SKIP x = False" |
  "assigned (y ::= e) x = (x = y)" |
  "assigned (c ; c') x = (assigned c x \<or> assigned c' x)" |
  "assigned (IF b THEN c ELSE c') x = (assigned c x \<or> assigned c' x)" |
  "assigned (WHILE b DO c) x = assigned c x"



section "Part (b)"

(* A variable can only ever change, if it is assigned *)
lemma not_assigned: "\<lbrakk> (c,s) \<Rightarrow> t ; \<not>assigned c x \<rbrakk> \<Longrightarrow> (s x) = (t x)"
by (induct c s t rule: big_step_induct) auto 



section "Part (c)"

(* Proven counterexample to the reverse of lemma not_assigned. *)
(* Assignment does not imply change of value *)
lemma "\<lbrakk> (c, s) \<Rightarrow> t ; c = (0 ::= (V 0)) \<rbrakk> \<Longrightarrow> s 0 = t 0 \<and> assigned c 0" by auto



section "Part (d)"

(* This is almost like the DO WHILE, just inverting the b *)
definition Repeat :: "com \<Rightarrow> bexp \<Rightarrow> com" ("REPEAT _ UNTIL _" [0, 61] 61) where
  "REPEAT c UNTIL b = c; WHILE Not b DO c" 

(* Naturally this is similar to trans1 *)
fun trans2 :: "com \<Rightarrow> com" where
  "trans2 SKIP = SKIP" |
  "trans2 (Assign x e) = Assign x e" |
  "trans2 (Semi c1 c2) = Semi (trans2 c1) (trans2 c2)" |
  "trans2 (If b c1 c2) = If b (trans2 c1) (trans2 c2)" |
  "trans2 (While b c) = IF b THEN REPEAT (trans2 c) UNTIL Not b ELSE SKIP"

(* Correctness of transformation trans2 *)
lemma "trans2 c \<sim> c"
proof (induct c)
  case (While b c)
  with While_cong 
  have "\<And>b. WHILE b DO (trans2 c) \<sim> WHILE b DO c" by blast
  with While.hyps While_cong Semi_cong
  have "trans2 c; WHILE (Not (Not b)) DO (trans2 c) \<sim> c; WHILE b DO c" by auto
  with Repeat_def If_cong show ?case by (auto simp add: unfold_while)
qed auto

end