theory Ex05_Template
imports Big_Step
begin
(*>*)

section {* Ex. 5.1 *}

(* prove or disprove *)
lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
oops

(* prove or disprove *)
lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
oops

(* prove or disprove *)
lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO c; WHILE And b1 b2 DO c"
oops

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "Or b1 b2 = Not (And (Not b1) (Not b2))"

(* prove or disprove *)
lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c; WHILE b1 DO c"
oops



section {* Ex. 5.2 *}

lemma Semi_cong: "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> c1; c2 \<sim> c1'; c2'"
oops

lemma If_cong: "\<lbrakk>\<And>s. bval b s = bval b' s; c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk>
   \<Longrightarrow> IF b THEN c1 ELSE c2 \<sim> IF b' THEN c1' ELSE c2'"
oops

lemma While_cong: "\<lbrakk> \<And>s. bval b s = bval b' s; c \<sim> c' \<rbrakk>
  \<Longrightarrow> WHILE b DO c \<sim> WHILE b' DO c'"
oops

definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
  "DO c WHILE b = SKIP" (* add real definition here! *)

fun trans1 :: "com \<Rightarrow> com" where
  "trans1 c = SKIP" (* add real definition here! *)

lemma "trans1 c \<sim> c"
oops


end
(*>*)
