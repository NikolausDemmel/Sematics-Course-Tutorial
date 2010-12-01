theory Ex05_Solution1
imports Big_Step
begin
(*>*)

section {* Ex. 5.1 *}

(* prove or disprove *)
lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
  (is "?i \<sim> ?ii")
proof -  (* sledgehammer also proves this, but here is a detailed proof *)
  {
    fix s t
    assume "(?i, s) \<Rightarrow> t"
    moreover
    {
      assume "bval b1 s \<and> bval b2 s"
      hence "bval (And b1 b2) s" by simp
    }
    moreover
    {
      assume "\<not>bval b1 s \<or> \<not>bval b2 s"
      hence "\<not>bval (And b1 b2) s" by simp
    }
    ultimately
    have "(?ii, s) \<Rightarrow> t" by blast
  }
  then show ?thesis by auto (* the other direction is automatic *)
qed

(* prove or disprove *)
lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
oops (* not equivalent:  b1 = B True, b2 = B False *)


(* prove or disprove *)
lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO c; WHILE And b1 b2 DO c"
oops (* not equivalent:  b1 = B True, b2 = B False *)

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "Or b1 b2 = Not (And (Not b1) (Not b2))"

text {* At the end of a loop the condition is always false *}

lemma While_end: "(WHILE b DO c, s) \<Rightarrow> t \<Longrightarrow> \<not>bval b t"
proof -
  assume "(WHILE b DO c, s) \<Rightarrow> t"
  then obtain c' where "(c', s) \<Rightarrow> t" and "c' = WHILE b DO c" by blast
  then show "\<not>bval b t"
    by (induct c' s t rule: big_step_induct) auto
qed

(* prove or disprove *)
lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c; WHILE b1 DO c"
proof -
  {
    fix s
    assume "\<not>bval (Or b1 b2) s"
    hence "\<not>bval b1 s" by (auto simp add: Or_def)
  }
  then show ?thesis by (blast intro!: While_end)
qed



section {* Ex. 5.2 *}

lemma Semi_cong: "\<lbrakk> c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk> \<Longrightarrow> c1; c2 \<sim> c1'; c2'"
by blast

lemma If_cong: "\<lbrakk>\<And>s. bval b s = bval b' s; c1 \<sim> c1'; c2 \<sim> c2' \<rbrakk>
   \<Longrightarrow> IF b THEN c1 ELSE c2 \<sim> IF b' THEN c1' ELSE c2'"
by blast

(* auxiliary lemma *)
lemma While_cond:
  "\<lbrakk> (c1, s) \<Rightarrow> t; c1 = WHILE b DO c; \<And>s. bval b s = bval b' s; c \<sim> c' \<rbrakk>
   \<Longrightarrow> (WHILE b' DO c', s) \<Rightarrow> t"
by (induct c1 s t rule: big_step_induct) auto (*>*)

lemma While_cong: "\<lbrakk> \<And>s. bval b s = bval b' s; c \<sim> c' \<rbrakk>
  \<Longrightarrow> WHILE b DO c \<sim> WHILE b' DO c'"
by (auto intro: While_cond)


definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
   "DO c WHILE b = c; WHILE b DO c"

fun trans1 :: "com \<Rightarrow> com" where
  "trans1 SKIP = SKIP"
| "trans1 (x ::= a) = x ::= a"
| "trans1 (c1; c2) = trans1 c1; trans1 c2"
| "trans1 (IF b THEN c1 ELSE c2) = IF b THEN trans1 c1 ELSE trans1 c2"
| "trans1 (WHILE b DO c) = IF b THEN (DO trans1 c WHILE b) ELSE SKIP"

lemma "trans1 c \<sim> c"
proof (induct c)
  case (While b c)
  have "WHILE b DO trans1 c \<sim> WHILE b DO c"
    by (rule While_cong) (simp_all add: While.hyps)
  with While
  have "trans1 c; WHILE b DO trans1 c \<sim> c; WHILE b DO c"
    by (blast intro: While)
  then show ?case
    by (auto simp add: Do_def unfold_while)
qed auto


end
(*>*)
