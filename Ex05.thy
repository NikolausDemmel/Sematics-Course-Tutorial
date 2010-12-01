theory Ex05
imports Big_Step
begin
(*>*)

section {* Ex. 5.1 *}

(* prove or disprove *)
lemma "IF And b1 b2 THEN c1 ELSE c2 \<sim> IF b1 THEN IF b2 THEN c1 ELSE c2 ELSE c2"
by (metis IfE IfFalse IfTrue bval.simps(3))

(* prove or disprove *)
lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c"
oops

(* counterexample:
  b1 = Less (V 0) (N 1)
  b2 = Less (V 1) (N 1)
  c = IF b1 THEN 0 ::= (N 1) ELSE 1 ::= (N 1) 
  s = [0, 0]
*)

abbreviation "w1 b1 b2 c s t \<equiv> exec (WHILE And b1 b2 DO c) s t"
abbreviation "w2 b1 b2 c s t \<equiv> exec (WHILE b1 DO WHILE b2 DO c) s t"

values "{t. w1 (Less (V 0) (N 1)) (Less (V 1) (N 1)) (IF (Less (V 0) (N 1)) THEN 0 ::= (N 1) ELSE 1 ::= (N 1)) [0,0] t }"
values "{t. w2 (Less (V 0) (N 1)) (Less (V 1) (N 1)) (IF (Less (V 0) (N 1)) THEN 0 ::= (N 1) ELSE 1 ::= (N 1)) [0,0] t }"

(* attempt to be able to formally proof couterexamples


lemma "(exec c l l') = ((c, nth l) \<Rightarrow> nth l')"
proof
  assume "(c, nth l) \<Rightarrow> nth l'"
  thus "exec c l l'"
    sledgehammer [full_types]


lemma "\<not> (\<forall> b1 b2 c. WHILE And b1 b2 DO c \<sim> WHILE b1 DO WHILE b2 DO c)"
proof (rule notI, elim allE)
  let ?b1 = "Less (V 0) (N 1)"
  let ?b2 = "Less (V 1) (N 1)"
  let ?c = "IF ?b1 THEN 0 ::= (N 1) ELSE 1 ::= (N 1)" 
  let ?s = "nth [0, 0]"
  let ?t1 = "nth [1, 0]"
  let ?t2 = "nth [1, 1]"
  assume "(WHILE And ?b1 ?b2 DO ?c, ?s) \<Rightarrow> t =
          (WHILE ?b1 DO WHILE ?b2 DO ?c, ?s) \<Rightarrow> t"
  hence "False"
    proof - 
      have "(WHILE And ?b1 ?b2 DO ?c, ?s) \<Rightarrow> ?t1"

. *)

(* prove or disprove *)
lemma "WHILE And b1 b2 DO c \<sim> WHILE b1 DO c; WHILE And b1 b2 DO c"
oops

(* counterexample:
   b1 = (Less (V 0) (N 1)
   b2 = (B False)
   c = (0 :: (N 1))
   s = [0]
*)

abbreviation "w3 b1 b2 c s t \<equiv> exec (WHILE b1 DO c; WHILE And b1 b2 DO c) s t"

values "{t. w1 (Less (V 0) (N 1)) (B False) (0 ::= (N 1)) [0] t}"
values "{t. w3 (Less (V 0) (N 1)) (B False) (0 ::= (N 1)) [0] t}"
 

definition Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
  "Or b1 b2 = Not (And (Not b1) (Not b2))"

(* prove or disprove *)

(* This is porvable. 

TODO complete the proofs

lemma not_or: "\<not>bval (Or b1 b2) s \<Longrightarrow> \<not>bval b1 s"
by (metis Or_def bval.simps)

lemma "\<lbrakk> (WHILE b DO c, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> \<not> bval b t"
apply (induct rule: big_step.induct)
apply (auto)

apply blast



lemma while_or: "\<lbrakk> (WHILE Or b1 b2 DO c, s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> \<not>bval b1 t"
proof -
  assume 0: "(WHILE Or b1 b2 DO c, s) \<Rightarrow> t"
  { assume 1: "\<not> bval (Or b1 b2) s"
    with 0 have "s = t" by blast
    with 1 have "\<not> bval b1 t" by (simp add: not_or) (* huh? *)
  }
  moreover
  {
    assume 1: "bval (Or b1 b2) s"
    
lemma "WHILE Or b1 b2 DO c \<sim> WHILE Or b1 b2 DO c; WHILE b1 DO c"

proof -
  { fix s t
    assume 0: "(WHILE Or b1 b2 DO c, s) \<Rightarrow> t"
    then have "bval b1 t = False" by (simp add: while_or)
    then have "(WHILE b1 DO c, t) \<Rightarrow> t" by blast
    with 0 have "(WHILE Or b1 b2 DO c; WHILE b1 DO c, s) \<Rightarrow> t" by blast
  }
  moreover
  { fix s t
    assume 1: "(WHILE Or b1 b2 DO c; WHILE b1 DO c, s) \<Rightarrow> t"
    then obtain s' where 2: "(WHILE Or b1 b2 DO c, s) \<Rightarrow> s' \<and> (WHILE b1 DO c, s') \<Rightarrow> t" by blast
    then have "bval b1 s' = False" by (fastsimp simp: while_or)
    with 1 2 have "s' = t" by blast
    with 2 have "(WHILE Or b1 b2 DO c, s) \<Rightarrow> t" by blast
  }
  ultimately show ?thesis by blast
qed

.
oops
*)


section {* Ex. 5.2 *}

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

definition Do :: "com \<Rightarrow> bexp \<Rightarrow> com" ("DO _ WHILE _"  [0, 61] 61) where
  "DO c WHILE b = c; WHILE b DO c"

fun trans1 :: "com \<Rightarrow> com" where
  "trans1 SKIP = SKIP"
| "trans1 (Assign x e) = Assign x e"
| "trans1 (Semi c1 c2) = Semi (trans1 c1) (trans1 c2)"
| "trans1 (If b c1 c2) = If b (trans1 c1) (trans1 c2)"
| "trans1 (WHILE b DO c) = IF b THEN (DO (trans1 c) WHILE b) ELSE SKIP"

lemma "trans1 c \<sim> c"
proof (induct c)
  case (While b c')
  with While_cong have "WHILE b DO (trans1 c') \<sim> WHILE b DO c'" by auto
  with While have "c'; (WHILE b DO c') \<sim> (trans1 c'); WHILE b DO (trans1 c')" by auto
  thus ?case by (auto simp add: Do_def unfold_while)
qed auto

end
(*>*)
