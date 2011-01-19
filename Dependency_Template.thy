theory Dependency_Template
imports Big_Step Vars
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
  Skip:       "influences x SKIP x" |
  AssignEq:   "y \<in> (vars a) \<Longrightarrow> influences y (x ::= a) x" |
  AssignNeq:  "y \<noteq> x \<Longrightarrow> influences y (x ::= a) y" |
  Semi:       "\<lbrakk> influences y c1 z; influences z c2 x \<rbrakk> \<Longrightarrow> influences y (c1; c2) x" |
  IfThen:     "influences y c1 x \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  IfElse:     "influences y c2 x \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  IfCondThen: "\<lbrakk> y \<in> vars b; assigned c1 x \<rbrakk> \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  IfCondElse: "\<lbrakk> y \<in> vars b; assigned c2 x \<rbrakk> \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  WhileSkip:  "influences x (WHILE b DO c) x" |
  WhileCond:  "\<lbrakk> y \<in> vars b; assigned c x \<rbrakk> \<Longrightarrow> influences y (WHILE b DO c) x" |
  WhileStep:  "\<lbrakk> influences y c x \<rbrakk> \<Longrightarrow> influences y (WHILE b DO c) x" |
  WhileTrans: "\<lbrakk> influences y (WHILE b DO c) z; influences z c x \<rbrakk> 
               \<Longrightarrow> influences y (WHILE b DO c) x" (* this rule might cause trouble *)

(* Is there a way to execute influences? 

   I can see where problems might be. For example in the Semi rule a potential
   execution would need to guess the z. Also e.g. in IfCondThen we have
   "assigned c1 x" where x is not yet determined, so again x would need to be
   guessed. Maybe there is a better definition of 'influences' that allows
   execution. However my version might still be ok for the soundness proof.

   One thing one could do, is instead of the "assigned c x", we define a
   function "assigned_vars" similar to "vars" and have "x \<in> assigned_vars c"
   instead.

   Guessing the "z" in the Semi and WhileTrans rule might be done with some
   kind of heuristic of possible values for z. Maybe something like z is
   either y or x or in "assigned_vars c".

   I assume here that the soundness proof might not effected by this
   shortcoming. We will see next week.

   Technical question: Is there some documentation on "code_pred"? I can
   actually execute "code_pred influences ." without error or warning or any
   hint at all, but the values/value fail miserably.
*)

(* proof automation *)
(* keep in mind this is potentially to aggressive use of automation *)
inductive_cases SkipE[elim!]:   "influences y SKIP x"
inductive_cases AssignE[elim!]: "influences y (z ::= a) x"
inductive_cases SemiE[elim!]:   "influences y (c1; c2) x"
inductive_cases IfE[elim!]:     "influences y (IF b THEN c1 ELSE c2) x"
inductive_cases WhileE[elim]:   "influences y (WHILE b DO c) x"
declare influences.intros[simp, intro]
declare WhileTrans[simp del]


(* Trying some examples. I have to proof manually. Automatic proof again
   fails, I guess because the proofer would have to guess the intermediary
   variables, that I give explicitally. Again I think with my definition of
   'influences' there is not much we can do about that. A different definition
   might not have this shortcoming. *)

lemma "influences 2 (WHILE b DO (0 ::= (V 1); 1 ::= (V 2))) 0"
apply (rule WhileTrans[of _ _ _ 1])
apply (rule WhileStep)
apply (rule Semi[of _ _ 2])
apply simp
apply simp
apply (rule Semi[of _ _ 0]) 
apply auto
done

lemma "influences 3 (WHILE b DO (0 ::= (V 1); 1 ::= (V 2); 2::= (V 3))) 0"
apply (rule WhileTrans[of _ _ _ 1])
apply (rule WhileTrans[of _ _ _ 2])
apply (rule WhileStep)
apply (rule Semi[of _ _ 3])
apply (rule Semi[of _ _ 3])
apply simp
apply simp
apply simp
apply (rule Semi[of _ _ 1])
apply (rule Semi[of _ _ 2])
apply simp
apply simp
apply simp
apply (rule Semi[of _ _ 0])
apply (rule Semi[of _ _ 0])
apply auto
done

text {* All dependencies of a variable *}
abbreviation deps :: "com \<Rightarrow> name \<Rightarrow> name set" where
"deps c x == {y. influences y c x}"


text {* A simple lemma that is useful later *}

lemma deps_unassigned_keep:
  "\<not> assigned c x \<Longrightarrow> x \<in> deps c x"
proof induct
qed auto


(* some other property that should hold, though i have trouble prooving it *)
lemma deps_unassigned_neq:
  "\<not> assigned c x \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> y \<in> deps c x"
apply (induct arbitrary: y)
apply auto
apply metis
apply (rule WhileE)
apply auto
proof -
  fix b c y
  {
    assume 0: "\<And> w. x\<noteq>w \<Longrightarrow> \<not> influences w c x"
    assume 1: "\<not> assigned c x"
    assume 2: "x \<noteq> y"
    from 0 1 2 have "\<not> influences y (WHILE b DO c) x" sorry 
    (* applying WhileE makes me go in circles *)
  }
  from this show "\<lbrakk>\<And>z. x \<noteq> z \<Longrightarrow> \<not> influences z c x; \<not> assigned c x; x \<noteq> y;
    influences y (WHILE b DO c) x\<rbrakk> \<Longrightarrow> False" by blast
qed

lemma deps_unassigned_singelton:
  "\<not> assigned c x \<Longrightarrow> {x} = deps c x"
proof
  assume "\<not> assigned c x"
  with deps_unassigned_keep show "{x} \<subseteq> deps c x" by blast
next
  assume 0: "\<not> assigned c x"
  show "deps c x \<subseteq> {x}"
    proof 
      fix a
      assume 1: "a \<in> deps c x"
      with 0 deps_unassigned_neq have 2: "a = x" by metis
      {
        fix t
        have "t \<in> {t}" by (metis insertCI)
      }
      with 2 show "a \<in> {x}" by auto
    qed
qed


text {* Main theorem *}

(* might be useful *)
lemma eq_on_subset: "\<lbrakk> s = s' on X; Y \<subseteq> X \<rbrakk> \<Longrightarrow> s = s' on Y" by auto

(* generalized statement, maybe neccessary *)
lemma "\<lbrakk> (c, s) \<Rightarrow> t; s = s' on X; (deps c x) \<subseteq> X; (c,s') \<Rightarrow> t' \<rbrakk> \<Longrightarrow> t x = t' x"
proof (induct arbitrary: X  t t' rule: big_step_induct)
  case Skip from this have ?case sorry
  have "t' = s'"
oops

lemma deps_sound:
  "\<lbrakk> (c, s) \<Rightarrow> t; s = s' on deps c x; (c, s') \<Rightarrow> t' \<rbrakk>
   \<Longrightarrow> t x = t' x"
proof (induct rule: big_step_induct)
  case (Skip s)
  thus ?case by blast
next
  case (Assign y a s)
  thus ?case by auto
next
  case (IfTrue b s c1 t c2)
  thus ?case
    apply auto
    apply (rule IfE)
    apply auto
    sorry
next 
  case (Semi c1 s1 s2 c2 s3)
  thus ?case
    apply auto
oops

end