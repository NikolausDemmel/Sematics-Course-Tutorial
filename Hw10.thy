header "Semantics homework sheet 10 part (a) - Nikolaus Demmel"

theory Hw10
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
  Skip[intro]:       "influences x SKIP x" |
  AssignEq[intro]:   "y \<in> (vars a) \<Longrightarrow> influences y (x ::= a) x" |
  AssignNeq[intro]:  "y \<noteq> x \<Longrightarrow> influences y (x ::= a) y" |
  Semi[intro]:       "\<lbrakk> influences y c1 z; influences z c2 x \<rbrakk> \<Longrightarrow> influences y (c1; c2) x" |
  IfThen[intro]:     "influences y c1 x \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  IfElse[intro]:     "influences y c2 x \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  IfCondThen[intro]: "\<lbrakk> y \<in> vars b; assigned c1 x \<rbrakk> 
                       \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  IfCondElse[intro]: "\<lbrakk> y \<in> vars b; assigned c2 x \<rbrakk> 
                       \<Longrightarrow> influences y (IF b THEN c1 ELSE c2) x" |
  WhileSkip[intro]:  "influences x (WHILE b DO c) x" |
  WhileCond[intro]:  "\<lbrakk> y \<in> vars b; assigned c x \<rbrakk> \<Longrightarrow> influences y (WHILE b DO c) x" |
  WhileTrans:        "\<lbrakk> influences y c z; influences z (WHILE b DO c) x \<rbrakk> 
                       \<Longrightarrow> influences y (WHILE b DO c) x"
(*  WhileTrans: "\<lbrakk> influences y (WHILE b DO c) z; influences z c x \<rbrakk> 
               \<Longrightarrow> influences y (WHILE b DO c) x" (* this rule might cause trouble *)
*)

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
inductive_cases WhileE:   "influences y (WHILE b DO c) x"
(*declare influences.intros[simp]
declare WhileTrans[simp del] *)


(* Trying some examples. I have to proof manually. Automatic proof again
   fails, I guess because the proofer would have to guess the intermediary
   variables, that I give explicitally. Again I think with my definition of
   'influences' there is not much we can do about that. A different definition
   might not have this shortcoming. *)

(*
lemma "influences 2 (WHILE b DO (0 ::= (V 1); 1 ::= (V 2))) 0"
apply (rule WhileTrans[of _ _ 1])
apply (rule WhileTrans[)
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

*)

text {* All dependencies of a variable *}
abbreviation deps :: "com \<Rightarrow> name \<Rightarrow> name set" where
"deps c x == {y. influences y c x}"


text {* A simple lemma that is useful later *}

lemma deps_unassigned_keep:
  "\<not> assigned c x \<Longrightarrow> x \<in> deps c x"
proof induct
qed auto

(*
(* some other property that should hold, though i have trouble prooving it *)
lemma deps_unassigned_neq:
  "\<not> assigned c x \<Longrightarrow> x \<noteq> y \<Longrightarrow> \<not> y \<in> deps c x"
apply (induct arbitrary: y x)
apply auto
apply metis
proof -
  fix b c y x
  {
    assume 0: "\<And> w v. \<lbrakk> v\<noteq>w; \<not> assigned c v \<rbrakk> \<Longrightarrow> \<not> influences w c v"
    assume 1: "\<not> assigned c x"
    assume 2: "x \<noteq> y"
    assume 3: "influences y (WHILE b DO c) x"
(*    assume 4: "influences y c z"
    assume 5: "influences z (WHILE b DO c) x" *)
    from 0 1 2 have 4: "\<not> influences y c x" by blast
    from 2 have "influences y (WHILE b DO c) x \<Longrightarrow> False" 
    proof (induct y "(WHILE b DO c)" x rule: influences.induct)
    
    from 4 0  have "y = z" by blast
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
*)

text {* Main theorem *}

(* might be useful *)
lemma eq_on_subset: "\<lbrakk> s = s' on X; Y \<subseteq> X \<rbrakk> \<Longrightarrow> s = s' on Y" by auto

(*
(* generalized statement, maybe neccessary *)
lemma "\<lbrakk> (c, s) \<Rightarrow> t; s = s' on X; (deps c x) \<subseteq> X; (c,s') \<Rightarrow> t' \<rbrakk> \<Longrightarrow> t x = t' x"
proof (induct arbitrary: X  t t' rule: big_step_induct)
  case Skip from this have ?case sorry
  have "t' = s'"
oops
*)

lemma deps_sound:
  "\<lbrakk> (c, s) \<Rightarrow> t; s = s' on deps c x; (c, s') \<Rightarrow> t' \<rbrakk>
   \<Longrightarrow> t x = t' x"
proof (induct c s t arbitrary: x s' t' rule: big_step_induct)
  case Skip 
  thus ?case by blast
next
  case (Assign y a s)
  thus ?case
  proof (cases "x = y")
    case False
    with Assign show ?thesis by auto
  next
    case True
    hence "vars a = deps (y ::= a) x" by fastsimp
    with Assign(1) have "aval a s' = aval a s" by fastsimp 
    with Assign(2) have "t' y = (s'(y := aval a s)) y" by fastsimp
    hence "t' y = aval a s" by fastsimp
    with `x = y` show ?thesis by fastsimp
  qed
next
  case (Semi c1 s s2 c2 t)
  from Semi(6) obtain s2' where s2':"(c1, s') \<Rightarrow> s2' \<and> (c2, s2') \<Rightarrow> t'" by fastsimp
  { fix w
    assume "w \<in> deps c2 x"
    hence "deps c1 w \<subseteq> deps (c1;c2) x" by fastsimp
    with Semi(5) s2' Semi(2)[of w s' s2'] have "s2 w = s2' w" by fastsimp
  }
  hence "s2 = s2' on deps c2 x" by fastsimp
  with Semi(4)[of x s2' t'] s2' show "t x = t' x" by fastsimp
next
  case (IfTrue b s c1 t c2)
  show ?case
  proof (cases "assigned c1 x \<or> assigned c2 x")
    case True
    with IfTrue(4) have "s = s' on vars b" by fastsimp
    hence "bval b s = bval b s'" by (simp add: bval_eq_if_eq_on_vars)
    with IfTrue(1,5) have "(c1, s') \<Rightarrow> t'" by blast
    thus "t x = t' x" using IfTrue(3-4) by blast
  next
    case False
    hence "s x = s' x" using deps_unassigned_keep IfTrue(4) by fastsimp
    moreover
    from unassigned_implies_equal IfTrue(2) False have "s x = t x" by fastsimp
    moreover
    from unassigned_implies_equal IfTrue(5) False have "s' x = t' x" by fastsimp
    ultimately
    show "t x = t' x" by simp
  qed
next
  case (IfFalse b s c2 t c1)
  show ?case
  proof (cases "assigned c1 x \<or> assigned c2 x")
    case True
    with IfFalse(4) have "s = s' on vars b" by fastsimp
    hence "bval b s = bval b s'" by (simp add: bval_eq_if_eq_on_vars)
    with IfFalse(1,5) have "(c2, s') \<Rightarrow> t'" by blast
    thus "t x = t' x" using IfFalse(3-4) by blast
  next
    case False
    hence "s x = s' x" using deps_unassigned_keep IfFalse(4) by fastsimp
    moreover
    from unassigned_implies_equal IfFalse(2) False have "s x = t x" by fastsimp
    moreover
    from unassigned_implies_equal IfFalse(5) False have "s' x = t' x" by fastsimp
    ultimately
    show "t x = t' x" by simp
  qed
next
  case (WhileFalse b s c)
  thus ?case
  proof (cases "assigned c x")
    case True
    with WhileFalse(2) have "s = s' on vars b" by fastsimp
    hence "bval b s = bval b s'" by (simp add: bval_eq_if_eq_on_vars)
    with WhileFalse(1,3) have "s' = t'" by fastsimp
    with WhileFalse(2) show "s x = t' x" by fastsimp
  next
    case False
    with unassigned_implies_equal WhileFalse(2,3) deps_unassigned_keep
      show "s x = t' x" by simp
  qed
next
  case (WhileTrue b s c s2 t)
  thus ?case
  proof (cases "assigned c x")
    case True
    with WhileTrue(6) have "s = s' on vars b" by blast
    hence "bval b s = bval b s'" by (simp add: bval_eq_if_eq_on_vars)
    with WhileTrue(1,7) obtain s2' where "(c, s') \<Rightarrow> s2' \<and> (WHILE b DO c, s2') \<Rightarrow> t'" by blast
    

. 


end