header "Semantics homework sheet 10 - Nikolaus Demmel"

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

inductive_cases SkipE[elim!]:   "influences y SKIP x"
inductive_cases AssignE[elim!]: "influences y (z ::= a) x"
inductive_cases SemiE[elim!]:   "influences y (c1; c2) x"
inductive_cases IfE[elim!]:     "influences y (IF b THEN c1 ELSE c2) x"
inductive_cases WhileE:         "influences y (WHILE b DO c) x"


text {* All dependencies of a variable *}
abbreviation deps :: "com \<Rightarrow> name \<Rightarrow> name set" where
"deps c x == {y. influences y c x}"


text {* A simple lemma that is useful later *}

lemma deps_unassigned_keep:
  "\<not> assigned c x \<Longrightarrow> x \<in> deps c x"
proof induct
qed auto


text {* Main theorem *}

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
    with WhileTrue(1,7) obtain s2' 
      where s2': "(c, s') \<Rightarrow> s2' \<and> (WHILE b DO c, s2') \<Rightarrow> t'" by blast
    { fix w
      assume "w \<in> deps (WHILE b DO c) x"
      hence "deps c w \<subseteq> deps (WHILE b DO c) x" using WhileTrans by fastsimp 
      with WhileTrue(6) have "s = s' on deps c w" by fastsimp
      hence "s2 w = s2' w" using s2' WhileTrue(3)[of w s' s2'] by simp
    }
    hence "s2 = s2' on deps (WHILE b DO c) x" by simp
    with s2' WhileTrue(5)[of x s2' t'] show "t x = t' x" by simp
  next
    case False
    hence "s x = s' x" using deps_unassigned_keep WhileTrue(6) by simp
    moreover
    from WhileTrue(1,2,4) have "(WHILE b DO c, s) \<Rightarrow> t" by blast
    hence "s x = t x" using unassigned_implies_equal False by simp
    moreover 
    have "s' x = t' x" using unassigned_implies_equal False WhileTrue(7) by simp
    ultimately show "t x = t' x" by simp
  qed
qed

end