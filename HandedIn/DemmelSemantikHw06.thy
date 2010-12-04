header "Semantics homework sheet 6 - Nikolaus Demmel"

theory Hw06 imports BExp begin

(* CONTENT FROM Com.thy *)

datatype
  com = SKIP 
      | Assign name aexp         ("_ ::= _" [1000, 61] 61)
      | Semi   com  com          ("_; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)
(* BEGIN MODIFIED *)
      | Or     com com          ("_ OR _" [60, 61] 60)
(* END MODIFIED *)



(* CONTENT FROM Big_Step.thy *)

subsection "Big-Step Semantics of Commands"

inductive
  big_step :: "com * state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
Skip:    "(SKIP,s) \<Rightarrow> s" |
Assign:  "(x ::= a,s) \<Rightarrow> s(x := aval a s)" |
Semi:    "\<lbrakk> (c\<^isub>1,s\<^isub>1) \<Rightarrow> s\<^isub>2;  (c\<^isub>2,s\<^isub>2) \<Rightarrow> s\<^isub>3 \<rbrakk> \<Longrightarrow>
          (c\<^isub>1;c\<^isub>2, s\<^isub>1) \<Rightarrow> s\<^isub>3" |

IfTrue:  "\<lbrakk> bval b s;  (c\<^isub>1,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         (IF b THEN c\<^isub>1 ELSE c\<^isub>2, s) \<Rightarrow> t" |
IfFalse: "\<lbrakk> \<not>bval b s;  (c\<^isub>2,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow>
         (IF b THEN c\<^isub>1 ELSE c\<^isub>2, s) \<Rightarrow> t" |



WhileFalse: "\<not>bval b s \<Longrightarrow> (WHILE b DO c,s) \<Rightarrow> s" |
WhileTrue:  "\<lbrakk> bval b s\<^isub>1;  (c,s\<^isub>1) \<Rightarrow> s\<^isub>2;  (WHILE b DO c, s\<^isub>2) \<Rightarrow> s\<^isub>3 \<rbrakk> \<Longrightarrow>
             (WHILE b DO c, s\<^isub>1) \<Rightarrow> s\<^isub>3" |

(* BEGIN MODIFIED *)
Or1:     "(c1,s) \<Rightarrow> t \<Longrightarrow> (c1 OR c2, s) \<Rightarrow> t" |
Or2:     "(c2,s) \<Rightarrow> t \<Longrightarrow> (c1 OR c2, s) \<Rightarrow> t"
(* END MODIFIED *)


text{* We want to execute the big-step rules: *}

code_pred big_step .

definition list :: "state \<Rightarrow> nat \<Rightarrow> nat list" where
"list s n = map s [0 ..< n]"

inductive exec where
"(c,nth ns) \<Rightarrow> s  \<Longrightarrow>  exec c ns (list s (length ns))"

code_pred exec .


text{* Proof automation: *}

declare big_step.intros [intro]

lemmas big_step_induct = big_step.induct[split_format(complete)]


subsection "Rule inversion"


inductive_cases skipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SemiE[elim!]: "(c1;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"

(* BEGIN MODIFIED *)
inductive_cases OrE[elim!]: "(c1 OR c2,s) \<Rightarrow> t"
thm OrE
(* END MODIFIED *)


subsection "Command Equivalence"

abbreviation
  equiv_c :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<sim>" 50) where
  "c \<sim> c' == (\<forall>s t. (c,s) \<Rightarrow> t  =  (c',s) \<Rightarrow> t)"

(* BEGIN MODIFIED *)
lemma commute_or: "c1 OR c2 \<sim> c2 OR c1" by blast
(* END MODIFIED *)

subsection "Execution is deterministic"

(* Well... its not any more :-) *)



(* CONTENT FROM Small_Step.thy *)

subsection "The transition relation"

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
SmallAssign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

SmallSemi1:   "(SKIP;c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |
SmallSemi2:   "(c\<^isub>1,s) \<rightarrow> (c\<^isub>1',s') \<Longrightarrow> (c\<^isub>1;c\<^isub>2,s) \<rightarrow> (c\<^isub>1';c\<^isub>2,s')" |

SmallIfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>1,s)" |
SmallIfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |

SmallWhile:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c; WHILE b DO c ELSE SKIP,s)" |

(* BEGIN MODIFIED *)
SmallOr1:     "(c1 OR c2,s) \<rightarrow> (c1,s)" |
SmallOr2:     "(c1 OR c2,s) \<rightarrow> (c2,s)"
(* END MODIFIED *)

inductive
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"  (infix "\<rightarrow>*" 55)  where
refl:  "cs \<rightarrow>* cs" |
step:  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<rightarrow>* cs'' \<Longrightarrow> cs \<rightarrow>* cs''"


subsection{* Executability *}

code_pred small_step .
code_pred small_steps .

inductive execl :: "com \<Rightarrow> nat list \<Rightarrow> com \<Rightarrow> nat list \<Rightarrow> bool" where
"small_steps (c,nth ns) (c',t) \<Longrightarrow> execl c ns c' (list t (size ns))"

code_pred execl .

(* BEGIN MODIFIED *)
values "{(c',t) . execl (0 ::= V 2 OR 1 ::= V 0) [3,7,5] c' t}"
(* END MODIFIED *)

subsection{* Proof infrastructure *}

subsubsection{* Induction rules *}

lemmas small_step_induct = small_step.induct[split_format(complete)]
lemmas small_steps_induct = small_steps.induct[split_format(complete)]

subsubsection{* Proof automation *}

declare small_step.intros[simp,intro]
declare small_steps.refl[simp,intro]

lemma step1[simp, intro]: "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow>* cs'"
by(metis refl step)

text{* So called transitivity rules. See below. *}

declare step[trans] step1[trans]

lemma step2[trans]:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<rightarrow> cs'' \<Longrightarrow> cs \<rightarrow>* cs''"
by(metis refl step)

lemma small_steps_trans[trans]:
  "cs \<rightarrow>* cs' \<Longrightarrow> cs' \<rightarrow>* cs'' \<Longrightarrow> cs \<rightarrow>* cs''"
proof(induct rule: small_steps.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis small_steps.step)
qed

text{* Rule inversion: *}

inductive_cases SmallSkipE[elim!]: "(SKIP,s) \<rightarrow> ct"
inductive_cases SmallAssignE[elim!]: "(x::=a,s) \<rightarrow> ct"
inductive_cases SmallSemiE[elim]: "(c1;c2,s) \<rightarrow> ct"
inductive_cases SmallIfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<rightarrow> ct"
inductive_cases SmallWhileE[elim]: "(WHILE b DO c, s) \<rightarrow> ct"
(* BEGIN MODIFIED *)
inductive_cases SmallOrE[elim!]: "(c1 OR c2, s) \<rightarrow> ct"
thm SmallOrE
(* END MODIFIED *)


subsection "Equivalence with big-step semantics"

lemma rtrancl_semi2: "(c1,s) \<rightarrow>* (c1',s') \<Longrightarrow> (c1;c2,s) \<rightarrow>* (c1';c2,s')"
proof(induct rule: small_steps_induct)
  case refl thus ?case by simp
next
  case step
  thus ?case by (metis SmallSemi2 small_steps.step)
qed

lemma semi_comp:
  "\<lbrakk> (c1,s1) \<rightarrow>* (SKIP,s2); (c2,s2) \<rightarrow>* (SKIP,s3) \<rbrakk>
   \<Longrightarrow> (c1;c2, s1) \<rightarrow>* (SKIP,s3)"
by(blast intro: small_steps.step rtrancl_semi2 small_steps_trans)

text{* The following proof corresponds to one on the board where one would
show chains of @{text "\<rightarrow>"} and @{text "\<rightarrow>*"} steps. This is what the
also/finally proof steps do: they compose chains, implicitly using the rules
declared with attribute [trans] above. *}

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induct rule: big_step.induct)
  fix s show "(SKIP,s) \<rightarrow>* (SKIP,s)" by simp
next
  fix x a s show "(x ::= a,s) \<rightarrow>* (SKIP, s(x := aval a s))" by auto
next
  fix c1 c2 s1 s2 s3
  assume "(c1,s1) \<rightarrow>* (SKIP,s2)" and "(c2,s2) \<rightarrow>* (SKIP,s3)"
  thus "(c1;c2, s1) \<rightarrow>* (SKIP,s3)" by (rule semi_comp)
next
  fix s::state and b c0 c1 t
  assume "bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c0,s)" by simp
  also assume "(c0,s) \<rightarrow>* (SKIP,t)"
  finally show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" . --"= by assumption"
next
  fix s::state and b c0 c1 t
  assume "\<not>bval b s"
  hence "(IF b THEN c0 ELSE c1,s) \<rightarrow> (c1,s)" by simp
  also assume "(c1,s) \<rightarrow>* (SKIP,t)"
  finally show "(IF b THEN c0 ELSE c1,s) \<rightarrow>* (SKIP,t)" .
next
  fix b c and s::state
  assume b: "\<not>bval b s"
  let ?if = "IF b THEN c; WHILE b DO c ELSE SKIP"
  have "(WHILE b DO c,s) \<rightarrow> (?if, s)" by blast
  also have "(?if,s) \<rightarrow> (SKIP, s)" by (simp add: b)
  finally show "(WHILE b DO c,s) \<rightarrow>* (SKIP,s)" by auto
next
  fix b c s s' t
  let ?w  = "WHILE b DO c"
  let ?if = "IF b THEN c; ?w ELSE SKIP"
  assume w: "(?w,s') \<rightarrow>* (SKIP,t)"
  assume c: "(c,s) \<rightarrow>* (SKIP,s')"
  assume b: "bval b s"
  have "(?w,s) \<rightarrow> (?if, s)" by blast
  also have "(?if, s) \<rightarrow> (c; ?w, s)" by (simp add: b)
  also have "(c; ?w,s) \<rightarrow>* (SKIP,t)" by(rule semi_comp[OF c w])
  finally show "(WHILE b DO c,s) \<rightarrow>* (SKIP,t)" by auto
(* BEGIN MODIFIED *)
next
  fix c1 c2 s s'
  assume c1: "(c1, s) \<rightarrow>* (SKIP, s')"
  have "(c1 OR c2, s) \<rightarrow> (c1, s)" by simp
  from this c1 show "(c1 OR c2, s) \<rightarrow>* (SKIP, s')" by (rule step)
next
  fix c1 c2 s s'
  assume c2: "(c2, s) \<rightarrow>* (SKIP, s')"
  have "(c1 OR c2, s) \<rightarrow> (c2, s)" by simp
  from this c2 show "(c1 OR c2, s) \<rightarrow>* (SKIP, s')" by (rule step)
(* END MODIFIED *)
qed

text{* Each case of the induction can be proved automatically: *}
lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (SKIP,t)"
proof (induct rule: big_step.induct)
  case Skip show ?case by blast
next
  case Assign show ?case by blast
next
  case Semi thus ?case by (blast intro: semi_comp)
next
  case IfTrue thus ?case by (blast intro: step)
next
  case IfFalse thus ?case by (blast intro: step)
next
  case WhileFalse thus ?case
    by (metis step step1 SmallIfFalse SmallWhile)
next
  case WhileTrue
  thus ?case
    by(metis SmallWhile semi_comp SmallIfTrue step[of "(a,b)",standard])
(* FIXME metis cannot find the proof w/o at least one pair in step *)
(* BEGIN MODIFIED *)
next
  case Or1
  thus ?case by (blast intro: step)
next
  case Or2
  thus ?case by (blast intro: step)
(* END MODIFIED *)
qed

lemma small1_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induct arbitrary: t rule: small_step.induct)
apply auto
done

lemma small_big_continue:
  "cs \<rightarrow>* cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
apply (induct rule: small_steps.induct)
apply (auto intro: small1_big_continue)
done

lemma small_to_big: "cs \<rightarrow>* (SKIP,t) \<Longrightarrow> cs \<Rightarrow> t"
by (metis small_big_continue Skip)

text {*
  Finally, the equivalence theorem:
*}
theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (SKIP,t)"
by(metis big_to_small small_to_big)


end
