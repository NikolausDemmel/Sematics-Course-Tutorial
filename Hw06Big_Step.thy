(* Modified for Homework 06 *)

theory Hw06Big_Step imports Hw06Com begin

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

end
