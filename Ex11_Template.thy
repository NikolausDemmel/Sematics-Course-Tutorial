header "Hoare Logic for Nondeterministic Programs and Assertions"

theory Hoare_Nondet imports "../../Semantics/BExp" begin

subsection "Language Definition"

datatype
  com = SKIP 
      | Assign name aexp       ("_ ::= _" [1000, 61] 61)
      | Semi   com  com        ("_; _"  [60, 61] 60)
      | If     bexp com com    ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com        ("WHILE _ DO _"  [0, 61] 61)

      (* new commands *)
      | Or com com             ("_ OR _" [60, 61] 60)
      | Arbitrary name         ("_ ::= *" [1000] 61)
      | ASSERT bexp             




subsection "Big-Step Semantics"

inductive
  big_step :: "com \<times> state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
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
(* new rules *)
OrLeft: "(c\<^isub>1,s) \<Rightarrow> t \<Longrightarrow> (c\<^isub>1 OR c\<^isub>2,s) \<Rightarrow> t" |
OrRight: "(c\<^isub>2,s) \<Rightarrow> t \<Longrightarrow> (c\<^isub>1 OR c\<^isub>2,s) \<Rightarrow> t" |
Arbitrary: "(x ::= *, s) \<Rightarrow> s(x := v)" |
Assert: "bval b s \<Longrightarrow> (ASSERT b, s) \<Rightarrow> s"


text{* The usual reasoning setup *}

declare big_step.intros [intro]
lemmas big_step_induct = big_step.induct[split_format(complete)]

inductive_cases skipE[elim!]: "(SKIP,s) \<Rightarrow> t"
inductive_cases AssignE[elim!]: "(x ::= a,s) \<Rightarrow> t"
inductive_cases SemiE[elim!]: "(c1;c2,s1) \<Rightarrow> s3"
inductive_cases IfE[elim!]: "(IF b THEN c1 ELSE c2,s) \<Rightarrow> t"
inductive_cases WhileE[elim]: "(WHILE b DO c,s) \<Rightarrow> t"
inductive_cases OrE[elim!]: "(c1 OR c2, s) \<Rightarrow> t"
inductive_cases ArbitraryE[elim!]: "(x ::= *, s) \<Rightarrow> t"
inductive_cases AssertE[elim!]: "(ASSERT b, s) \<Rightarrow> t"



subsection "Hoare Logic for Partial Correctness"

types assn = "state \<Rightarrow> bool"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> name \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
Skip: "\<turnstile> {P} SKIP {P}"  |

Assign:  "\<turnstile> {\<lambda>s. P(s[a/x])} x::=a {P}"  |

Semi: "\<lbrakk> \<turnstile> {P} c\<^isub>1 {Q};  \<turnstile> {Q} c\<^isub>2 {R} \<rbrakk>
       \<Longrightarrow> \<turnstile> {P} c\<^isub>1;c\<^isub>2 {R}"  |

If: "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> bval b s} c\<^isub>1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not> bval b s} c\<^isub>2 {Q} \<rbrakk>
     \<Longrightarrow> \<turnstile> {P} IF b THEN c\<^isub>1 ELSE c\<^isub>2 {Q}"  |

While: "\<turnstile> {\<lambda>s. P s \<and> bval b s} c {P} \<Longrightarrow>
        \<turnstile> {P} WHILE b DO c {\<lambda>s. P s \<and> \<not> bval b s}"  |

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk>
        \<Longrightarrow> \<turnstile> {P'} c {Q'}"



lemmas [simp] = hoare.Skip hoare.Assign hoare.Semi If

lemmas [intro!] = hoare.Skip hoare.Assign hoare.Semi hoare.If


lemma strengthen_pre:
  "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s;  \<turnstile> {P} c {Q} \<rbrakk> \<Longrightarrow> \<turnstile> {P'} c {Q}"
by (blast intro: conseq)

lemma weaken_post:
  "\<lbrakk> \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s \<rbrakk> \<Longrightarrow>  \<turnstile> {P} c {Q'}"
by (blast intro: conseq)


subsection "Soundness"

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P}c{Q} = (\<forall>s t. (c,s) \<Rightarrow> t  \<longrightarrow>  P s \<longrightarrow>  Q t)"

lemma hoare_sound: "\<turnstile> {P}c{Q}  \<Longrightarrow>  \<Turnstile> {P}c{Q}"
proof(induct rule: hoare.induct)
  case (While P b c)
  { fix s t
    have "(WHILE b DO c,s) \<Rightarrow> t  \<Longrightarrow>  P s \<longrightarrow> P t \<and> \<not> bval b t"
    proof(induct "WHILE b DO c" s t rule: big_step_induct)
      case WhileFalse thus ?case by blast
    next
      case WhileTrue thus ?case
        using While(2) unfolding hoare_valid_def by blast
    qed
  }
  thus ?case unfolding hoare_valid_def by blast
qed (auto simp: hoare_valid_def)


subsection "Weakest Precondition"

definition wp :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"wp c Q = (\<lambda>s. \<forall>t. (c,s) \<Rightarrow> t  \<longrightarrow>  Q t)"

lemma wp_SKIP[simp]: "wp SKIP Q = Q"
by (rule ext) (auto simp: wp_def)

lemma wp_Ass[simp]: "wp (x::=a) Q = (\<lambda>s. Q(s[a/x]))"
by (rule ext) (auto simp: wp_def)

lemma wp_Semi[simp]: "wp (c\<^isub>1;c\<^isub>2) Q = wp c\<^isub>1 (wp c\<^isub>2 Q)"
by (rule ext) (auto simp: wp_def)

lemma wp_If[simp]:
 "wp (IF b THEN c\<^isub>1 ELSE c\<^isub>2) Q =
 (\<lambda>s. (bval b s \<longrightarrow> wp c\<^isub>1 Q s) \<and>  (\<not> bval b s \<longrightarrow> wp c\<^isub>2 Q s))"
by (rule ext) (auto simp: wp_def)

lemma wp_While_If:
 "wp (WHILE b DO c) Q s =
  wp (IF b THEN c;WHILE b DO c ELSE SKIP) Q s"
unfolding wp_def by blast

lemma wp_While_True[simp]: "bval b s \<Longrightarrow>
  wp (WHILE b DO c) Q s = wp (c; WHILE b DO c) Q s"
by(simp add: wp_While_If)

lemma wp_While_False[simp]: "\<not> bval b s \<Longrightarrow> wp (WHILE b DO c) Q s = Q s"
by(simp add: wp_While_If)


subsection "Completeness"

lemma wp_is_pre: "\<turnstile> {wp c Q} c {Q}"
proof(induct c arbitrary: Q)
  case Semi thus ?case by(auto intro: Semi)
next
  case (If b c1 c2)
  let ?If = "IF b THEN c1 ELSE c2"
  show ?case
  proof(rule hoare.If)
    show "\<turnstile> {\<lambda>s. wp ?If Q s \<and> bval b s} c1 {Q}"
    proof(rule strengthen_pre[OF _ If(1)])
      show "\<forall>s. wp ?If Q s \<and> bval b s \<longrightarrow> wp c1 Q s" by auto
    qed
    show "\<turnstile> {\<lambda>s. wp ?If Q s \<and> \<not> bval b s} c2 {Q}"
    proof(rule strengthen_pre[OF _ If(2)])
      show "\<forall>s. wp ?If Q s \<and> \<not> bval b s \<longrightarrow> wp c2 Q s" by auto
    qed
  qed
next
  case (While b c)
  let ?w = "WHILE b DO c"
  have "\<turnstile> {wp ?w Q} ?w {\<lambda>s. wp ?w Q s \<and> \<not> bval b s}"
  proof(rule hoare.While)
    show "\<turnstile> {\<lambda>s. wp ?w Q s \<and> bval b s} c {wp ?w Q}"
    proof(rule strengthen_pre[OF _ While(1)])
      show "\<forall>s. wp ?w Q s \<and> bval b s \<longrightarrow> wp c (wp ?w Q) s" by auto
    qed
  qed
  thus ?case
  proof(rule weaken_post)
    show "\<forall>s. wp ?w Q s \<and> \<not> bval b s \<longrightarrow> Q s" by auto
  qed
qed auto

lemma hoare_relative_complete: assumes "\<Turnstile> {P}c{Q}" shows "\<turnstile> {P}c{Q}"
proof(rule strengthen_pre)
  show "\<forall>s. P s \<longrightarrow> wp c Q s" using assms
    by (auto simp: hoare_valid_def wp_def)
  show "\<turnstile> {wp c Q} c {Q}" by(rule wp_is_pre)
qed

end
