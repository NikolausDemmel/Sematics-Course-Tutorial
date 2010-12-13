header "A Typed Language"

theory Types imports Complex_Main begin

subsection "Arithmetic Expressions"

datatype val = Iv int | Rv real

types
  name = nat
  state = "name \<Rightarrow> val"

datatype aexp =  Ic int | Rc real | V name | Plus aexp aexp

inductive taval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
"taval (Ic i) s (Iv i)" |
"taval (Rc r) s (Rv r)" |
"taval (V x) s (s x)" |
"taval a\<^isub>1 s (Iv i\<^isub>1) \<Longrightarrow> taval a\<^isub>2 s (Iv i\<^isub>2)
 \<Longrightarrow> taval (Plus a\<^isub>1 a\<^isub>2) s (Iv(i\<^isub>1+i\<^isub>2))" |
"taval a\<^isub>1 s (Rv r\<^isub>1) \<Longrightarrow> taval a\<^isub>2 s (Rv r\<^isub>2)
 \<Longrightarrow> taval (Plus a\<^isub>1 a\<^isub>2) s (Rv(r\<^isub>1+r\<^isub>2))"

inductive_cases [elim!]:
  "taval (Ic i) s v"  "taval (Rc i) s v"
  "taval (V x) s v"
  "taval (Plus a1 a2) s v"

subsection "Boolean Expressions"

datatype bexp = B bool | Not bexp | And bexp bexp | Less aexp aexp

inductive tbval :: "bexp \<Rightarrow> state \<Rightarrow> bool \<Rightarrow> bool" where
"tbval (B bv) s bv" |
"tbval b s bv \<Longrightarrow> tbval (Not b) s (\<not> bv)" |
"tbval b\<^isub>1 s bv\<^isub>1 \<Longrightarrow> tbval b\<^isub>2 s bv\<^isub>2 \<Longrightarrow> tbval (And b\<^isub>1 b\<^isub>2) s (bv\<^isub>1 & bv\<^isub>2)" |
"taval a\<^isub>1 s (Iv i\<^isub>1) \<Longrightarrow> taval a\<^isub>2 s (Iv i\<^isub>2) \<Longrightarrow> tbval (Less a\<^isub>1 a\<^isub>2) s (i\<^isub>1 < i\<^isub>2)" |
"taval a\<^isub>1 s (Rv r\<^isub>1) \<Longrightarrow> taval a\<^isub>2 s (Rv r\<^isub>2) \<Longrightarrow> tbval (Less a\<^isub>1 a\<^isub>2) s (r\<^isub>1 < r\<^isub>2)"

subsection "Syntax of Commands"
(* a copy of Com.thy - keep in sync! *)

datatype
  com = SKIP 
      | Assign name aexp         ("_ ::= _" [1000, 61] 61)
      | Semi   com  com          ("_; _"  [60, 61] 60)
      | If     bexp com com     ("IF _ THEN _ ELSE _"  [0, 0, 61] 61)
      | While  bexp com         ("WHILE _ DO _"  [0, 61] 61)


subsection "Small-Step Semantics of Commands"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "taval a s v \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := v))" |

Semi1:   "(SKIP;c,s) \<rightarrow> (c,s)" |
Semi2:   "(c\<^isub>1,s) \<rightarrow> (c\<^isub>1',s') \<Longrightarrow> (c\<^isub>1;c\<^isub>2,s) \<rightarrow> (c\<^isub>1';c\<^isub>2,s')" |

IfTrue:  "tbval b s True \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>1,s)" |
IfFalse: "tbval b s False \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsection "The Type System"

datatype ty = Ity | Rty

types tyenv = "name \<Rightarrow> ty"

inductive atyping :: "tyenv \<Rightarrow> aexp \<Rightarrow> ty \<Rightarrow> bool"
  ("(1_/ \<turnstile>/ (_ :/ _))" [50,0,50] 50)
where
Ic_ty: "\<Gamma> \<turnstile> Ic i : Ity" |
Rc_ty: "\<Gamma> \<turnstile> Rc r : Rty" |
V_ty: "\<Gamma> \<turnstile> V x : \<Gamma> x" |
Plus_ty: "\<Gamma> \<turnstile> a\<^isub>1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a\<^isub>2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Plus a\<^isub>1 a\<^isub>2 : \<tau>"

text{* Warning: the ``:'' notation leads to syntactic ambiguities,
i.e. multiple parse trees, because ``:'' also stands for set membership.
In most situations Isabelle's type system will reject all but one parse tree,
but will still inform you of the potential ambiguity. *}

inductive btyping :: "tyenv \<Rightarrow> bexp \<Rightarrow> bool" (infix "\<turnstile>" 50)
where
B_ty: "\<Gamma> \<turnstile> B bv" |
Not_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> Not b" |
And_ty: "\<Gamma> \<turnstile> b\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> b\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> And b\<^isub>1 b\<^isub>2" |
Less_ty: "\<Gamma> \<turnstile> a\<^isub>1 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> a\<^isub>2 : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> Less a\<^isub>1 a\<^isub>2"

inductive ctyping :: "tyenv \<Rightarrow> com \<Rightarrow> bool" (infix "\<turnstile>" 50) where
Skip_ty: "\<Gamma> \<turnstile> SKIP" |
Assign_ty: "\<Gamma> \<turnstile> a : \<Gamma>(x) \<Longrightarrow> \<Gamma> \<turnstile> x ::= a" |
Semi_ty: "\<Gamma> \<turnstile> c\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> c\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> c\<^isub>1;c\<^isub>2" |
If_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c\<^isub>1 \<Longrightarrow> \<Gamma> \<turnstile> c\<^isub>2 \<Longrightarrow> \<Gamma> \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2" |
While_ty: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> WHILE b DO c"

inductive_cases [elim!]:
  "\<Gamma> \<turnstile> x ::= a"  "\<Gamma> \<turnstile> c1;c2"
  "\<Gamma> \<turnstile> IF b THEN c\<^isub>1 ELSE c\<^isub>2"
  "\<Gamma> \<turnstile> WHILE b DO c"

subsection "Well-typed Programs Do Not Get Stuck"

fun type :: "val \<Rightarrow> ty" where
"type (Iv i) = Ity" |
"type (Rv r) = Rty"

lemma [simp]: "type v = Ity \<longleftrightarrow> (\<exists>i. v = Iv i)"
by (cases v) simp_all

lemma [simp]: "type v = Rty \<longleftrightarrow> (\<exists>r. v = Rv r)"
by (cases v) simp_all

definition styping :: "tyenv \<Rightarrow> state \<Rightarrow> bool" (infix "\<turnstile>" 50)
where "\<Gamma> \<turnstile> s  \<longleftrightarrow>  (\<forall>x. type (s x) = \<Gamma> x)"

lemma apreservation:
  "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> taval a s v \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> type v = \<tau>"
apply(induct arbitrary: v rule: atyping.induct)
apply (fastsimp simp: styping_def)+
done

lemma aprogress: "\<Gamma> \<turnstile> a : \<tau> \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. taval a s v"
proof(induct rule: atyping.induct)
  case (Plus_ty \<Gamma> a1 t a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2" by blast
  show ?case
  proof (cases v1)
    case Iv
    with Plus_ty(1,3,5) v show ?thesis
      by(fastsimp intro: taval.intros(4) dest!: apreservation)
  next
    case Rv
    with Plus_ty(1,3,5) v show ?thesis
      by(fastsimp intro: taval.intros(5) dest!: apreservation)
  qed
qed (auto intro: taval.intros)

lemma bprogress: "\<Gamma> \<turnstile> b \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<exists>v. tbval b s v"
proof(induct rule: btyping.induct)
  case (Less_ty \<Gamma> a1 t a2)
  then obtain v1 v2 where v: "taval a1 s v1" "taval a2 s v2"
    by (metis aprogress)
  show ?case
  proof (cases v1)
    case Iv
    with Less_ty v show ?thesis
      by (fastsimp intro!: tbval.intros(4) dest!:apreservation)
  next
    case Rv
    with Less_ty v show ?thesis
      by (fastsimp intro!: tbval.intros(5) dest!:apreservation)
  qed
qed (auto intro: tbval.intros)

theorem progress:
  "\<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists>cs'. (c,s) \<rightarrow> cs'"
proof(induct rule: ctyping.induct)
  case Skip_ty thus ?case by simp
next
  case Assign_ty 
  thus ?case by (metis Assign aprogress)
next
  case Semi_ty thus ?case by simp (metis Semi1 Semi2)
next
  case (If_ty \<Gamma> b c1 c2)
  then obtain bv where "tbval b s bv" by (metis bprogress)
  show ?case
  proof(cases bv)
    assume "bv"
    with `tbval b s bv` show ?case by simp (metis IfTrue)
  next
    assume "\<not>bv"
    with `tbval b s bv` show ?case by simp (metis IfFalse)
  qed
next
  case While_ty show ?case by (metis While)
qed

theorem styping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> \<Gamma> \<turnstile> s'"
proof(induct rule: small_step_induct)
  case Assign thus ?case
    by (auto simp: styping_def) (metis Assign(1,3) apreservation)
qed auto

theorem ctyping_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> c'"
by (induct rule: small_step_induct) (auto simp: ctyping.intros)

inductive
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"  (infix "\<rightarrow>*" 55)  where
refl:  "cs \<rightarrow>* cs" |
step:  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<rightarrow>* cs'' \<Longrightarrow> cs \<rightarrow>* cs''"

lemmas small_steps_induct = small_steps.induct[split_format(complete)]

theorem type_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> \<Gamma> \<turnstile> c \<Longrightarrow> \<Gamma> \<turnstile> s \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
apply(induct rule:small_steps_induct)
apply (metis progress)
by (metis styping_preservation ctyping_preservation)

end
