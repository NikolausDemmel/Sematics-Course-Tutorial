theory Ex09_Template
imports
  "../../Semantics/Com"
  "../../Semantics/Def_Ass_Exp"
  "../../Semantics/Vars"
  "../../Semantics/Util"
begin


subsection "Initialization-Sensitive Small Step Semantics"

inductive
  small_step :: "(com \<times> state) \<Rightarrow> (com \<times> state) \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "aval a s = Some i \<Longrightarrow> (x ::= a, s) \<rightarrow> (SKIP, s(x := Some i))" |

Semi1:   "(SKIP;c,s) \<rightarrow> (c,s)" |
Semi2:   "(c\<^isub>1,s) \<rightarrow> (c\<^isub>1',s') \<Longrightarrow> (c\<^isub>1;c\<^isub>2,s) \<rightarrow> (c\<^isub>1';c\<^isub>2,s')" |

IfTrue:  "bval b s = Some True \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>1,s)" |
IfFalse: "bval b s = Some False \<Longrightarrow> (IF b THEN c\<^isub>1 ELSE c\<^isub>2,s) \<rightarrow> (c\<^isub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow> (IF b THEN c; WHILE b DO c ELSE SKIP,s)"

lemmas small_step_induct = small_step.induct[split_format(complete)]

inductive
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool"  (infix "\<rightarrow>*" 55)  where
refl:  "cs \<rightarrow>* cs" |
step:  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<rightarrow>* cs'' \<Longrightarrow> cs \<rightarrow>* cs''"

lemmas small_steps_induct = small_steps.induct[split_format(complete)]



subsection "Definite Assignment Analysis"

fun AA :: "com \<Rightarrow> name set" where
"AA c = {}"   (* provide a suitable definition *)


fun D :: "name set \<Rightarrow> com \<Rightarrow> bool" where
"D A c = True"   (* provide a suitable definition *)



subsection "Soundness wrt Small Steps"

theorem progress:
  "D (dom s) c \<Longrightarrow> c \<noteq> SKIP \<Longrightarrow> \<exists> cs'. (c,s) \<rightarrow> cs'"
  oops


lemma D_incr: "(c,s) \<rightarrow> (c',s') \<Longrightarrow> dom s \<union> AA c \<subseteq> dom s' \<union> AA c'"
  oops


lemma D_mono: "A \<subseteq> A' \<Longrightarrow> D A c \<Longrightarrow> D A' c"
  oops


theorem D_preservation:
  "(c,s) \<rightarrow> (c',s') \<Longrightarrow> D (dom s) c \<Longrightarrow> D (dom s') c'"
  oops


theorem D_sound:
  "(c,s) \<rightarrow>* (c',s') \<Longrightarrow> D (dom s) c \<Longrightarrow> c' \<noteq> SKIP
   \<Longrightarrow> \<exists>cs''. (c',s') \<rightarrow> cs''"
  oops


end
