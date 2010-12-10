header "Semantics sheet 7 tutorial - Nikolaus Demmel"

theory Ex07 imports Big_Step
begin

subsection "Instructions and Stack Machine"

datatype instr = 
  PUSH_N nat | PUSH_V nat | ADD | LESS | AND | NOT |
  STORE nat |
  JMPF nat |
  JMPB nat |
  JMPFZ nat |
  JMPFLESS nat |
  JMPFGE nat

types stack = "nat list"
      config = "nat\<times>state\<times>stack"

abbreviation "hd2 xs == hd(tl xs)"
abbreviation "tl2 xs == tl(tl xs)"

inductive exec1 :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool"
    ("(_/ \<turnstile> (_ \<rightarrow>/ _))" [50,0,0] 50)
  for P :: "instr list"
where
"\<lbrakk> i < size P;  P!i = PUSH_N n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, n#stk)" |
"\<lbrakk> i < size P;  P!i = PUSH_V x \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, s x # stk)" |
"\<lbrakk> i < size P;  P!i = ADD \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, (hd2 stk + hd stk) # tl2 stk)" |
"\<lbrakk> i < size P;  P!i = LESS \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, (if (hd2 stk < hd stk) then 1 else 0) # tl2 stk)" |
"\<lbrakk> i < size P;  P!i = AND \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, (if (hd2 stk > 0) \<and> (hd stk > 0) then 1 else 0) # tl2 stk)" |
"\<lbrakk> i < size P;  P!i = NOT \<rbrakk> \<Longrightarrow> 
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s, (if hd stk > 0 then 0 else 1) # tl stk)" |
"\<lbrakk> i < size P;  P!i = STORE n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1,s(n := hd stk),tl stk)" |
"\<lbrakk> i < size P;  P!i = JMPF n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1+n,s,stk)" |
"\<lbrakk> i < size P;  P!i = JMPB n;  n \<le> i+1 \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (i+1-n,s,stk)" |
"\<lbrakk> i < size P;  P!i = JMPFZ n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (if hd stk = 0 then i+1+n else i+1,s,tl stk)" |
"\<lbrakk> i < size P;  P!i = JMPFLESS n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (if hd2 stk < hd stk then i+1+n else i+1,s,tl2 stk)" |
"\<lbrakk> i < size P;  P!i = JMPFGE n \<rbrakk> \<Longrightarrow>
 P \<turnstile> (i,s,stk) \<rightarrow> (if hd2 stk >= hd stk then i+1+n else i+1,s,tl2 stk)"

code_pred exec1 .

declare exec1.intros[intro]

inductive exec :: "instr list \<Rightarrow> config \<Rightarrow> config \<Rightarrow> bool" ("_/ \<turnstile> (_ \<rightarrow>*/ _)" 50)
where
refl: "P \<turnstile> c \<rightarrow>* c" |
step: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> P \<turnstile> c' \<rightarrow>* c'' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c''"

declare exec.intros[intro]

lemmas exec_induct = exec.induct[split_format(complete)]

code_pred exec .


text{* Integrating the state to list transformation: *}
inductive execl :: "instr list \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> stack
  \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> stack \<Rightarrow> bool" where
"P \<turnstile> (i,nth ns,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 execl P i ns stk i' (list s' (size ns)) stk'"

code_pred execl .

values "{(i,ns,stk). execl [PUSH_V 1, STORE 0] 0 [3,4] [] i ns stk}"


subsection{* Verification infrastructure *}

lemma exec_trans: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P \<turnstile> c' \<rightarrow>* c'' \<Longrightarrow> P \<turnstile> c \<rightarrow>* c''"
apply(induct rule: exec.induct)
 apply blast
by (metis exec.step)

lemma exec1_subst: "P \<turnstile> c \<rightarrow> c' \<Longrightarrow> c' = c'' \<Longrightarrow> P \<turnstile> c \<rightarrow> c''"
by auto

lemmas exec1_simps = exec1.intros[THEN exec1_subst]

text{* Below we need to argue about the execution of code that is embedded in
larger programs. For this purpose we show that execution is preserved by
appending code to the left or right of a program. *}

lemma exec1_appendR: assumes "P \<turnstile> c \<rightarrow> c'" shows "P@P' \<turnstile> c \<rightarrow> c'"
proof-
  from assms show ?thesis
  by cases (simp_all add: exec1_simps nth_append)
  -- "All cases proved with the final simp-all"
qed

lemma exec_appendR: "P \<turnstile> c \<rightarrow>* c' \<Longrightarrow> P@P' \<turnstile> c \<rightarrow>* c'"
apply(induct rule: exec.induct)
 apply blast
by (metis exec1_appendR exec.step)

lemma exec1_appendL:
assumes "P \<turnstile> (i,s,stk) \<rightarrow> (i',s',stk')"
shows "P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow> (size(P')+i',s',stk')"
proof-
  from assms show ?thesis
  by cases (simp_all add: exec1_simps)
qed

lemma exec_appendL:
 "P \<turnstile> (i,s,stk) \<rightarrow>* (i',s',stk')  \<Longrightarrow>
  P' @ P \<turnstile> (size(P')+i,s,stk) \<rightarrow>* (size(P')+i',s',stk')"
apply(induct rule: exec_induct)
 apply blast
by (blast intro: exec1_appendL exec.step)

text{* Now we specialise the above lemmas to enable automatic proofs of
@{prop "P \<turnstile> c \<rightarrow>* c'"} where @{text P} is a mixture of concrete instructions and
pieces of code that we already know how they execute (by induction), combined
by @{text "@"} and @{text "#"}. Backward jumps are not supported.
The details should be skipped on a first reading.

If the pc points beyond the first instruction or part of the program, drop it: *}

lemma exec_Cons_Suc[intro]:
  "P \<turnstile> (i,s,stk) \<rightarrow>* (j,t,stk') \<Longrightarrow>
  instr#P \<turnstile> (Suc i,s,stk) \<rightarrow>* (Suc j,t,stk')"
apply(drule exec_appendL[where P'="[instr]"])
apply simp
done

lemma exec_appendL_if[intro]:
 "size P' <= i
  \<Longrightarrow> P \<turnstile> (i - size P',s,stk) \<rightarrow>* (i',s',stk')
  \<Longrightarrow> P' @ P \<turnstile> (i,s,stk) \<rightarrow>* (size P' + i',s',stk')"
apply(drule exec_appendL[where P'=P'])
apply simp
done

text{* Split the execution of a compound program up into the excution of its
parts: *}

lemma exec_append_trans[intro]:
"P \<turnstile> (0,s,stk) \<rightarrow>* (i',s',stk') \<Longrightarrow>
 size P \<le> i' \<Longrightarrow>
 P' \<turnstile>  (i' - size P,s',stk') \<rightarrow>* (i'',s'',stk'') \<Longrightarrow>
 j'' = size P + i''
 \<Longrightarrow>
 P @ P' \<turnstile> (0,s,stk) \<rightarrow>* (j'',s'',stk'')"
by(metis exec_trans[OF  exec_appendR exec_appendL_if])


declare Let_def[simp] nat_number[simp]


subsection "Compilation"

fun acomp :: "aexp \<Rightarrow> instr list" where
"acomp (N n) = [PUSH_N n]" |
"acomp (V n) = [PUSH_V n]" |
"acomp (Plus a1 a2) = acomp a1 @ acomp a2 @ [ADD]"

lemma acomp_correct[intro]:
  "acomp a \<turnstile> (0,s,stk) \<rightarrow>* (size(acomp a),s,aval a s#stk)"
apply(induct a arbitrary: stk)
apply(fastsimp)+
done

fun bcomp :: "bexp \<Rightarrow> instr list" where
"bcomp (B True) = [PUSH_N 1]" |
"bcomp (B False) = [PUSH_N 0]" |
"bcomp (Not b) = bcomp b @ [NOT]" |
"bcomp (And b1 b2) = bcomp b1 @ bcomp b2 @ [AND]" |
"bcomp (Less a1 a2) = acomp a1 @ acomp a2 @ [LESS]"

value "bcomp (And (Less (V 0) (V 1)) (Not(Less (V 2) (V 3)))) "

lemma bcomp_correct[intro]:
 "bcomp b \<turnstile> (0,s,stk) \<rightarrow>* (size(bcomp b),s,(if bval b s then 1 else 0)#stk)"
by (induct b arbitrary: stk) fastsimp+


fun ccomp :: "com \<Rightarrow> instr list" where
"ccomp SKIP = []" |
"ccomp (x ::= a) = acomp a @ [STORE x]" |
"ccomp (c1;c2) = ccomp c1 @ ccomp c2" |
"ccomp (IF b THEN c1 ELSE c2) =
  (let cc1 = ccomp c1; cc2 = ccomp c2; cb = bcomp b
   in cb @ [JMPFZ(size cc1 + 1)] @ cc1 @ [JMPF(size cc2)] @ cc2 )" |
"ccomp (WHILE b DO c) =
 (let cc = ccomp c; cb = bcomp b
  in cb @ [JMPFZ(size cc + 1)] @ cc @ [JMPB (size cb + size cc + 2)])"

value "ccomp (IF Less (V 4) (N 1) THEN 4 ::= Plus (V 4) (N 1) ELSE 3 ::= V 4)"

value "ccomp (WHILE Less (V 4) (N 1) DO (4 ::= Plus (V 4) (N 1)))"


subsection "Preservation of sematics"

thm Cons_eq_append_conv self_append_conv2
thm append_take_drop_id drop_1_Cons take_1_Cons
thm append.simps
thm conjI

lemma ccomp_correct:
  "(c,s) \<Rightarrow> t \<Longrightarrow> ccomp c \<turnstile> (0,s,stk) \<rightarrow>* (size(ccomp c),t,stk)"
proof(induct arbitrary: stk rule: big_step_induct)
  case (Assign x a s)
  show ?case by (fastsimp simp:fun_upd_def)
next
  case (Semi c1 s1 s2 c2 s3)
  let ?cc1 = "ccomp c1"  let ?cc2 = "ccomp c2"
  have "?cc1 @ ?cc2 \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cc1,s2,stk)"
    using Semi.hyps(2) by (fastsimp)
  moreover
  have "?cc1 @ ?cc2 \<turnstile> (size ?cc1,s2,stk) \<rightarrow>* (size(?cc1 @ ?cc2),s3,stk)"
    using Semi.hyps(4) by (fastsimp)
  ultimately show ?case by simp (blast intro: exec_trans)
next
  case (WhileTrue b s1 c s2 s3)
  let ?cc = "ccomp c"
  let ?cb = "bcomp b"
  let ?cw = "ccomp(WHILE b DO c)"
  let ?i = "Suc (size ?cb + size ?cc)"
  let ?i' = "(size ?cb + 1 + size ?cc)"
  have "?cw \<turnstile> (0,s1,stk) \<rightarrow>* (size ?cb + 1 + size ?cc,s2,stk)"
    using WhileTrue(1,3) by fastsimp
  moreover
  have "?cw \<turnstile> (size ?cb + 1 + size ?cc,s2,stk) \<rightarrow>* (0,s2,stk)"
  proof -
    have 0: "size (bcomp b @ JMPFZ (Suc (length (ccomp c))) # ccomp c) = ?i" by simp
    have 1: "(bcomp b @ JMPFZ (Suc (length (ccomp c))) # ccomp c) = (bcomp b @ [JMPFZ (Suc (length (ccomp c)))] @ ccomp c)" by simp
    from 0 1 have "?cw ! ?i = JMPB (?i' + 1)" 

    from this have "?cw \<turnstile> (size ?cb + 1 + size ?cc,s2,stk) \<rightarrow> (?i + 1 - Suc ?i,s2,stk)"
      apply auto
      
      proof -


.

bcomp b @
    JMPFZ (Suc (length (ccomp c))) #
    ccomp c @ [JMPB (Suc (Suc (length (bcomp b) + length (ccomp c))))]
    \<turnstile> (Suc (length (bcomp b) + length (ccomp c)), s2, stk) \<rightarrow>* (0, s2, stk)

(*

    proof -
      have "size(bcomp b @ JMPFZ (Suc (length (ccomp c))) # ccomp c) = 
              (Suc (length (bcomp b) + length (ccomp c)))" by simp
      moreover
      from this  have foo: "?cw ! ?i = JMPB (Suc ?i)" sorry
      moreover
      have "length ?cw = (Suc (Suc (length (bcomp b) + length (ccomp c))))" by simp
      ultimately
      have "ccomp (WHILE b DO c) \<turnstile> (length (bcomp b) + 1 + length (ccomp c), s2, stk) \<rightarrow> (0, s2, stk)" apply (auto simp add: algebra_simps) sorry

      have " ?cw \<turnstile> (?i, s2, stk) \<rightarrow> (?i + 1 - (Suc ?i), s2, stk) "
       apply (rule exec1.intros(9))
       apply (auto)
       apply (rule foo)
      proof 
        have "ccomp (WHILE b DO c) ! Suc (length (bcomp b) + length (ccomp c)) =
    JMPB (Suc (Suc (length (bcomp b) + length (ccomp c))))" by (rule foo)
        thus ?thesis by auto
      qed
        apply (fastsimp add: foo)

        apply 
        apply auto

        thm exec1.intros(9) 
        sorry
      have " foo  \<turnstile> (j, s2, stk) \<rightarrow> (j + 1 - n, s2, stk)"
       apply (rule exec1.intros(9))
      show ?thesis apply auto

    bcomp b @
    JMPFZ (Suc (length (ccomp c))) #
    ccomp c @ [JMPB (Suc (Suc (length (bcomp b) + length (ccomp c))))]
    \<turnstile> (Suc (length (bcomp b) + length (ccomp c)), s2, stk) \<rightarrow> ((Suc (length (bcomp b) + length (ccomp c))) + 1 - (Suc (Suc (length (bcomp b) + length (ccomp c)))), s2, stk)

    bcomp b @
    JMPFZ (Suc (length (ccomp c))) #
    ccomp c @ [JMPB (Suc (Suc (length (bcomp b) + length (ccomp c))))]
    \<turnstile> (Suc (length (bcomp b) + length (ccomp c)), s2, stk) \<rightarrow> (0, s2, stk)


    apply auto
    by (fastsimp) *)
  moreover
  have "?cw \<turnstile> (0,s2,stk) \<rightarrow>* (size ?cw,s3,stk)" by(rule WhileTrue(5))
  ultimately show ?case by(blast intro: exec_trans)
qed fastsimp+

end
