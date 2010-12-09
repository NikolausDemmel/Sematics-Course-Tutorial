theory Ex06_Template
imports Small_Step
begin

inductive
 n_steps :: "com * state \<Rightarrow> nat \<Rightarrow> com * state \<Rightarrow> bool" 
 ("_ \<rightarrow>^_ _" [60,1000,60]999)
where
 zero_steps: "cs \<rightarrow>^0 cs" |
 one_step: "cs \<rightarrow> cs' \<Longrightarrow> cs' \<rightarrow>^n cs'' \<Longrightarrow> cs \<rightarrow>^(Suc n) cs''"

inductive_cases zero_stepsE[elim!]: "cs \<rightarrow>^0 cs'"
thm zero_stepsE
inductive_cases one_stepE[elim!]: "cs \<rightarrow>^(Suc n) cs''"
thm one_stepE


lemma small_steps_n: "cs \<rightarrow>* cs' \<Longrightarrow> (\<exists>n. cs \<rightarrow>^n cs')"
by (induct rule: small_steps.induct) (auto intro: n_steps.intros)

lemma n_small_steps: "cs \<rightarrow>^n cs' \<Longrightarrow> cs \<rightarrow>* cs'"
apply (induct n arbitrary: cs cs')
apply (auto intro: small_steps.intros)
done


definition
 small_step_equiv :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<approx>" 50) where
 "c \<approx> c' == (\<forall>s t n. (c,s) \<rightarrow>^n (SKIP, t)  =  (c', s) \<rightarrow>^n (SKIP, t))"

lemma small_eqv_implies_big_eqv: "c \<approx> c' \<Longrightarrow> c \<sim> c'"
proof -
 assume "c \<approx> c'"

 {
   fix s t
   assume "(c, s) \<Rightarrow> t"
   then have "(c, s) \<rightarrow>* (SKIP, t)" by (rule big_to_small)
   with small_steps_n obtain n where "(c,s) \<rightarrow>^n (SKIP, t)"
     by blast
   with `c \<approx> c'` have "(c',s) \<rightarrow>^n (SKIP, t)"
     by (auto simp: small_step_equiv_def)
   then have "(c',s) \<rightarrow>* (SKIP, t)"
     by (rule n_small_steps)
   then have "(c', s) \<Rightarrow> t" by (rule small_to_big)
 }
 moreover
 {
   fix s t
   assume "(c', s) \<Rightarrow> t"
   have "(c, s) \<Rightarrow> t"
     sorry
 }
 ultimately
 show "c \<sim> c'" by blast
qed



oops

end
