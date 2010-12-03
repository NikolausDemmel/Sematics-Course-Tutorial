theory Ex06
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
proof (induct rule: small_steps.induct)
qed (blast intro: n_steps.intros)+


lemma n_small_steps: "cs \<rightarrow>^n cs' \<Longrightarrow> cs \<rightarrow>* cs'"
proof (induct rule: n_steps.induct)
qed (blast intro: step)+


definition
  small_step_equiv :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<approx>" 50) where
  "c \<approx> c' == (\<forall>s t n. (c,s) \<rightarrow>^n (SKIP, t)  =  (c', s) \<rightarrow>^n (SKIP, t))"


lemma small_eqv_implies_big_eqv: "c \<approx> c' \<Longrightarrow> c \<sim> c'"
proof -
  assume "c \<approx> c'"
  {
    fix s t c c'
    assume "c \<approx> c'" "(c, s) \<Rightarrow> t"
    then have "(c,s) \<rightarrow>* (SKIP,t)" by (simp add: big_to_small)
    with small_steps_n  obtain n where "(c,s) \<rightarrow>^n (SKIP, t)" by blast
    with `c \<approx> c'` small_step_equiv_def have "(c',s) \<rightarrow>^n (SKIP, t)" by auto
    with n_small_steps have "(c',s) \<rightarrow>* (SKIP, t)" by auto
    then have "(c', s) \<Rightarrow> t" by (rule small_to_big)
  }
  moreover
  have "(c \<approx> c') = (c' \<approx> c)" by (auto simp add: small_step_equiv_def)
  ultimately  have 
    "\<And>s t. \<lbrakk> c \<approx> c' ; (c ,s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (c',s) \<Rightarrow> t" and 
    "\<And>s t. \<lbrakk> c \<approx> c' ; (c',s) \<Rightarrow> t \<rbrakk> \<Longrightarrow> (c ,s) \<Rightarrow> t" 
    by blast+ 
  with `c \<approx> c'` show "c \<sim> c'" by blast
qed

end
