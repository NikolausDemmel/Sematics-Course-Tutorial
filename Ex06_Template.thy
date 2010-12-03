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
oops

lemma n_small_steps: "cs \<rightarrow>^n cs' \<Longrightarrow> cs \<rightarrow>* cs'"
oops


definition
  small_step_equiv :: "com \<Rightarrow> com \<Rightarrow> bool" (infix "\<approx>" 50) where
  "c \<approx> c' == (\<forall>s t n. (c,s) \<rightarrow>^n (SKIP, t)  =  (c', s) \<rightarrow>^n (SKIP, t))"

lemma small_eqv_implies_big_eqv: "c \<approx> c' \<Longrightarrow> c \<sim> c'"
oops

end

