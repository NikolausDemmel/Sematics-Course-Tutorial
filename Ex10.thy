theory Ex10_Template
imports Sec_Typing
begin

inductive sec_type2' :: "com \<Rightarrow> level \<Rightarrow> bool" ("(\<turnstile>' _ : _)" [0,0] 50) where
Skip2':
  "\<turnstile>' SKIP : l" |
Assign2':
  "sec x \<ge> sec a \<Longrightarrow> \<turnstile>' x ::= a : sec x" |
Semi2':
  "\<lbrakk> \<turnstile>' c\<^isub>1 : l;  \<turnstile>' c\<^isub>2 : l \<rbrakk> \<Longrightarrow> \<turnstile>' c\<^isub>1;c\<^isub>2 : l" |
If2':
  "\<lbrakk> sec b \<le> min l\<^isub>1 l\<^isub>2;  \<turnstile>' c\<^isub>1 : l\<^isub>1;  \<turnstile>' c\<^isub>2 : l\<^isub>2 \<rbrakk>
  \<Longrightarrow> \<turnstile>' IF b THEN c\<^isub>1 ELSE c\<^isub>2 : min l\<^isub>1 l\<^isub>2" |
While2':
  "\<lbrakk> sec b \<le> l;  \<turnstile>' c : l \<rbrakk> \<Longrightarrow> \<turnstile>' WHILE b DO c : l"


lemma "\<turnstile> c : l \<Longrightarrow> \<turnstile>' c : l"
oops


lemma "\<turnstile>' c : l \<Longrightarrow> \<exists>l' \<ge> l. \<turnstile> c : l'"
oops


end
