header "Arithmetic and Boolean Expressions"

theory AExp imports Main begin

subsection "Arithmetic Expressions"

types
  name = nat --"For simplicity in examples"
  state = "name \<Rightarrow> nat"

datatype aexp = N nat | V name | Plus aexp aexp

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> nat" where
"aval (N n) _ = n" |
"aval (V x) st = st x" |
"aval (Plus e\<^isub>1 e\<^isub>2) st = aval e\<^isub>1 st + aval e\<^isub>2 st"

text{* Subscripts are for visual beauty only! *}

value "aval (Plus (V 0) (N 5)) (nth [2,1])"


subsection "Optimization"

text{* Evaluate constant subsexpressions: *}

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V x) = V x" |
"asimp_const (Plus e1 e2) =
  (case (asimp_const e1, asimp_const e2) of
    (N n1, N n2) \<Rightarrow> N(n1+n2) |
    (e1',e2') \<Rightarrow> Plus e1' e2')"

theorem aval_asimp_const[simp]:
  "aval (asimp_const a) st = aval a st"
apply(induct a)
apply (auto split: aexp.split)
done

text{* Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors: *}

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N 0) e = e" |
"plus e (N 0) = e" |
"plus (N n1) (N n2) = N(n1+n2)" |
"plus e1 e2 = Plus e1 e2"

lemma aval_plus[simp]:
  "aval (plus e1 e2) st = aval e1 st + aval e2 st"
apply(induct e1 e2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus e1 e2) = plus (asimp e1) (asimp e2)"

text{* Note that in @{const asimp_const} the optimized constructor was
inlined. Making it a separate function @{const plus} improves modularity of
the code and the proofs. *}

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V 5) (N 0)))"

theorem aval_asimp[simp]:
  "aval (asimp a) st = aval a st"
apply(induct a)
apply simp_all
done

end
