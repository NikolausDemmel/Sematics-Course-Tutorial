theory BExp imports AExp begin

subsection "Boolean Expressions"

datatype bexp = B bool | Not bexp | And bexp bexp | Less aexp aexp

primrec bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (B b) _ = b" |
"bval (Not b) st = (\<not> bval b st)" |
"bval (And b1 b2) st = (if bval b1 st then bval b2 st else False)" |
"bval (Less a1 a2) st = (aval a1 st < aval a2 st)"

value "bval (Less (V 1) (Plus (N 3) (V 0))) (nth [1,3])"


subsection "Optimization"

text{* Optimized constructors: *}

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = B(n1 < n2)" |
"less a1 a2 = Less a1 a2"

lemma [simp]: "bval (less a1 a2) st = (aval a1 st < aval a2 st)"
apply(induct a1 a2 rule: less.induct)
apply simp_all
done

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (B True) b = b" |
"and b (B True) = b" |
"and (B False) b = B False" |
"and b (B False) = B False" |
"and b1 b2 = And b1 b2"

lemma bval_and[simp]: "bval (and b1 b2) st = (bval b1 st & bval b2 st)"
apply(induct b1 b2 rule: and.induct)
apply simp_all
done

fun not :: "bexp \<Rightarrow> bexp" where
"not (B True) = B False" |
"not (B False) = B True" |
"not b = Not b"

lemma bval_not[simp]: "bval (not b) st = (~bval b st)"
apply(induct b rule: not.induct)
apply simp_all
done

text{* Now the overall optimizer: *}

fun bsimp :: "bexp \<Rightarrow> bexp" where
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (B bv) = B bv"

value "bsimp (And (Less (N 0) (N 1)) b)"

value "bsimp (And (Less (N 1) (N 0)) (B True))"

theorem "bval (bsimp b) st = bval b st"
apply(induct b)
apply simp_all
done

end
