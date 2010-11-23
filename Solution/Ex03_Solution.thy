theory Ex03_Solution
imports BExp
begin

section {* Ex. 3.1 -- Boolean If expression *}

datatype ifexp = B bool | If ifexp ifexp ifexp | Less aexp aexp

primrec ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (B b) _ = b" |
"ifval (If b1 b2 b3) st = (if ifval b1 st then ifval b2 st else ifval b3 st)" |
"ifval (Less a\<^isub>1 a\<^isub>2) st = (aval a\<^isub>1 st < aval a\<^isub>2 st)"

fun Or :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"Or b1 b2 = Not (And (Not b1) (Not b2))"

fun If_bexp :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"If_bexp b1 b2 b3 = Or (And b1 b2) (And (Not b1) b3)"

primrec translate :: "ifexp \<Rightarrow> bexp" where
"translate (B b) = (bexp.B b)" |
"translate (If b1 b2 b3) =
  If_bexp (translate b1) (translate b2) (translate b3)" |
"translate (Less a1 a2) = bexp.Less a1 a2"

lemma translate_sound: "bval (translate exp) s = ifval exp s"
by (induct exp) auto

section {* Ex. 3.2 -- More Arithmetic Constructs *}

text {* to avoid name clashes, we call the type @{text "amexp"}.*}

datatype amexp = N nat | V name | Plus amexp amexp | Times amexp amexp

fun amval :: "amexp \<Rightarrow> state \<Rightarrow> nat" where
"amval (N n) _ = n" |
"amval (V x) st = st x" |
"amval (Plus e1 e2) st = amval e1 st + amval e2 st" |
"amval (Times e1 e2) st = amval e1 st * amval e2 st"

text {* We must repeat this definition literally, since the old one is
on a different type *}

fun plus :: "amexp \<Rightarrow> amexp \<Rightarrow> amexp" where
"plus (N 0) e = e" |
"plus e (N 0) = e" |
"plus (N n1) (N n2) = N(n1+n2)" |
"plus e1 e2 = Plus e1 e2"

lemma amval_plus[simp]:
  "amval (plus e1 e2) st = amval e1 st + amval e2 st"
apply (induct e1 e2 rule: plus.induct)
apply auto
done

text {* Now the same for @{text Times}: We eliminate zero and
one. Since 1 is not a constructor (Natural numbers are built from zero
and successor), we must write @{term "Suc 0"}.
*}

fun times :: "amexp \<Rightarrow> amexp \<Rightarrow> amexp" where
"times (N 0) e = N 0" |
"times e (N 0) = N 0" |
"times (N (Suc 0)) e = e" |
"times e (N (Suc 0)) = e" |
"times (N n1) (N n2) = N (n1 * n2)" |
"times e1 e2 = Times e1 e2"

fun amsimp :: "amexp \<Rightarrow> amexp" where
"amsimp (N n) = N n" |
"amsimp (V x) = V x" |
"amsimp (Plus e1 e2) = plus (amsimp e1) (amsimp e2)" |
"amsimp (Times e1 e2) = times (amsimp e1) (amsimp e2)"

lemma amval_times[simp]: "amval (times e1 e2) st = amval (Times e1 e2) st"
apply (induct e1 e2 rule: times.induct)
apply auto
done

lemma "amval (amsimp e) st = amval e st"
apply (induct e)
apply auto
done

section {* Homework -- Let expressions *}

datatype lexp = N nat | V name | Plus lexp lexp | Let name lexp lexp

primrec lval where
"lval (N n) st = n" |
"lval (V x) st = st x" |
"lval (Plus e\<^isub>1 e\<^isub>2) st = lval e\<^isub>1 st + lval e\<^isub>2 st" |
"lval (Let x e1 e2) st = lval e2 (st(x:=lval e1 st))"

section {* One solution: translation into aexps *}

primrec subst where
"subst y e (aexp.N n) = aexp.N n" |
"subst y e (aexp.V x) = (if x = y then e else aexp.V x)" |
"subst y e (aexp.Plus e1 e2) = aexp.Plus (subst y e e1) (subst y e e2)"

primrec inline where
"inline (N n) = aexp.N n" |
"inline (V x) = aexp.V x" |
"inline (Plus e1 e2) = aexp.Plus (inline e1) (inline e2)" |
"inline (Let x e1 e2) = subst x (inline e1) (inline e2)"

lemma val_subst: "aval (subst x e e') st = aval e' (st(x:=aval e st))"
by (induct e') auto

lemma val_inline: "aval (inline e) st = lval e st"
by (induct e arbitrary: st) (auto simp: val_subst)

subsection {* Another solution: translate to lexps without occurrence of Let *}

text {* NB: Substituting an expression @{term e} for a variable @{term
y} in an expression @{term e'} is very difficult when @{term e'} contains Let.
This is because free variables in @{term e} may become bound accidentally.
Thus, the last equation of the following definition does not really work:
*}

primrec subst' :: "name \<Rightarrow> lexp \<Rightarrow> lexp \<Rightarrow> lexp" where
"subst' y e (N n) = N n" |
"subst' y e (V x) = (if x = y then e else V x)" |
"subst' y e (Plus e1 e2) = Plus (subst' y e e1) (subst' y e e2)" |
"subst' y e (Let x e1 e2) = 
  (if x = y then Let x (subst' y e e1) e2 
            else Let x (subst' y e e1) (subst' y e e2))"

lemma "lval (Let x e e') st = lval (subst' x e e') st"
quickcheck (* does not hold: quickcheck finds a counterexample that illustrates the variable-capture problem *)
oops

text {* However, the function above works as long as @{term e'} is
let-free, which we define as follows: *}

primrec let_free :: "lexp \<Rightarrow> bool" where
"let_free (N _) = True" |
"let_free (V _) = True" |
"let_free (Plus e1 e2) = (let_free e1 \<and> let_free e2)" |
"let_free (Let _ _ _) = False"

lemma val_subst': "let_free e' \<Longrightarrow> lval (subst' x e e') st = lval (Let x e e') st"
by (induct e') auto

lemma let_free_subst': "let_free e \<Longrightarrow> let_free e' \<Longrightarrow> let_free (subst' x e e')"
by (induct e') auto

text {* Remark: The following function uses @{term "subst'"} on let-free expressions only,
  which lets us work around the variable-capture problem.
  Generalizing it to inline only some of the Lets instead of all would therefore be
  really non-trivial.
*}

primrec inline' :: "lexp \<Rightarrow> lexp" where
"inline' (N n) = N n" |
"inline' (V x) = V x" |
"inline' (Plus e1 e2) = Plus (inline' e1) (inline' e2)" |
"inline' (Let x e1 e2) = subst' x (inline' e1) (inline' e2)"

lemma inline'_let_free: "let_free (inline' e)"
by (induct e) (auto simp: let_free_subst')

lemma val_inline': "lval (inline' e) st = lval e st"
by (induct e arbitrary: st) (auto simp: val_subst' inline'_let_free)

text {* Remark: An interesting variation is to define @{term subst'} such that
@{prop "subst' y e (Let x e1 e2) = Let y e (Let x e1 e2)"}. Then lemma
@{text "val_subst'"} above holds without the precondition.
*}


subsection {* c) eliminating useless Lets *}

primrec occurs :: "name \<Rightarrow> lexp \<Rightarrow> bool" where
"occurs x (N _) = False" |
"occurs x (V y) = (x = y)" |
"occurs x (Plus e1 e2) = (occurs x e1 \<or> occurs x e2)" |
"occurs x (Let y e1 e2) = (occurs x e1 \<or> (x \<noteq> y \<and> occurs x e2))"

primrec elim_useless where
"elim_useless (N n) = N n" |
"elim_useless (V x) = V x" |
"elim_useless (Plus e1 e2) = Plus (elim_useless e1) (elim_useless e2)" |
"elim_useless (Let x e1 e2) = 
  (if occurs x e2 
    then Let x (elim_useless e1) (elim_useless e2) 
    else elim_useless e2)"

lemma occurs_lval: "\<not> occurs x e \<Longrightarrow> lval e (st(x:=v)) = lval e st"
apply (induct e arbitrary: st)
apply auto
by (metis fun_upd_twist fun_upd_upd lval.simps(4)) (* found by sledgehammer *)

lemma "lval (elim_useless e) st = lval e st"
by (induct e arbitrary: st) (auto simp: occurs_lval)

end
