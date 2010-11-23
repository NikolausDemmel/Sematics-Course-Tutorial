theory Inductive_Demo
imports Main
begin

subsection{*Inductive definition of the even numbers*}

inductive Ev :: "nat => bool" where
Ev0: "Ev 0" |
EvSS: "Ev n ==> Ev (Suc(Suc n))"

thm Ev0 EvSS
thm Ev.intros

text{* Using the introduction rules: *}
lemma "Ev (Suc(Suc(Suc(Suc 0))))"
apply(rule EvSS)
apply(rule EvSS)
apply(rule Ev0)
done

thm EvSS[OF Ev0]

thm EvSS[OF EvSS[OF Ev0]]

text{*A simple inductive proof: *}
lemma "Ev n ==> Ev (n+n)"
apply(induct rule: Ev.induct)
 apply(simp)
 apply(rule Ev0)
apply(simp)
apply(rule EvSS)
apply(rule EvSS)
apply(assumption)
done

text{* No problem with termination because the premises are always smaller
than the conclusion: *}
declare Ev.intros[simp]

text{* A shorter proof: *}

lemma "Ev n ==> Ev(n+n)"
apply(induct rule: Ev.induct)
apply(auto)
done

text{* Nice example, but overkill: don't need assumption @{prop"Ev n"}
because @{prop"Ev (n+n)"} is true for all @{text n}. However,
@{prop"Ev n ==> Ev(n+n+n)"} really does need the assmption. *}

text{* The power of arith: *}
lemma "Ev n ==> EX k. n = 2*k"
apply(induct rule: Ev.induct)
 apply(simp)
apply arith
done


subsection{*Inductive definition of the reflexive transitive closure *}

consts step :: "'a => 'a => bool" (infix "->" 55)

inductive steps :: "'a => 'a => bool" (infix "->*" 55) where
refl: "x ->* x" |
step: "[| x -> y; y ->* z  |] ==> x ->* z"

text{* Let refl be used automatically by simp and blast: *}
declare refl[simp, intro]

lemma steps_if_step: "x -> y ==> x ->* y"
by(rule step[OF _ refl])

lemma steps_trans: "[| x ->* y; y ->* z  |] ==> x ->* z"
apply(induct rule: steps.induct)
apply assumption
apply(rule step)
apply assumption
apply assumption
done
(* Variations: use blast and sledgehammer *)

end
