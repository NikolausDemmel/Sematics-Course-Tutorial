header "Homework Sheet 4 - Nikolaus Demmel"

theory Hw04
imports Main
begin



section "Part (a)"

datatype symbol = A | B

inductive s :: "symbol list \<Rightarrow> bool"
where
  s1: "s []"
| s2: "s xs \<Longrightarrow> s (A # xs @ [B])"
| s3: "\<lbrakk>s xs ; s ys\<rbrakk> \<Longrightarrow> s (xs @ ys)"

inductive t :: "symbol list \<Rightarrow> bool"
where
  t1: "t []"
| t2: "\<lbrakk>t xs ; t ys\<rbrakk> \<Longrightarrow> t (xs @ [A] @ ys @ [B])"

declare t.intros[simp, intro] (* isn't 'intro' default for these? *)
declare s.intros[simp, intro]



section "Part (b)"

(* why cant i swap ys and xs in the assumption for the induct to work? *)
lemma t_conc: "\<lbrakk> t ys ; t xs \<rbrakk> \<Longrightarrow> t (xs @ ys)"
apply (induct ys rule: t.induct)
apply auto
by (metis Cons_eq_appendI append_assoc append_self_conv2 t.intros(2))
 
(* TODO: show lemma with isar-style proof or proof it inline in the proof below
lemma t_conc:
fixes xs ys
assumes "t xs" "t ys"
shows "t (xs @ ys)"
proof (induct ys rule: t.induct)
  assume "xs = []" 
  with `t ys` show ?thesis by auto
next
  fix x xs' assume "xs = x # xs'"
sorry
*)

theorem "s xs = t xs"
apply auto
apply (induct xs rule: s.induct)
apply (rule t.intros(1))
apply (metis Cons_eq_append_conv eq_Nil_appendI t.intros)
apply (simp add: t_conc)
apply (induct xs rule: t.induct)
apply auto
done

theorem
fixes xs
shows "s xs = t xs"
proof
  assume "s xs"
  then show "t xs"
  proof (induct rule: s.induct)
    case s1 thus ?case by simp
  next
    case (s2 xs)
    thus ?case by (metis Cons_eq_append_conv eq_Nil_appendI t.intros)
  next
    case (s3 xs ys)
    thus ?case by (simp add: t_conc) (* TODO: dont use lemma, add sub proof *)
  qed
next
  assume "t xs"
  then show "s xs"
    by (induct rule: t.induct) auto
qed