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

(* NOTE: is "\<lbrakk> A1 ; A2 ; ... \<rbrakk> \<Rightarrow> Conclustion" the correct style for inductive defs? *)

declare t.intros[simp, intro] (* NOTE: isn't 'intro' default for these? *)
declare s.intros[simp, intro]



section "Part (b)"


subsection "A lemma in apply style and then isar style"

(* Apply style proof of simple lemma *)
lemma t_conc: "\<lbrakk> t ys ; t xs \<rbrakk> \<Longrightarrow> t (xs @ ys)"
apply (induct ys rule: t.induct)
(* NOTE: why cant i swap ys and xs in the assumption for the induct to work? *)
apply auto
apply (metis Cons_eq_appendI append_assoc append_self_conv2 t.intros(2))
done

(* Same lemma as above, now with isar proof *)
lemma "\<lbrakk> t ys ; t xs \<rbrakk> \<Longrightarrow> t (xs @ ys)"
proof (induct ys rule: t.induct)
  case t1 thus ?case by simp
next
  case t2
  thus ?case by (metis Cons_eq_appendI append_assoc append_self_conv2 t.intros(2))
qed

(* NOTE: why does this not work?
lemma
fixes xs ys
assumes "t ys" "t xs"
shows "t (xs @ ys)"
proof (induct ys rule: t.induct) *)


subsection "Now the requested theorem with two proofs"

(* Apply style proof first *)
theorem "s xs = t xs"
(* NOTE: How would I proceed if I wanted to show "s = t" without the parameter? *)
apply auto
apply (induct xs rule: s.induct)
apply (rule t1)
apply (metis Cons_eq_append_conv eq_Nil_appendI t.intros)
apply (simp add: t_conc)
apply (induct xs rule: t.induct)
apply auto
done

(* Same theorem as above, now with isar proof *)
theorem
fixes xs
shows "s xs = t xs"
proof
  assume "s xs"
  then show "t xs"
  proof (induct rule: s.induct)
    case s1 thus ?case by (rule t1)
  next
    case s2
    thus ?case by (metis Cons_eq_append_conv eq_Nil_appendI t.intros)
  next
    (* ALTERNATIVE 1: use lemma            *)
    (* case (s3 xs ys)                     *)
    (* thus ?case by (simp add: t_conc)    *)
    (* ALTERNATIVE 2: use inline sub-proof *)
    fix xs ys
    assume "t ys" "t xs"
    then show "t (xs @ ys)"
    (* NOTE: again we have to spell out the case manually to have the "t ys" assumption 
       appear first. Also including additional assumptions like "s xs" "s ys" also 
       makes the induct proof fail. I don't quite undestand... *)
    proof (induct ys rule: t.induct) 
      case t1 thus ?case by simp
    next
      case t2
      thus ?case by (metis Cons_eq_appendI append_assoc append_self_conv2 t.intros(2))
    qed
  qed
next
  assume "t xs"
  then show "s xs"
    by (induct rule: t.induct) auto
qed

end
