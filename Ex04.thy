header "Excercise Sheet 4 - Nikolaus Demmel"

theory Ex04
imports Inductive_Demo
begin



subsection{* Ex 4.1 *}

lemma steps_right: "[| x ->* y; y -> z |] ==> x ->* z"
apply (induct rule: steps.induct)
apply (rule steps_if_step)
apply assumption
apply (rule step)
apply assumption
apply assumption
done

lemma steps_right2: "[| x ->* y; y -> z |] ==> x ->* z"
proof (induct rule: steps.induct)
  case refl
  thus ?case by (rule steps_if_step)
next
  case (step _ y')
  from step(3-4) have "y' ->* z" by simp
  from step(1) and this show ?case by (rule steps.step)
qed



subsection{* Ex 4.2 *}

inductive palindrome :: "nat list => bool" where
palin0: "palindrome []" |
palin1: "palindrome [_]" |
palin_step: "palindrome xs ==> palindrome (a # xs @ [a])" 

declare palindrome.intros[simp]

lemma palindrome_rev: "palindrome xs <-> (rev xs = xs)"
proof 
  assume "palindrome xs"
  then
  show "rev xs = xs"
    by (induct xs rule: palindrome.induct) auto
next
  assume "rev xs = xs"
  then
  show "palindrome xs"
  proof (induct xs rule: length_induct)
    fix xs :: "nat list"
    assume rev: "rev xs = xs"
    assume IH: "\<forall> ys. length ys < length xs \<longrightarrow> rev ys = ys \<longrightarrow> palindrome ys"
    
    have "xs = [] \<or> (\<exists> a. xs = [a]) \<or> (\<exists> a b zs. xs = a # zs @ [b])"
      by (metis append_butlast_last_id drop_0 drop_Suc_conv_tl length_greater_0_conv)
    moreover
    {
      fix a b zs assume xs: "xs = a # zs @ [b]"
      from rev have "a = b"
        by (simp only: xs rev.simps rev_append append.simps) (metis list.inject)
      have "palindrome xs" using rev IH xs `a = b` by simp
    }
    ultimately
    show "palindrome xs" by auto
  qed
qed

end
