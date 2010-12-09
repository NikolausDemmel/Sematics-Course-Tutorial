
theory Palindrome
imports Main
begin

inductive palindrome :: "nat list \<Rightarrow> bool"
where
 "palindrome []"
| "palindrome [a]"
| "palindrome xs \<Longrightarrow> palindrome (a#xs@[a])"


lemma "palindrome xs \<longleftrightarrow> rev xs = xs"
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
   assume IH: "\<forall>ys. length ys < length xs 
    \<longrightarrow> rev ys = ys \<longrightarrow> palindrome ys"

   have "xs = [] \<or> (\<exists>a. xs = [a]) \<or> (\<exists>a b zs. xs = a # zs @ [b])"
     by (metis append_butlast_last_id append_eq_Cons_conv rev.simps(2) rev_swap)

   {
     fix a b zs assume xs: "xs = a # zs @ [b]"
     from rev
     have "a = b"
       apply (simp only: xs)
       apply (simp only: rev.simps rev_append append.simps)
       by (metis list.inject)




   show "palindrome xs"

end
