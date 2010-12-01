theory Ex04_Solution
imports Inductive_Demo
begin

subsection {* Ex. 4.1 *}

lemma steps_right_apply_style:"\<lbrakk> x \<rightarrow>* y; y \<rightarrow> z \<rbrakk>  \<Longrightarrow> x \<rightarrow>* z"
apply (induct rule: steps.induct)
apply (blast intro: steps_if_step)
apply (blast intro: steps.step)
done

(* Alternative: Single steps instead of blast *)
lemma "\<lbrakk> x \<rightarrow>* y; y \<rightarrow> z \<rbrakk>  \<Longrightarrow> x \<rightarrow>* z"
apply (induct rule: steps.induct)
apply (rule steps_if_step)
apply assumption
apply (rule steps.step)
apply assumption
apply assumption
done

(* Isar *)
lemma steps_right: "\<lbrakk> x \<rightarrow>* y; y \<rightarrow> z \<rbrakk>  \<Longrightarrow> x \<rightarrow>* z"
(*<*)
proof (induct rule: steps.induct)
  case refl
  thus ?case by (rule steps_if_step)
next
  case step
  thus ?case by (blast intro: steps.step)
qed
(*>*)


subsection {* Ex 4.2 *}

inductive palindrome :: "nat list \<Rightarrow> bool"
where
  "palindrome []"
| "palindrome [a]"
| "palindrome xs \<Longrightarrow> palindrome (a#xs@[a])"


lemma palindrome_rev: "palindrome xs \<longleftrightarrow> (rev xs = xs)"
proof 
  assume "palindrome xs" 
  then show "rev xs = xs"
    by (induct xs rule: palindrome.induct) auto
next
  assume "rev xs = xs"
  then show "palindrome xs"
  proof (induct xs rule: measure_induct_rule[of length])
    fix xs :: "nat list" assume rev: "rev xs = xs"
    and IH: "\<And>ys. \<lbrakk> length ys < length xs; rev ys = ys\<rbrakk> \<Longrightarrow> palindrome ys"
    have "xs = [] \<or> (\<exists>a. xs = [a]) \<or> (\<exists>a b ys. xs = a # ys @ [b])"
      by (metis append_butlast_last_id append_eq_Cons_conv rev.simps(2) rev_swap)
    moreover
    {
      fix a b and ys assume xs: "xs = a#ys@[b]"

      from xs have "length ys < length xs" by auto

      moreover
      from rev
      have "rev ys = ys"
        unfolding xs
        by auto

      ultimately
      have "palindrome ys" by (rule IH)

      moreover
      from rev
      have "a = b"
        unfolding xs
        unfolding rev.simps rev_append append.simps
        unfolding list.inject
        by blast

      ultimately
      have "palindrome xs" unfolding xs
        by (blast intro: palindrome.intros)
    }
    ultimately
    show "palindrome xs" by (auto intro: palindrome.intros)
  qed
qed

subsection {* Homework *}

datatype symbol = A | B

inductive_set S :: "symbol list set"
where
  S1[iff]: "[] : S"
| S2[intro!, simp]: "w : S \<Longrightarrow> A#w@[B] : S"
| S3: "v : S \<Longrightarrow> w : S \<Longrightarrow> v @ w : S"


inductive_set T :: "symbol list set"
where
  T1[iff]: "[] : T"
| T23: "v : T \<Longrightarrow> w : T \<Longrightarrow> v @ A # w @ [B]: T"


text {* We dont declare any [intro] or [simp] globally.
Then it is actually visible below which rule is used where. *}

text {* @{text T} is a subset of @{text S} *}

lemma T2S: "w : T \<Longrightarrow> w : S"
by (induct rule: T.induct)
 (auto intro: S3)

text {* @{text S} is a subset of @{text T} *}

lemma T2: "w : T \<Longrightarrow> A#w@[B] : T"
using T23[where v = "[]"] by simp

lemma T3: "v : T \<Longrightarrow> u : T \<Longrightarrow> u@v : T"
apply (induct rule: T.induct)
apply auto
by (metis T23 append_eq_appendI)

lemma S2T: "w : S \<Longrightarrow> w : T"
by (induct rule: S.induct) (auto intro: T2 T3)


subsection{* @{text"S = T"} *}

lemma "S = T"
by(blast intro: S2T T2S)

end

