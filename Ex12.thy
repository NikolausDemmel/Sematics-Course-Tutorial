header "Semantics exercices and homework sheet 12 - Nikolaus Demmel"

theory Ex12
imports "../Thys/VC" GCD
begin

section {* A nicer notation for annotated programs *}

notation Askip ("SKIP")
notation Aassign ("_ #= _" [1000, 61] 61)
notation Asemi ("_;;/ _"  [60, 61] 60)
notation Aif ("(IF' _/ THEN _/ ELSE _)"  [0, 0, 61] 61)
notation Awhile ("(WHILE' _/ _/ DO _)"  [0, 61] 61)


text {* A convenient loop construct: *}

abbreviation Afor :: "name \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> assn \<Rightarrow> acom \<Rightarrow> acom"
  ("(FOR _/ FROM _/ TO _/ _/ DO _)"  [0, 0, 0, 0, 61] 61) where
  "FOR v FROM a1 TO a2 b DO c \<equiv>
     (v #= a1 ;; WHILE' (Less (V v) a2) b DO (c ;; v #= Plus (V v) (N 1)))"

abbreviation vc_pretaut :: "acom \<Rightarrow> assn \<Rightarrow> state \<Rightarrow> bool" where
  "vc_pretaut c pc s \<equiv> vc c pc s \<and> pre c pc s"



section {* Exercise 1 *}

definition MAX :: "acom" where
  "MAX = IF' Less (V 0) (V 1) THEN 2 #= (V 1) ELSE 2 #= (V 0)" 

lemma MAX_sound: "vc_pretaut MAX (\<lambda>s. s 2 = max (s 0) (s 1)) s"
unfolding MAX_def
apply auto
done



section {* Exercise 2 *}

definition MULTIPLY :: "acom" where
  "MULTIPLY = 2 #= (N 0) ;;
              FOR 3 FROM (N 0) TO (V 0) (\<lambda>s. s 2 = s 3 * s 1 \<and> s 3 \<le> s 0) 
              DO 2 #= Plus (V 2) (V 1)"

lemma MULTIPLY_sound: "vc_pretaut MULTIPLY (\<lambda>s. s 2 = s 0 * s 1) s"
unfolding MULTIPLY_def
apply auto
done



section {* Exercise 3 *}

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1"
| "factorial (Suc n) = factorial n * Suc n"

lemma factorial_unfold: 
  "1 \<le> n \<Longrightarrow> factorial n = n * factorial (n - 1)"
by (induct n) simp_all

abbreviation InvFAC where 
  "InvFAC s \<equiv> s 1 = factorial ((s 2) - 1) \<and> 
              s 2 \<le> (s 0) + 1 \<and> 
              1 \<le> s 2"

abbreviation InvFAC2 where
  "InvFAC2 s \<equiv> s 3 = (s 4) * (s 1) \<and> 
               s 4 \<le> s 2 \<and> 
               1 \<le> s 2 \<and>
               s 1 = factorial ((s 2) - 1) \<and> 
               s 2 \<le> (s 0)"

definition FACTORIAL :: "acom" where
  "FACTORIAL = 1 #= (N 1) ;;
               FOR 2 FROM (N 1) TO (Plus (V 0) (N 1)) (\<lambda>s. InvFAC s) DO 
                ( 3 #= (N 0) ;;
                  FOR 4 FROM (N 0) TO (V 2) (\<lambda>s. InvFAC2 s)  DO 
                     3 #= Plus (V 3) (V 1) ;;
                  1 #= (V 3) )" 



lemma FACTORIAL_sound: "vc_pretaut FACTORIAL (\<lambda>s. s 1 = factorial (s 0)) s"
by (auto simp: factorial_unfold FACTORIAL_def)



section {* Homework *}


text {* A useful abbreviation: *}

abbreviation Eq where "Eq a1 a2 \<equiv> And (Not (Less a1 a2)) (Not (Less a2 a1))"



definition SUB :: "acom" where
  "SUB = SKIP"  (* provide a definition *)
 
lemma SUB_sound: "vc SUB (\<lambda>s. s 2 = s 0 - s 1) s"
  oops  (* provide a proof *)



definition EUCLID :: "acom" where
  "EUCLID = SKIP"  (* provide a definition *)

lemma EUCLID_sound: "vc EUCLID (\<lambda>s. s 2 = gcd (s 0) (s 1)) s"
  oops  (* provide a proof *)


end
