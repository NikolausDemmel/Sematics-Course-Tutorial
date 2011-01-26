theory Ex12_Template
imports VC GCD
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
  "FOR v FROM a1 TO a2 b DO c =
     (v #= a1 ;; WHILE' (Less (V v) a2) b DO (c ;; v #= Plus (V v) (N 1)))"



section {* Exercise 1 *}

definition MAX :: "acom" where
  "MAX = SKIP"  (* provide a definition *)

lemma MAX_sound: "vc MAX (\<lambda>s. s 2 = max (s 0) (s 1)) s"
  oops  (* provide a proof *)



section {* Exercise 2 *}

definition MULTIPLY :: "acom" where
  "MULTIPLY = SKIP"  (* provide a definition *)

lemma MULTIPLY_sound: "vc MULTIPLY (\<lambda>s. s 2 = s 0 * s 1) s"
  oops  (* provide a proof *)



section {* Exercise 3 *}

fun factorial :: "nat \<Rightarrow> nat" where
  "factorial 0 = 1"
| "factorial (Suc n) = factorial n * Suc n"

definition FACTORIAL :: "acom" where
  "FACTORIAL = SKIP"  (* provide a definition *)

lemma FACTORIAL_sound: "vc FACTORIAL (\<lambda>s. s 1 = factorial (s 0)) s"
  oops  (* provide a proof *)



section {* Homework *}


text {* A useful abbreviation: *}

abbreviation Eq where "Eq a1 a2 \<equiv> And (Not (Less a1 a2)) (Not (Less a2 a1))"



definition SUB :: "name \<Rightarrow> name \<Rightarrow> name \<Rightarrow> acom" where
  "SUB a b c = SKIP"  (* provide a definition *)
 
lemma SUB_sound: "vc SUB (\<lambda>s. s 2 = s 0 - s 1) s"
  oops  (* provide a proof *)



definition EUCLID where
  "EUCLID = SKIP"  (* provide a definition *)

lemma EUCLID_sound: "vc EUCLID (\<lambda>s. s 2 = gcd (s 0) (s 1)) s"
  oops  (* provide a proof *)


end
