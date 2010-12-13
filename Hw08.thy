theory Type_Inference_Template
imports Types
begin

text {* Make the typing relation executable: *}

code_pred ctyping .

text {* Auxiliary function to collect variables in expressions and commands.  The function @{const List.insert} adds an element to a list if it is not already in the list. *}

fun avars :: "aexp \<Rightarrow> name list \<Rightarrow> name list"
where
  "avars (V x) vs = List.insert x vs"
| "avars (Plus e1 e2) vs = avars e2 (avars e1 vs)"
| "avars _ vs = vs"

fun bvars :: "bexp \<Rightarrow> name list \<Rightarrow> name list"
where
  "bvars (B _) vs = vs"
| "bvars (Not e) vs = bvars e vs"
| "bvars (And e1 e2) vs = bvars e2 (bvars e1 vs)"
| "bvars (Less e1 e2) vs = avars e2 (avars e1 vs)"

fun cvars :: "com \<Rightarrow> name list \<Rightarrow> name list"
where
  "cvars SKIP vs = vs"
| "cvars (x ::= a) vs = List.insert x (avars a vs)"
| "cvars (c1 ; c2) vs = cvars c2 (cvars c1 vs)"
| "cvars (IF b THEN c1 ELSE c2) vs =
    cvars c2 (cvars c1 (bvars b vs))"
| "cvars (WHILE b DO c) vs =
    cvars c (bvars b vs)"


text {* Type variables and constraints *}

datatype tvar = TVar name | Type ty

fun type_of :: "tyenv \<Rightarrow> tvar \<Rightarrow> ty"
where
  "type_of \<Gamma> (TVar v) = \<Gamma>(v)"
| "type_of \<Gamma> (Type t) = t"

types
  constraint = "tvar * tvar"
  constraints = "constraint list"

fun constraint_holds :: "tyenv \<Rightarrow> constraint \<Rightarrow> bool" (infix "\<Turnstile>" 50)
where "\<Gamma> \<Turnstile> (v, v') \<longleftrightarrow> type_of \<Gamma> v = type_of \<Gamma> v'"

subsection {* Constraint generation *}

fun ccollect :: "com \<Rightarrow> constraints"
where 
  "ccollect _ = []" (* add definition here *)

lemma ccollect_sound_and_complete:
"\<Gamma> \<turnstile> c \<longleftrightarrow> (\<forall>C \<in> set (ccollect c). \<Gamma> \<Turnstile> C)"
(* quickcheck[iterations=200,size=8,report] *)
oops

subsection {* Constraint solving *}


fun solve :: "constraints \<Rightarrow> (name * tvar) list \<Rightarrow> (name * tvar) list option"
where
  "solve _ M = Some M" (* add real definition here *)

subsection {* Type inference *}

fun type_infer :: "com \<Rightarrow> (name * tvar) list option"
where
  "type_infer c = 
    (let constraints = ccollect c;
         vars = cvars c [];
         init = map (\<lambda>x. (x, TVar x)) vars
     in solve constraints init)"

subsection {* Specification of type inference *}

definition instantiate :: "(name \<Rightarrow> ty) \<Rightarrow> (name \<times> tvar) list \<Rightarrow> tyenv"
where
  "instantiate I M =
    (\<lambda>x. case map_of M x of
      None \<Rightarrow> I x
    | Some (Type T) \<Rightarrow> T
    | Some (TVar y) \<Rightarrow> I y)"

fun is_instance :: "tyenv \<Rightarrow> (name \<times> tvar) list \<Rightarrow> bool" (infix "<:" 50)
where
  "\<Gamma> <: [] \<longleftrightarrow> True"
| "\<Gamma> <: ((x,Type t)#M) \<longleftrightarrow> (\<Gamma>(x) = t \<and> \<Gamma> <: M)"
| "\<Gamma> <: ((x,TVar y)#M) \<longleftrightarrow> (\<Gamma>(x) = \<Gamma>(y) \<and> \<Gamma> <: M)"

text {* The following lemmas are formulated in a way that is suitable
for counterexample generation with quickcheck. *}

lemma type_infer_sound:
"(case type_infer c of
    None \<Rightarrow> True
  | Some M \<Rightarrow> (instantiate I M \<turnstile> c))"
(*quickcheck[iterations=200,size=8,report]*)
oops

lemma type_infer_complete:
"\<Gamma> \<turnstile> c \<longrightarrow>
  (case type_infer c of 
     None \<Rightarrow> False
   | Some M \<Rightarrow> \<Gamma> <: M)"
(*quickcheck[iterations=200,size=8,report]*)
oops


end