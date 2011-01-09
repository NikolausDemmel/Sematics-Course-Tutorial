header "Semantics homework sheet 8 - Nikolaus Demmel"

theory Hw08
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

fun tvar_of :: "aexp \<Rightarrow> tvar"
where
  "tvar_of (Ic _) = Type Ity" |
  "tvar_of (Rc _) = Type Rty" |
  "tvar_of (V x) = TVar x" |
  "tvar_of (Plus a1 _) = (tvar_of a1)"

fun acollect :: "aexp \<Rightarrow> constraints"
where
  "acollect (Plus a1 a2) = (tvar_of a1, tvar_of a2) # acollect a1 @ acollect a2" |
  "acollect _ = []"

fun bcollect :: "bexp \<Rightarrow> constraints"
where
  "bcollect (B _) = []" |
  "bcollect (Not b) = bcollect b" |
  "bcollect (And b1 b2) = bcollect b1 @ bcollect b2" |
  "bcollect (Less a1 a2) = (tvar_of a1, tvar_of a2) # acollect a1 @ acollect a2" 

fun ccollect :: "com \<Rightarrow> constraints"
where 
  "ccollect SKIP = []" |
  "ccollect (x ::= a) = (TVar x, tvar_of a) # acollect a" |
  "ccollect (c1 ; c2) = ccollect c1 @ ccollect c2" |
  "ccollect (IF b THEN c1 ELSE c2) = bcollect b @ ccollect c1 @ ccollect c2" |
  "ccollect (WHILE b DO c) = bcollect b @ ccollect c"

lemma ccollect_sound_and_complete:
"\<Gamma> \<turnstile> c \<longleftrightarrow> (\<forall>C \<in> set (ccollect c). \<Gamma> \<Turnstile> C)"
quickcheck[iterations=200,size=8,report]
oops

subsection {* Constraint solving *}

(* Assume there are no circular variable assignments *)
(*fun assigned_type :: "name \<Rightarrow> (name * tvar) list \<Rightarrow> tvar option"
where
  "assigned_type x M = (case map_of M x of
     None \<Rightarrow> None
   | Some (Type t) \<Rightarrow> Some (Type t)
   | Some (TVar v) \<Rightarrow> Some (" *)

fun assign_type :: "name \<Rightarrow> ty \<Rightarrow> (name * tvar) list \<Rightarrow> (name * tvar) list option"
where
  "assign_type x t M =
     (case (map_of M x) of
        None \<Rightarrow> None
      | Some (Type t') \<Rightarrow> (if t' = t then Some M else None)
      | Some (TVar v) \<Rightarrow> Some (map (\<lambda>(a,b). (a,(if b = (TVar v) then (Type t) else b))) M))"

fun assign_tvar :: "name \<Rightarrow> name \<Rightarrow> (name * tvar) list \<Rightarrow> (name * tvar) list option"
where
  "assign_tvar x tv M =
     (case (map_of M x) of
        None \<Rightarrow> None
      | Some (Type t) \<Rightarrow> assign_type tv t M
      | Some (TVar tv') \<Rightarrow> (case (map_of M tv) of
          None \<Rightarrow> None
        | Some (Type t) \<Rightarrow> Some (map (\<lambda>(a,b). (a,(if b = (TVar tv') then (Type t) else b))) M)
        | Some (TVar tv'') \<Rightarrow> Some (map (\<lambda>(a,b). (a,(if b = (TVar tv') then (TVar tv'') else b))) M)))"

fun solve :: "constraints \<Rightarrow> (name * tvar) list option \<Rightarrow> (name * tvar) list option"
where
  "solve _ None = None" |
  "solve [] X = X" |
  "solve ((Type t1, Type t2)#C) (Some M) = (if t1 = t2 then solve C (Some M) else None)" |
  "solve ((Type t, TVar v)#C) (Some M) = solve C (assign_type v t M)" |
  "solve ((TVar v, Type t)#C) (Some M) = solve C (assign_type v t M)" |
  "solve ((TVar v1, TVar v2)#C) (Some M) = solve C (assign_tvar v1 v2 M)"

value "ccollect (WHILE (Less (V 0) (V 1)) DO 0 ::= (V 2) ; 2 ::= (Ic 42))"
value "solve [(TVar 0, TVar (Suc 0)), (TVar 0, TVar 2), (TVar 2, Type Ity)]
             (Some (map (\<lambda>x. (x, TVar x)) [0,1,2]))"

subsection {* Type inference *}

fun type_infer :: "com \<Rightarrow> (name * tvar) list option"
where
  "type_infer c = 
    (let constraints = ccollect c;
         vars = cvars c [];
         init = map (\<lambda>x. (x, TVar x)) vars
     in solve constraints (Some init))"

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
quickcheck[iterations=200,size=8,report]
oops

value "ccollect (WHILE And (B False) (Less (V (Suc 0)) (Ic 0)) DO 0 ::= V (Suc 0))"

value "solve [(TVar (Suc 0), Type Ity), (TVar 0, TVar (Suc 0))]
             (Some (map (\<lambda>x. (x, TVar x)) [0,1]))"

lemma type_infer_complete:
"\<Gamma> \<turnstile> c \<longrightarrow>
  (case type_infer c of 
     None \<Rightarrow> False
   | Some M \<Rightarrow> \<Gamma> <: M)"
quickcheck[iterations=200,size=8,report]
oops


end