(*  Title:      MultiASP.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       Multi-active object formalisation
                For the moment methods and parameter bindings are done statically, 
                  without inheritance but with interfaces
                  this could be improved
*)
(*Conventions:
  l = location in store
  x,y=varname
  locs = local variables
  l_\<alpha> = location in the local store of the active object of \<alpha>
 Stl = statement list
 EContext is an execution context, ie a thread 
 EcL = EContext list*)

chapter {* Syntax and Semantics *}

theory MultiASP imports Main AuxiliaryFunctions begin
 
subsection {* Syntax *}
type_synonym ItfName = string
type_synonym VarName =  string
datatype VarOrThis = This | Id VarName
type_synonym ClassName = string
type_synonym MethodName = string

type_synonym ActName = nat
type_synonym FutName = nat
type_synonym Location = nat

datatype Signature = Method ItfName MethodName  "(ItfName * VarName) list" 
  (* signature = Method returnType MethodName (list of parameters)*)

datatype Value = null | ASPInt nat | ASPBool bool (* static values *)
                | ActRef ActName (* runtime values *)
                | ObjRef Location
type_synonym  Object = "(VarName\<rightharpoonup>Value) * ClassName"
abbreviation GetObject:: "Object \<Rightarrow>VarName=>Value option" ("_.[_]")
  where "GetObject ob x \<equiv> (fst ob) x"
abbreviation SetObject:: "Object \<Rightarrow>VarName=>Value\<Rightarrow>Object" ("_.[_]:=_")
  where "SetObject ob x v\<equiv> ((fst ob)(x\<mapsto>v),snd ob)"

datatype Storable = Obj Object | FutRef FutName | StoredVal Value

datatype Expression = Val Value
             | Var VarOrThis 
             | Plus Expression Expression ("_+\<^sub>A_" [120,120] 200) 
             | And Expression Expression ("_&\<^sub>A_" [100,100] 300) 
             | Test Expression Expression ("_==\<^sub>A_" [100,100] 300) 
             


datatype Rhs = Expr Expression
             | Call Expression MethodName "Expression list" ("_.\<^sub>A_'(_')" [440,0,50] 500) (*e.m(e list) *)
             | New ClassName "Expression list" ("new _'(_')" [300,0] 500) (*new C(e list) *)
             | NewActive ClassName "Expression list" ("newActive _'(_')" [300,0] 500) (*newActive C(e list) *)
             | Hole (* runtime term *)

datatype Statement =   Assign VarName Rhs  (infix "=\<^sub>A"  400) (*x=z*)
| Return Expression ("return _" [300] 300)(*return E *)
| If Expression "Statement list" "Statement list" ("IF _ THEN _ ELSE _ " [300,0,0] 300)(*if E then s else s *)
(* skip |  NB: skip and seq are not necessary thanks to the use of statement list
| Seq Statement Statement (infix ";;"  100)*)
abbreviation MakeStatementList:: "Statement \<Rightarrow>Statement list\<Rightarrow>Statement list" (infix ";;" 100)
  where "MakeStatementList s Stl\<equiv> s#Stl"
abbreviation MakeStatementList2:: "Statement \<Rightarrow>Statement\<Rightarrow>Statement list" (infix ";;;" 120)
  where "MakeStatementList2 s s'\<equiv> s#[s']"


(*primrec RedContext:: "Statement\<Rightarrow> Statement \<times>Statement" (* returns basic instruction,context , i.e. the rest of the sequence*)
where
  "RedContext Skip = (Skip,Skip)" |
  "RedContext (x=\<^sub>Az) =  ((x=\<^sub>Az),Skip)" |
  "RedContext (return e) =  (return e,Skip)" |
  "RedContext (IF e THEN s ELSE s') =  (IF e THEN s ELSE s',Skip)" |
  "RedContext ( s ;; s') =  (fst (RedContext s),(snd (RedContext s);;s'))"
*)
(*abbreviation BuildContext::"Statement\<Rightarrow>Statement\<Rightarrow> Statement \<times>Statement" ("_[[_]]" [300, 0] 300)
where "BuildContext R s \<equiv> (s,R)"
*)
record Method = 
MethSignature:: Signature 
LocalVariables::"(ItfName * VarName) list" 
Body::"Statement list"
(*MethDefinition methodname (local variables) body*)

abbreviation Parameters::"Method \<Rightarrow>(ItfName * VarName) list" 
where "Parameters m \<equiv> case (MethSignature m) of 
        Method ItfName MethodName  param_list\<Rightarrow>param_list"

abbreviation MName:: "Method \<Rightarrow> MethodName"
where "MName m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>MethName"

abbreviation MRType:: "Method \<Rightarrow> ItfName"
where "MRType m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>returnType"

abbreviation MParams:: "Method \<Rightarrow>(ItfName * VarName) list"  
where "MParams m \<equiv> case (MethSignature m) of 
        (Method returnType MethName listparameters) \<Rightarrow>listparameters"


record Class = 
 Name::ClassName 
 Interfaces::"(ItfName list) "
 ClassParameters::"((ItfName * VarName) list)"
 StateVariables::"((ItfName * VarName) list)"
 Methods::"(Method list)"
             (*ASPclass name (classparameters) (implementedinterfaces) (statevariables) (listofmethodbodies) *)
record Interface = 
  IName:: ItfName  
  IMethods:: "(Signature list)"

datatype Program = Prog "Interface list" "Class list" "(ItfName * VarName) list" "Statement list"

type_synonym EContext = " Location * (VarName\<rightharpoonup>Value) * (Statement list)" 
                          (*execution context = location of this, local variables, and statements *)
type_synonym Request = "FutName * MethodName * (Value list)"
type_synonym Store = "Location \<rightharpoonup> Storable"
abbreviation EC_location::"EContext \<Rightarrow>Location"
where "EC_location Ec \<equiv> fst Ec"
abbreviation EC_locs:: "EContext \<Rightarrow>(VarName\<rightharpoonup>Value)"
where "EC_locs Ec \<equiv> fst (snd Ec)"
abbreviation EC_Stl:: "EContext \<Rightarrow>Statement list"
where "EC_Stl Ec \<equiv> snd (snd Ec)"
(*datatype Process = Proc Request "Context list" *)

datatype ActiveObject = AO Location Store "Request\<rightharpoonup>(EContext list)" "Request list"
    (* active object location , store, task list, request queue*)

datatype FutValue = Undefined | FutVal Value  Store

datatype Configuration = Cn "ActName\<rightharpoonup>ActiveObject" "FutName\<rightharpoonup>FutValue"

subsection {*finite configuration *}

definition finite_Store :: "Store \<Rightarrow> bool"
  where
    "finite_Store \<sigma> \<equiv> (finite (dom \<sigma>) \<and> (\<forall> loc obj. (\<sigma>(loc)=Some (Obj obj)\<longrightarrow> finite (dom (fst obj)))))"

definition finite_Processes :: "(Request\<rightharpoonup>(EContext list)) \<Rightarrow> bool"
  where
    "finite_Processes (processMap) \<equiv> finite (dom (processMap)) \<and>
       (\<forall> contList\<in>(ran(processMap)). \<forall>cont\<in> set contList. finite (dom(EC_locs(cont))))"

primrec finite_Configuration :: "Configuration => bool"
  where
 " finite_Configuration (Cn AOs Futures) =
      (finite (dom AOs) \<and> finite (dom Futures) \<and> 
    (\<forall> futVal\<in>(ran Futures). \<forall> v \<sigma>. (futVal =FutVal v \<sigma> \<longrightarrow> finite_Store \<sigma>)) \<and> (*NB: Undefined futures are finite*)
    (\<forall> ao\<in>(ran AOs). \<forall> l \<sigma> P Q. ao = AO l \<sigma> P Q \<longrightarrow> finite_Store \<sigma> \<and> finite_Processes P))"
declare MultiASP.finite_Configuration.simps[simp del]

text{* Binding and fetching elements *}
definition  fetchClass
where
"fetchClass P C \<equiv> 
case P of (Prog Is CL Vars Stl) \<Rightarrow> (List.find  (\<lambda>class.(Name class) = C) CL) 
"
definition fetchMethodInClass
where
"fetchMethodInClass  class m \<equiv> 
Option.bind 
(List.find (\<lambda>method. (MName method = m)) (Methods class))
(\<lambda>method. Some (map snd (MParams method), map snd (LocalVariables method), Body method))
"

definition Bind::"Program\<Rightarrow>Location\<Rightarrow>ClassName\<Rightarrow>MethodName\<Rightarrow>Value list\<Rightarrow> EContext option"
where
 "Bind P l C m value_list\<equiv>
(case fetchClass P C of
  Some class \<Rightarrow>
    (case  fetchMethodInClass class m  of 
       Some (param_list,locs,b) \<Rightarrow> 
         if length param_list = length value_list then
           ( let locales=  (map_of (zip locs (replicate (length locs) null)))
                    ++ (map_of (zip param_list value_list)) in
                Some ( l, locales,b))
           else None
       | None \<Rightarrow> None)
  | _\<Rightarrow> None)"
definition  fields:: "Program\<Rightarrow>ClassName \<Rightarrow>VarName list"
where
  "fields P C \<equiv>
     case (fetchClass P C) of
  Some class \<Rightarrow>(map snd (StateVariables class))"

definition  params:: "Program\<Rightarrow>ClassName \<Rightarrow>VarName list"
where
  "params P C \<equiv>case (fetchClass P C) of
  Some class \<Rightarrow>(map snd (ClassParameters class))"


definition Interface_set_from_variable_list:: "(ItfName * VarName) list\<Rightarrow>ItfName set"
where
"Interface_set_from_variable_list VL\<equiv> set (map fst VL)"

abbreviation DefinedClassNames
where "DefinedClassNames prog \<equiv>set (case prog of Prog IL CL vl xtl \<Rightarrow>map Name CL)"



subsection {* serialization and location renaming *}

inductive serialize :: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ran(fst(obj)). \<exists>\<sigma>''. (serialize v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
     \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (FutRef f)  \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (StoredVal v)  \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
     "(serialize (ActRef f) \<sigma> \<sigma>')" |
     "serialize (null) \<sigma> \<sigma>' " | 
     "serialize (ASPInt n) \<sigma> \<sigma>'" | 
     "serialize (ASPBool b) \<sigma> \<sigma>'"

 definition Referenced_locations_Value:: "Value \<Rightarrow> Location set"
where  "Referenced_locations_Value v \<equiv> (case v of ObjRef l \<Rightarrow>{l} | _ \<Rightarrow> {})"

axiomatization where finite_map: "finite (dom (\<sigma>::Store))"
function (sequential) serialization_filter :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (serialization_filter l \<sigma> L) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      Some (Obj obj) \<Rightarrow> listunionMap (\<lambda>x.(serialization_filter x \<sigma> (L\<union>{l}))) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) |
      _ \<Rightarrow> {}))" 
by auto
termination 
apply (relation "measure (\<lambda>(l,\<sigma>,L). card (dom \<sigma> - L))") 
apply auto
apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
apply (subgoal_tac "finite ((dom \<sigma>-L))")
apply (drule_tac x=l in Finite_Set.card.remove)+
apply (insert finite_map)
apply auto
done
     
primrec subst_Value :: " Value \<Rightarrow> (Location\<Rightarrow>Location) \<Rightarrow> Value"
where
  "subst_Value (ObjRef l) \<psi> = ObjRef (\<psi>(l))" |
  "subst_Value (ActRef a) \<psi> = ActRef a" |
  "subst_Value (null) \<psi> = null" |
  "subst_Value (ASPInt i) \<psi> = ASPInt i" |
  "subst_Value (ASPBool b) \<psi> = ASPBool b"

definition check_subst :: "Store \<Rightarrow> (Location\<Rightarrow>Location) \<Rightarrow> Store \<Rightarrow> bool"
where
  "check_subst  \<sigma> \<psi> \<sigma>' \<equiv>
    ( inj \<psi> \<and> dom \<sigma>' =  \<psi> ` (dom(\<sigma>)) 
    \<and> (\<forall> obj l . (\<sigma>(l) = Some (Obj obj)  
      \<longrightarrow> (\<exists> obj'. (\<sigma>'(\<psi>(l)) = Some (Obj obj') \<and> (\<forall> x  v. (obj.[x]) = Some v \<longrightarrow> (obj'.[x])=Some (subst_Value v \<psi>)))))
    \<and>   (\<forall> f l . (\<sigma>(l) = Some (FutRef f) \<longrightarrow> \<sigma>'(\<psi>(l)) =Some (FutRef f)))
    \<and>   (\<forall> v l . (\<sigma>(l) = Some (StoredVal v) \<longrightarrow> 
      \<sigma>'(\<psi>(l)) = Some (StoredVal (subst_Value v \<psi>))))))"

definition rename_value_store :: " Store \<Rightarrow> Value \<Rightarrow> Store \<Rightarrow> Value \<Rightarrow> Store \<Rightarrow> bool"
 where "rename_value_store \<sigma>\<^sub>0 v \<sigma> v' \<sigma>'  \<equiv> (\<exists>\<psi> . check_subst \<sigma> \<psi> \<sigma>'\<and>v'=subst_Value v \<psi>)\<and>
                                            dom \<sigma>\<^sub>0 \<inter> dom \<sigma>' = {}"

definition serialize_and_rename_list :: " Store \<Rightarrow> Value list \<Rightarrow> Store \<Rightarrow> Value list \<Rightarrow> Store \<Rightarrow> bool"
 where "serialize_and_rename_list \<sigma>\<^sub>0 vl \<sigma> vl' \<sigma>'  \<equiv> 
              length vl=length vl' \<and>
              (\<exists>\<psi> \<sigma>''. (\<forall> i<length vl. serialize  (vl!i) \<sigma> \<sigma>''\<and>vl'!i=subst_Value (vl!i) \<psi>) \<and>check_subst \<sigma>'' \<psi> \<sigma>') \<and>
              dom \<sigma>\<^sub>0 \<inter> dom \<sigma>' = {}"

(*locale Generic_Functions = *)

(*consts 
  Bind:: "Program\<Rightarrow>Location\<Rightarrow>ClassName\<Rightarrow>MethodName\<Rightarrow>Value list\<Rightarrow> EContext "*)
(* consts
  params:: "Program\<Rightarrow>ClassName \<Rightarrow>VarName list"
 *)
(*consts fetch:: "Class list\<Rightarrow>ClassName\<Rightarrow>MethodName\<Rightarrow>
            ((VarName list) *(VarName list) * (Statement list)) option" *)


(* semantics parameterized by compatibility and binder function*)
axiomatization 
  Compatible :: "(Request * Request) set"
where                                         
  symmetric_compatible: "sym Compatible"




lemma COMP[rule_format]: "\<forall>x y. (x,y)\<in>Compatible\<longrightarrow>(y,x)\<in>Compatible"
apply (fold sym_def)
apply (rule symmetric_compatible)
done

section{*SOS*}

(*datatype EvaluatedExpr = Undefined | EVal Value | EObj Object | EFutRef FutName*)

inductive_set EvalValue:: "(Value \<times> Store \<times> Value) set"
where
  Valnull[simp,intro]: "(null, \<sigma>,  null)\<in>EvalValue" |
  Valint[simp,intro]: "(ASPInt i, \<sigma>,  (ASPInt i) )\<in>EvalValue" |
  valbool[simp,intro]: "(ASPBool b, \<sigma>,  (ASPBool b) )\<in>EvalValue" |
  valact[simp,intro]: "(ActRef \<alpha>, \<sigma>,  (ActRef \<alpha>) )\<in>EvalValue" |
  valfut[simp,intro]:"\<sigma>(l) = Some (FutRef f) \<Longrightarrow>(ObjRef l, \<sigma>, ObjRef l)\<in>EvalValue" |
  valobj[simp,intro]:"\<sigma>(l) = Some (Obj obj) \<Longrightarrow>(ObjRef l, \<sigma>, ObjRef l)\<in>EvalValue" |
  valstored[simp,intro]: "\<lbrakk>\<sigma>(l) = Some (StoredVal v);(v,\<sigma>,ee)\<in> EvalValue\<rbrakk> \<Longrightarrow>(ObjRef l, \<sigma>, ee)\<in>EvalValue" 

lemma EvalValue_is_deterministic[rule_format,intro]: "(e,\<sigma>,v)\<in>EvalValue \<longrightarrow>(e,\<sigma>,v')\<in>EvalValue \<longrightarrow>v=v'"
apply (rule impI)
apply (erule EvalValue.induct)
apply auto
apply (erule EvalValue.cases,simp+)+
done

inductive_set EvalExpr:: "(Expression \<times> Location \<times> (VarName\<rightharpoonup>Value)\<times>Store \<times> Value) set"
(* (e1,l,locs,\<sigma>,v) is true if e1 EVALUATES to v  in a setting where local variables are locs, store is \<sigma> and l is the location of this*)
 where
   exprval[simp,intro]: "(v,\<sigma>,ev)\<in>EvalValue \<Longrightarrow>(Val v, l, locs, \<sigma>, ev)\<in>EvalExpr" |
   exprlocs[simp,intro]: "\<lbrakk>locs(x)=Some v;(v,\<sigma>,ev)\<in>EvalValue\<rbrakk> \<Longrightarrow>(Var (Id x), l, locs, \<sigma>, ev)\<in>EvalExpr" |
   exprThis[simp,intro]: "\<lbrakk>(ObjRef l,\<sigma>,ev)\<in>EvalValue\<rbrakk> \<Longrightarrow>(Var This, l, locs, \<sigma>, ev)\<in>EvalExpr" |
   exprfield[simp,intro]:
   "\<lbrakk>locs(x)=None; \<sigma> l=Some (Obj ob); ob.[x] = Some v;(v,\<sigma>,ev)\<in>EvalValue\<rbrakk> 
                      \<Longrightarrow>(Var (Id x), l, locs, \<sigma>, ev)\<in>EvalExpr" |
   expradd[simp,intro]:"\<lbrakk>(e,l,locs,\<sigma>,ASPInt i)\<in>EvalExpr;(e',l,locs,\<sigma>, ASPInt i')\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e +\<^sub>A e', l, locs, \<sigma>, ASPInt (i+i'))\<in>EvalExpr" |
   exprand[simp,intro]:"\<lbrakk>(e,l,locs,\<sigma>,ASPBool b)\<in>EvalExpr;(e',l,locs,\<sigma>,ASPBool b')\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e &\<^sub>A e', l, locs, \<sigma>, ASPBool (b\<and>b'))\<in>EvalExpr" |
   exprtest[simp,intro]:"\<lbrakk>(e,l,locs,\<sigma>,ASPInt i)\<in>EvalExpr;(e',l,locs,\<sigma>,ASPInt i')\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e ==\<^sub>A e', l, locs, \<sigma>, ASPBool (i=i'))\<in>EvalExpr"

lemma EvalExpr_is_deterministic[rule_format]: 
      " (e,l,locs,\<sigma>,v)\<in>EvalExpr \<longrightarrow> (\<forall> v'. (e,l,locs,\<sigma>,v')\<in>EvalExpr \<longrightarrow>v=v')"
apply (rule impI)
apply (erule EvalExpr.induct)
apply auto
apply (erule EvalExpr.cases,auto)
apply (erule EvalExpr.cases,auto)
apply (erule EvalExpr.cases,auto)
apply (erule EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e+\<^sub>Ae'"  in EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e&\<^sub>Ae'"  in EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e==\<^sub>Ae'"  in EvalExpr.cases,auto)
done

abbreviation Ready:: "Request\<Rightarrow>(Request\<rightharpoonup>(EContext list))\<Rightarrow>(Request list)\<Rightarrow>bool"
  (*Ready q,p,Rq returns true if q is ready to be served*)
where
 "Ready R tasks Rq \<equiv>(\<forall> Q\<in>dom(tasks). (R,Q)\<in>Compatible)
                    \<and> (\<forall> Q\<in>set Rq. (R,Q)\<in>Compatible)"

inductive reduction :: "Program\<Rightarrow>[Configuration, Configuration] => bool"  ("_\<turnstile>_\<leadsto>_" 50)
  where
    Serve [simp, intro!]: 
      "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> tasks (Rq@R#Rq')) ; R=(f,m,vl); 
        Ready R tasks Rq; 
         (\<sigma> l_\<alpha>) = Some (Obj (obj,C));
        Bind P l_\<alpha> C m vl = Some EC\<rbrakk> 
          \<Longrightarrow> P\<turnstile>Cn Activities Futures 
                \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(R\<mapsto>[EC]))) (Rq@Rq'))) Futures" |

    AssignLocal  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l,locs,(x=\<^sub>AExpr e);;Stl)#EcL);
       x\<in>dom locs ; (e,l, locs, \<sigma>,v)\<in>EvalExpr
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>((l,locs(x\<mapsto>v),Stl)#EcL))) Rq)))  Futures" |

    AssignField  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,(x=\<^sub>AExpr e);;Stl)#EcL);
       x\<notin>dom locs;  \<sigma>(l_this) = Some (Obj obj);     x\<in>dom(fst(obj));  
       (e, l_this, locs, \<sigma>,v)\<in>EvalExpr;     \<sigma>'=\<sigma>(l_this\<mapsto>Obj (obj.[x]:=v))
      \<rbrakk> 
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma>' (tasks(Q\<mapsto>((l_this,locs,Stl)#EcL))) Rq))) Futures" |

     New  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,(x=\<^sub>Anew C(el));;Stl)#EcL);
       field_list=fields P C; param_list=params P C; field_list\<noteq>undefined;
       l\<notin>dom \<sigma>; 
       length param_list = length el;length param_list = length value_list; 
       \<forall> i<length value_list . (el!i,l_this,locs,\<sigma>,value_list!i)\<in>EvalExpr ;
       \<sigma>'=\<sigma>(l\<mapsto> Obj (  (map_of (zip field_list (replicate (length field_list) null)))
                    ++ (map_of (zip param_list value_list)), C ))
      \<rbrakk>  
      (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma>' (tasks(Q\<mapsto>((l_this,locs,(x=\<^sub>AExpr (Val (ObjRef l));;Stl))#EcL))) Rq)) ) Futures" |

     NewActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,(x=\<^sub>AnewActive C(el));;Stl)#EcL); 
       fields P C=field_list; params P C=param_list; 
       \<gamma>\<notin>dom Activities;       
       length param_list = length el;   length param_list = length value_list; 
       \<forall> i<length value_list . ((el!i,l_this,locs,\<sigma>,value_list!i)\<in>EvalExpr \<and> serialize (value_list!i) \<sigma> \<sigma>\<^sub>0) ;
        l\<notin>dom \<sigma>\<^sub>0;
       \<sigma>'=\<sigma>\<^sub>0(l\<mapsto> Obj (  (map_of (zip field_list (replicate (length field_list) null)))
                    ++ (map_of (zip param_list value_list)), C )) 
     \<rbrakk>   
        \<Longrightarrow> P\<turnstile>Cn Activities Futures 
             \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>((l_this,locs,(x=\<^sub>AExpr (Val (ActRef \<gamma>)));;Stl)#EcL))) Rq))
                             (\<gamma>\<mapsto> (AO l \<sigma>' empty [])))  Futures" |
       (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)

   InvkActive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       Activities \<beta> = Some (AO l\<^sub>\<beta> \<sigma>\<^sub>\<beta> tasks\<^sub>\<beta> Rq\<^sub>\<beta>); 
       tasks Q = Some ((l_this,locs,x=\<^sub>A(e.\<^sub>Am(el));;Stl)#EcL);
       \<alpha>\<noteq>\<beta>;
       (e,lt,locs,\<sigma>,ActRef \<beta>)\<in>EvalExpr;
       f\<notin>dom Futures;      l\<notin>dom \<sigma>;
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,l_this,locs,\<sigma>,value_list!i)\<in>EvalExpr) ;
       serialize_and_rename_list \<sigma>\<^sub>\<beta> value_list \<sigma> value_list' \<sigma>\<^sub>P; 
        \<sigma>'=\<sigma>\<^sub>\<beta> ++ \<sigma>\<^sub>P
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> (\<sigma>(l\<mapsto>FutRef f)) (tasks(Q\<mapsto>((l_this,locs,x=\<^sub>AExpr (Val (ObjRef l));;Stl)#EcL))) Rq)
                             (\<beta>\<mapsto> AO l\<^sub>\<beta> \<sigma>' tasks\<^sub>\<beta> (Rq\<^sub>\<beta>@[(f,m,value_list')]) )) (Futures(f\<mapsto>Undefined))" |

   InvkActive_Self  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,x=\<^sub>A(e.\<^sub>Am(el));;Stl)#EcL);
       (e,l_this,locs,\<sigma>,ActRef \<alpha>)\<in>EvalExpr;
       f\<notin>dom Futures;   
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,l_this,locs,\<sigma>,value_list!i)\<in>EvalExpr) ;
       serialize_and_rename_list \<sigma> value_list \<sigma> value_list' \<sigma>\<^sub>P; 
       \<sigma>'=\<sigma> ++ \<sigma>\<^sub>P; l\<notin>dom \<sigma>'
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> (\<sigma>'(l\<mapsto>FutRef f)) (tasks(Q\<mapsto>((l_this,locs,x=\<^sub>AExpr (Val (ObjRef l));;Stl)#EcL))) (Rq@[(f,m,value_list')]))) 
               (Futures(f\<mapsto>Undefined))" |

   InvkPassive  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,(x=\<^sub>Ae.\<^sub>Am(el));;Stl) #EcL); 
       (e,l_this,locs,\<sigma>,ObjRef l)\<in>EvalExpr;
         (\<sigma> l) = Some (Obj (obj,C));
       length vl = length el; \<forall> i<length vl . ((el!i,l_this,locs,\<sigma>,vl!i)\<in>EvalExpr) ;
        Bind P l C m vl = Some EC
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>(EC#(l_this,locs,x=\<^sub>AHole;;Stl)#EcL))) Rq) ) Futures" |

   ReturnLocal  [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this',locs',return e;;Stl)#(l_this,locs,x=\<^sub>AHole#Stl')#EcL); 
       (e,l_this',locs,\<sigma>,v)\<in>EvalExpr
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma> 
                             (tasks(Q\<mapsto>((l_this,locs,x=\<^sub>AExpr (Val v)#Stl')#EcL))) Rq) ) Futures" |

   ReturnRequest [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some [(l_this,locs,return e;;Stl)];   Q=(f,m,vl);
       (e,l_this,locs,\<sigma>,v)\<in>EvalExpr;  serialize v \<sigma> \<sigma>\<^sub>f
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma> (tasks|``Q) Rq) ) (Futures(f\<mapsto>FutVal v \<sigma>\<^sub>f))" |

    UpdateFuture [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       \<sigma> l = Some (FutRef f);  Futures f = Some (FutVal v \<sigma>\<^sub>f); 
       rename_value_store \<sigma> v \<sigma>\<^sub>f v' \<sigma>\<^sub>r; 
       \<sigma>'=(\<sigma>++\<sigma>\<^sub>r)(l\<mapsto>StoredVal v')
      \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma>' tasks Rq)) Futures"   |

    IfThenElseTrue [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((l_this,locs,(IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl)#EcL);
       (e,l_this,locs,\<sigma>,ASPBool True)\<in>EvalExpr
   \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
           \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>((l_this,locs,s\<^sub>t@Stl)#EcL))) Rq))) Futures"  |

    IfThenElseFalse [simp, intro!]: 
     "\<lbrakk>Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq);
       tasks Q = Some ((l_this,locs,(IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl)#EcL);
       (e,l_this,locs,\<sigma>,ASPBool False)\<in>EvalExpr
   \<rbrakk>  
      \<Longrightarrow> P\<turnstile>Cn Activities Futures 
          \<leadsto>Cn (Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>((l_this,locs,s\<^sub>e@Stl)#EcL))) Rq))) Futures"  

 (*   Skip [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> tasks Rq); 
       tasks Q = Some ((locs,S)#EcL);RedContext S = R[[Skip]];R\<noteq>Skip;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (tasks(Q\<mapsto>((locs,R)#EcL))) Rq))
   \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures"  
   *)   
(*     upd  [simp, intro!]: "l : dom f \<Longrightarrow>\<leadsto> 
                         Upd (Obj f T) l a \<rightarrow>\<^sub>\<beta>  Obj (f (l \<mapsto> a)) T" |
    sel  [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Call s l u \<rightarrow>\<^sub>\<beta>  Call t l u" |
    selR [simp, intro!]: "u \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Call s l u \<rightarrow>\<^sub>\<beta>  Call s l t" |
    updL [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Upd s l u \<rightarrow>\<^sub>\<beta> Upd t l u" |
    updR [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Upd u l s \<rightarrow>\<^sub>\<beta> Upd u l t" |
    obj [simp, intro!]: "\<lbrakk> s \<rightarrow>\<^sub>\<beta> t; l: dom f \<rbrakk> \<Longrightarrow> Obj (f (l \<mapsto> s)) T \<rightarrow>\<^sub>\<beta> Obj (f (l \<mapsto> t)) T" |
  act [simp, intro!]: "s \<rightarrow>\<^sub>\<beta> t \<Longrightarrow> Active s \<rightarrow>\<^sub>\<beta> Active t"    
abbreviation
  beta_reds :: "[dB, dB] => bool"  (infixl "->>" 50) where
  "s ->> t == beta^** s t"

notation (latex)
  beta_reds  (infixl "\<rightarrow>\<^sub>\<beta>\<^sup>*" 50)
*)

definition emptyObj :: Storable where
"emptyObj \<equiv> Obj (empty,''EmptyObjectClass'')"

definition emptyObjClass  where
"emptyObjClass \<equiv> 
\<lparr>Name = ''EmptyObjectClass'',
 Interfaces=[],
 ClassParameters=[],
 StateVariables=[],
 Methods=[]
\<rparr>"

definition BuildInitialConfigurationfromVarsStl:: "(VarName list) \<Rightarrow>Statement list\<Rightarrow> Configuration"
where
  "BuildInitialConfigurationfromVarsStl vl stl \<equiv> Cn (empty(0\<mapsto>(AO 0 (empty(0\<mapsto> emptyObj)) 
                  (empty((0,''m'',[])\<mapsto>[(0,(map_of (zip vl (replicate (length vl) null))),stl)])) [])))
                  (empty(0\<mapsto>Undefined))"

definition InitialConfiguration:: "Program \<Rightarrow>Configuration"
where  
" InitialConfiguration prog \<equiv> case prog of (Prog Is CL Vars Stl) \<Rightarrow> BuildInitialConfigurationfromVarsStl (map snd Vars) Stl" 


end
