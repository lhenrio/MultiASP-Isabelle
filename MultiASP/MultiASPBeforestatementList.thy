(*  Title:      MultiASP.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       Multi-active object formalisation
*)

header {* Syntax and Semantics *}

theory MultiASP imports Main begin

subsection{*Preliminaries*}

definition
  remove_from_map :: "('a ~=> 'b) => 'a  => ('a ~=> 'b)"  (infixl "|``"  110) where
  "m|``x = m|`(dom m - {x})"

subsection {* Syntax *}
type_synonym ItfName = string
datatype VarName = This | Id string
type_synonym ClassName = string
type_synonym MethodName = string

type_synonym ActName = nat
type_synonym FutName = nat
type_synonym Location = nat

datatype Signature = Method Interface MethodName "(Interface * VarName) list" 
  (* signature = Method returnType MethodName (list of parameters)*)
and Interface = Itf ItfName "Signature list"
  (*interface = Itf Itfname (list of method signatures)*)

datatype Value = null | ASPInt nat | ASPBool bool (* static values *)
                | ActRef ActName (* runtime values *)
                | ObjRef Location
type_synonym  Object = "VarName~=>Value"

datatype Storable = Obj Object | FutRef FutName | StoredVal Value

datatype Expression = Val Value
             | Var VarName
             | Plus Expression Expression ("_+\<^sub>A_" [120,120] 200) 
             | And Expression Expression ("_&\<^sub>A_" [100,100] 300) 
             
datatype Rhs = Expr Expression
             | Call Expression MethodName "Expression list" ("_.\<^sub>A_(_)" [440,0,50] 500) (*e.m(e list) *)
             | New ClassName "Expression list" ("new _(_)" [300,0] 500) (*new C(e list) *)
             | NewActive ClassName "Expression list" ("newActive _(_)" [300,0] 500) (*newActive C(e list) *)
             | Hole (* runtime term *)

datatype Statement = Skip 
|  Assign VarName Rhs  (infix "=\<^sub>A"  400) (*x=z*)
| Return Expression ("return _" [300] 300)(*return E *)
| If Expression Statement Statement ("IF _ THEN _ ELSE _ " [300,0,0] 300)(*if E then s else s *)
| Seq Statement Statement (infix ";;"  100)

primrec RedContext:: "Statement\<Rightarrow> Statement \<times>Statement" (* returns basic instruction,context , i.e. the rest of the sequence*)
where
  "RedContext Skip = (Skip,Skip)" |
  "RedContext (x=\<^sub>Az) =  ((x=\<^sub>Az),Skip)" |
  "RedContext (return e) =  (return e,Skip)" |
  "RedContext (IF e THEN s ELSE s') =  (IF e THEN s ELSE s',Skip)" |
  "RedContext ( s ;; s') =  (fst (RedContext s),(snd (RedContext s);;s'))"

abbreviation BuildContext::"Statement\<Rightarrow>Statement\<Rightarrow> Statement \<times>Statement" ("_[[_]]" [300, 0] 300)
where "BuildContext R s \<equiv> (s,R)"

datatype Method = Signature  "(Interface * VarName) list" Statement
(*signature (local variables) body*)

datatype Class = ASPclass ClassName "(Interface * VarName) list" "Interface list" 
                                   "(Interface * VarName) list" "Method list"
             (*ASPClass name (class parameters) (implemented interfaces) (state variables) (list of method bodies) *)

datatype Program = Prog "Interface set" "Class set" "(Interface * VarName) list" Statement

type_synonym EContext = "(VarName~=>Value) * Statement" (*execution contet = local variables and statement *)
type_synonym Request = "FutName * MethodName * (Value list)"
type_synonym Store = "Location~=>Storable"

(*datatype Process = Proc Request "Context list" *)

datatype ActiveObject = AO Location Store "Request~=>(EContext list)" "Request list"
    (* active object location , store, task list, request queue*)

datatype FutValue = Undefined | FutVal Value  Store

datatype Configuration = Cn "ActName~=>ActiveObject" "FutName~=>FutValue"

subsection {*finite configuration *}

definition finite_Store :: "Store \<Rightarrow> bool"
  where
    "finite_Store \<sigma> \<equiv> (finite (dom \<sigma>) \<and> (\<forall> loc obj. (\<sigma>(loc)=Some (Obj obj)\<longrightarrow> finite (dom obj))))"

definition finite_Processes :: "(Request~=>(EContext list)) \<Rightarrow> bool"
  where
    "finite_Processes (processMap) \<equiv> finite (dom (processMap)) \<and>
       (\<forall> contList\<in>(ran(processMap)). \<forall>cont\<in> set contList. finite (dom(fst(cont))))"

primrec finite_Configuration :: "Configuration => bool"
  where
 " finite_Configuration (Cn AOs Futures) =
      (finite (dom AOs) \<and> finite (dom Futures) \<and> 
    (\<forall> futVal\<in>(ran Futures). \<forall> v \<sigma>. (futVal =FutVal v \<sigma> \<longrightarrow> finite_Store \<sigma>)) \<and> (*NB: Undefined futures are finite*)
    (\<forall> ao\<in>(ran AOs). \<forall> l \<sigma> P Q. ao = AO l \<sigma> P Q \<longrightarrow> finite_Store \<sigma> \<and> finite_Processes P))"
declare MultiASP.finite_Configuration.simps[simp del]

subsection {* serialization and location renaming *}

inductive serialize :: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ran(obj). \<exists>\<sigma>''. (serialize v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
     \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (FutRef f)  \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (StoredVal v)  \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
     "(serialize (ActRef f) \<sigma> \<sigma>')" |
     "serialize (null) \<sigma> \<sigma>' " | 
     "serialize (ASPInt n) \<sigma> \<sigma>'" | 
     "serialize (ASPBool b) \<sigma> \<sigma>'"

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
      \<longrightarrow> (\<exists> obj'. (\<sigma>'(\<psi>(l)) = Some (Obj obj') \<and> (\<forall> x  v. obj(x) = Some v \<longrightarrow> obj'(x)=Some (subst_Value v \<psi>)))))
    \<and>   (\<forall> f l . (\<sigma>(l) = Some (FutRef f) \<longrightarrow> \<sigma>'(\<psi>(l)) =Some (FutRef f)))
    \<and>   (\<forall> v l . (\<sigma>(l) = Some (StoredVal v) \<longrightarrow> 
      \<sigma>'(\<psi>(l)) = Some (StoredVal (subst_Value v \<psi>))))))"

definition serialize_and_rename :: "Value \<Rightarrow> Store \<Rightarrow> Value \<Rightarrow> Store \<Rightarrow> bool"
 where "serialize_and_rename v \<sigma> v' \<sigma>'  \<equiv> (\<exists>\<psi> \<sigma>''. serialize  v \<sigma> \<sigma>'' \<and>check_subst \<sigma>'' \<psi> \<sigma>'\<and>v'=subst_Value v \<psi>)"

definition serialize_and_rename_list :: "Value list \<Rightarrow> Store \<Rightarrow> Value list \<Rightarrow> Store \<Rightarrow> bool"
 where "serialize_and_rename_list vl \<sigma> vl' \<sigma>'  \<equiv> 
              (length vl=length vl' \<and>
              (\<exists>\<psi> \<sigma>''. (\<forall> i<length vl. serialize  (vl!i) \<sigma> \<sigma>''\<and>vl'!i=subst_Value (vl!i) \<psi>) \<and>check_subst \<sigma>'' \<psi> \<sigma>'))"

(*locale Generic_Functions = *)

(* semantics parameterized by compatibility and binder function*)
axiomatization 
  Compatible :: "(Request * Request) set"
and
  Bind:: "Object\<Rightarrow>MethodName\<Rightarrow>Value list\<Rightarrow> EContext "
and
  fields:: "ClassName \<Rightarrow>VarName list"
and 
  params:: "ClassName \<Rightarrow>VarName list"
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
  "(null, \<sigma>,  null)\<in>EvalValue" |
  "(ASPInt i, \<sigma>,  (ASPInt i) )\<in>EvalValue" |
  "(ASPBool b, \<sigma>,  (ASPBool b) )\<in>EvalValue" |
  "(ActRef \<alpha>, \<sigma>,  (ActRef \<alpha>) )\<in>EvalValue" |
  "\<sigma>(l) = Some (FutRef f) \<Longrightarrow>(ObjRef l, \<sigma>, ObjRef l)\<in>EvalValue" |
  "\<sigma>(l) = Some (Obj obj) \<Longrightarrow>(ObjRef l, \<sigma>, ObjRef l)\<in>EvalValue" |
  "\<lbrakk>\<sigma>(l) = Some (StoredVal v);(v,\<sigma>,ee)\<in> EvalValue\<rbrakk> \<Longrightarrow>(ObjRef l, \<sigma>, ee)\<in>EvalValue" 

lemma EvalValue_is_deterministic[rule_format,intro]: "(e,\<sigma>,v)\<in>EvalValue \<longrightarrow>(e,\<sigma>,v')\<in>EvalValue \<longrightarrow>v=v'"
apply (rule impI)
apply (erule EvalValue.induct)
apply auto
apply (erule EvalValue.cases,simp+)+
done

inductive_set EvalExpr:: "(Expression \<times> (VarName~=>Value)\<times>Store \<times> Value) set"
 where
   "(v,\<sigma>,ev)\<in>EvalValue \<Longrightarrow>(Val v,  locs, \<sigma>, ev)\<in>EvalExpr" |
   "\<lbrakk>locs(x)=Some v;(v,\<sigma>,ev)\<in>EvalValue\<rbrakk> \<Longrightarrow>(Var x,  locs, \<sigma>, ev)\<in>EvalExpr" |
   "\<lbrakk>locs(x)=None;locs(This)=Some (ObjRef or); (\<sigma>(or))=Some (Obj ob);
     ob(x) = Some v;(v,\<sigma>,ev)\<in>EvalValue\<rbrakk> 
                      \<Longrightarrow>(Var x,  locs, \<sigma>, ev)\<in>EvalExpr" |
   "\<lbrakk>(e,locs,\<sigma>,ASPInt i)\<in>EvalExpr;(e',locs,\<sigma>, ASPInt i')\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e +\<^sub>A e',  locs, \<sigma>, ASPInt (i+i'))\<in>EvalExpr" |
   "\<lbrakk>(e,locs,\<sigma>,ASPBool b)\<in>EvalExpr;(e',locs,\<sigma>,ASPBool b')\<in>EvalExpr\<rbrakk> 
                      \<Longrightarrow>(e &\<^sub>A e',  locs, \<sigma>, ASPBool (b\<and>b'))\<in>EvalExpr"

lemma EvalExpr_is_deterministic[rule_format,intro]: 
      " (e,locs,\<sigma>,v)\<in>EvalExpr \<longrightarrow> (\<forall> v'. (e,locs,\<sigma>,v')\<in>EvalExpr \<longrightarrow>v=v')"
apply (rule impI)
apply (erule EvalExpr.induct)
apply auto
apply (erule EvalExpr.cases,auto)
apply (erule EvalExpr.cases,auto)
apply (erule EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e+\<^sub>Ae'"  in EvalExpr.cases,auto)
apply (erule_tac ?a1.0="e&\<^sub>Ae'"  in EvalExpr.cases,auto)
done

thm EvalExpr_is_deterministic

inductive reduction :: "[Configuration, Configuration] => bool"  (infixl "\<leadsto>" 50)
  where
    Serve [simp, intro!]: 
      "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks (Rq@R#Rq')) ; R=(f,m,vl); 
        \<forall> Q\<in>dom(Tasks). (R,Q)\<in>Compatible;\<forall> Q\<in>set Rq. (R,Q)\<in>Compatible; 
         (\<sigma> l_\<alpha>) = Some (Obj obj);
        Bind obj m vl = (locs,s); locs'=locs(This\<mapsto>ObjRef l_\<alpha>);
        Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(R\<mapsto>[(locs',s)])) (Rq@Rq')))\<rbrakk> 
          \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

    AssignLocal  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL); RedContext S = R[[(x=\<^sub>AExpr e)]];
       x\<in>dom locs ; (e, locs, \<sigma>,v)\<in>EvalExpr;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs(x\<mapsto>v),R)#TL))) Rq)) 
      \<rbrakk> 
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

    AssignField  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL); RedContext S = R[[(x=\<^sub>AExpr e)]];
       x\<notin>dom locs ;locs(This) = Some (ObjRef l);\<sigma>(l) = Some (Obj obj);x\<in>dom(obj);  (e, locs, \<sigma>,v)\<in>EvalExpr;
       \<sigma>'=\<sigma>(l\<mapsto>Obj (obj(x\<mapsto>v)));
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma>' (Tasks(Q\<mapsto>((locs,R)#TL))) Rq)) 
      \<rbrakk> 
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

     New  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL);RedContext S = R[[x=\<^sub>Anew C(el)]];
       fields(C)=field_list; params(C)=param_list; l\<notin>dom \<sigma>; 
       length param_list = length el;length param_list = length value_list; 
       \<forall> i<length value_list . (el!i,locs,\<sigma>,value_list!i)\<in>EvalExpr ;
       \<sigma>'=\<sigma>(l\<mapsto> Obj (  (map_of (zip field_list (replicate (length field_list) null)))
                    ++ (map_of (zip param_list value_list)) )) ;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma>' (Tasks(Q\<mapsto>((locs,(x=\<^sub>AExpr (Val (ObjRef l));;R))#TL))) Rq)) 
      \<rbrakk>  
      (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

     NewActive  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL); RedContext S = R[[x=\<^sub>AnewActive C(el)]];
       fields(C)=field_list; params(C)=param_list; \<gamma>\<notin>dom Activities; 
       length param_list = length el;length param_list = length value_list; 
       \<forall> i<length value_list . ((el!i,locs,\<sigma>,value_list!i)\<in>EvalExpr \<and> serialize (value_list!i) \<sigma> \<sigma>\<^sub>0) ;
       l\<notin>dom \<sigma>\<^sub>0;
       \<sigma>'=\<sigma>\<^sub>0(l\<mapsto> Obj (  (map_of (zip field_list (replicate (length field_list) null)))
                    ++ (map_of (zip param_list value_list)) )) ;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs,(x=\<^sub>AExpr (Val (ActRef \<gamma>)));;R)#TL))) Rq))
                             (\<gamma>\<mapsto> (AO l \<sigma>' empty [])) 
       (* new term to evaluate is artificially complex because obj ref has to be encapsulated in a value and an expression*)
     \<rbrakk>   
        \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

   InvkActive  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       (Activities \<beta>) = Some (AO l\<^sub>\<beta> \<sigma>\<^sub>\<beta> Tasks\<^sub>\<beta> Rq\<^sub>\<beta>); 
       Tasks Q = Some ((locs,S)#TL);RedContext S = R[[x=\<^sub>A(e.\<^sub>Am(el))]];
       (e,locs,\<sigma>,ActRef \<beta>)\<in>EvalExpr;
       f\<notin>dom Futures;      l\<notin>dom \<sigma>;
       length value_list = length el; 
       \<forall> i<length value_list . ((el!i,locs,\<sigma>,value_list!i)\<in>EvalExpr) ;
       serialize_and_rename_list value_list \<sigma> value_list' \<sigma>\<^sub>P; dom \<sigma>\<^sub>P\<inter>dom \<sigma>\<^sub>\<beta>={};  
       \<sigma>'=\<sigma>\<^sub>\<beta> ++ \<sigma>\<^sub>P;
       Activities'=Activities(\<alpha>\<mapsto> AO l_\<alpha> (\<sigma>(l\<mapsto>FutRef f)) (Tasks(Q\<mapsto>((locs,x=\<^sub>AExpr (Val (ObjRef l));;R)#TL))) Rq)
                             (\<beta>\<mapsto> AO l\<^sub>\<beta> \<sigma>' Tasks\<^sub>\<beta> (Rq\<^sub>\<beta>@[(f,m,value_list')]) ) 
      \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' (Futures(f\<mapsto>Undefined))" |

   InvkPassive  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL); RedContext S = R[[x=\<^sub>Ae.\<^sub>Am(el)]];
       (e,locs,\<sigma>,ObjRef l)\<in>EvalExpr;
         (\<sigma> l) = Some (Obj obj);
       length vl = length el; \<forall> i<length vl . ((el!i,locs,\<sigma>,vl!i)\<in>EvalExpr) ;
        Bind obj m vl = (locs,s); locs'=locs(This\<mapsto>ObjRef l);
       Activities'=Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs',s)#(locs,x=\<^sub>AHole;;R)#TL))) Rq) 
      \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

   ReturnLocal  [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs',S)#(locs,x=\<^sub>AHole;;R)#TL); RedContext S = R[[return e]];
       (e,locs,\<sigma>,v)\<in>EvalExpr;
       Activities'=Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma> 
                              (Tasks(Q\<mapsto>((locs,x=\<^sub>AExpr (Val v);;R)#TL))) Rq) 
      \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures" |

   ReturnRequest [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some [(locs',S)]; RedContext S = R[[return e]];
       Q=(f,m,vl);
       (e,locs,\<sigma>,v)\<in>EvalExpr;  serialize v \<sigma> \<sigma>\<^sub>f;
       Activities'=Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma> (Tasks|``Q) Rq) 
      \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' (Futures(f\<mapsto>FutVal v \<sigma>\<^sub>f))" |

    UpdateFuture [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       (\<sigma> l) = Some (FutRef f);  (Futures f) = Some (FutVal v \<sigma>\<^sub>f); 
       check_subst \<sigma>\<^sub>f \<psi> \<sigma>\<^sub>r; v'=subst_Value v \<psi>; (dom \<sigma>\<^sub>r)\<inter>(dom \<sigma>)= {};
       \<sigma>'=(\<sigma>++\<sigma>\<^sub>r)(l\<mapsto>StoredVal v'); Activities'=Activities(\<alpha>\<mapsto> AO l_\<alpha> \<sigma>' Tasks Rq) 
      \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures"   |

    IfThenElseTrue [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL);RedContext S = R[[IF e THEN s\<^sub>t ELSE s\<^sub>e]];
       (e,locs,\<sigma>,ASPBool True)\<in>EvalExpr;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs,s\<^sub>t;;R)#TL))) Rq))
   \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures"  |
    IfThenElseFalse [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL);RedContext S = R[[IF e THEN s\<^sub>t ELSE s\<^sub>e]];
       (e,locs,\<sigma>,ASPBoolFalse)\<in>EvalExpr;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs,s\<^sub>e;;R)#TL))) Rq))
   \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures"  |

    Skip [simp, intro!]: 
     "\<lbrakk>(Activities \<alpha>) = Some (AO l_\<alpha> \<sigma> Tasks Rq); 
       Tasks Q = Some ((locs,S)#TL);RedContext S = R[[Skip]];R\<noteq>Skip;
       Activities'=Activities(\<alpha>\<mapsto> (AO l_\<alpha> \<sigma> (Tasks(Q\<mapsto>((locs,R)#TL))) Rq))
   \<rbrakk>  
      \<Longrightarrow> Cn Activities Futures \<leadsto>Cn Activities' Futures"  
      
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

abbreviation InitialConfiguration:: "(VarName list) \<Rightarrow>Statement \<Rightarrow> Configuration"
where
  "InitialConfiguration vl s \<equiv> Cn (empty(0\<mapsto>(AO 0 (empty(0\<mapsto>Obj empty)) 
                  (empty((0,''m'',[])\<mapsto>[((map_of (zip vl (replicate (length vl) null))),s)])) []))) empty"




inductive Comp2 :: "(Request * Request) \<Rightarrow>bool"
 where
  symmetric_compatible: " Comp2 (x,y) \<Longrightarrow>Comp2 (y,x) "

end
