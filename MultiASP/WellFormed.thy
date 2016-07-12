(*    Author:     Ludovic Henrio and Florian Kammuller
                2014
    Note:       Multi-active object formalisation
                well formed program and configurations
*)
(*Conventions (reminder, cf MultiASP.thy):
  l = location in store
  x,y=varname
  locs = local variables
  l_\<alpha> = location in the local store of the active object of \<alpha>
 Stl = statement list
 EContext is an execution context, ie a thread 
 EcL = EContext list*)


(* TODO: remove commented STL2*)

theory WellFormed imports MultiASP begin

subsection {* Collectors *}
(* element collectors: a set of function that collects  a kind of references (AO, futs or locations) in different parts of a configuration *)
primrec Collector_Expression:: "Expression \<Rightarrow> (Value \<Rightarrow> 'a set)\<Rightarrow> 'a set"
where
 "Collector_Expression (Val v) Collector_Value = Collector_Value v" |
 "Collector_Expression (Var x) Collector_Value= {}" |
 "Collector_Expression (e +\<^sub>A e') Collector_Value= 
            Collector_Expression e Collector_Value\<union> Collector_Expression e' Collector_Value" |
 "Collector_Expression (e &\<^sub>A e') Collector_Value= 
            Collector_Expression e Collector_Value\<union> Collector_Expression e' Collector_Value" |
 "Collector_Expression (e ==\<^sub>A e') Collector_Value= 
            Collector_Expression e Collector_Value\<union> Collector_Expression e' Collector_Value" 

primrec Collector_Rhs:: "Rhs \<Rightarrow> (Value \<Rightarrow> 'a set)\<Rightarrow>'a set"
where
 "Collector_Rhs (Expr e) Collector_Value= Collector_Expression e Collector_Value" |
 "Collector_Rhs (e.\<^sub>Am(el)) Collector_Value= 
            Collector_Expression e Collector_Value \<union> (listunionMap (\<lambda>x. Collector_Expression x Collector_Value) el )" |
 "Collector_Rhs (new C(el)) Collector_Value=   (listunionMap (\<lambda>x. Collector_Expression x Collector_Value) el)" |
 "Collector_Rhs (newActive C(el)) Collector_Value=  (listunionMap (\<lambda>x. Collector_Expression x Collector_Value) el)" |
 "Collector_Rhs (Hole) Collector_Value =  {}"

primrec Collector_Stl:: "Statement list \<Rightarrow>(Value \<Rightarrow> 'a set)\<Rightarrow> 'a set"
 (* and Collector_Stl_2:: "Statement list \<Rightarrow>(Value \<Rightarrow> 'a set)\<Rightarrow> 'a set" *)
and Collector_Statement:: "Statement  \<Rightarrow>(Value \<Rightarrow> 'a set)\<Rightarrow> 'a set"  
where
 "Collector_Stl [] Collector_Value= {}" |
 "Collector_Stl (S;;Stl) Collector_Value= Collector_Statement S Collector_Value \<union> Collector_Stl Stl Collector_Value" |
 (* "Collector_Stl_2 [] Collector_Value= {}" |
  "Collector_Stl_2 (S;;Stl) Collector_Value= Collector_Statement S Collector_Value \<union> Collector_Stl_2 Stl Collector_Value" | *)
 "Collector_Statement (x=\<^sub>Ae) Collector_Value= Collector_Rhs e Collector_Value" |
 "Collector_Statement (Return e) Collector_Value= Collector_Expression e Collector_Value" |
 "Collector_Statement (IF e THEN Stl ELSE Stl') Collector_Value= 
           Collector_Expression e Collector_Value
           \<union> (Collector_Stl Stl Collector_Value)
           \<union> (Collector_Stl Stl' Collector_Value) " 


primrec Collector_Storable:: "Storable \<Rightarrow> (Value \<Rightarrow> 'a set)\<Rightarrow>(FutName \<Rightarrow> 'a set)\<Rightarrow> 'a set"
where
  "Collector_Storable (Obj obj)  Collector_Value Collector_FutName=  Union (Collector_Value ` (ran (fst obj)))" |
  "Collector_Storable (StoredVal v)  Collector_Value Collector_FutName= Collector_Value v" | 
  "Collector_Storable (FutRef f)  Collector_Value Collector_FutName= Collector_FutName f"

definition Collector_Request:: "Request \<Rightarrow> (Value \<Rightarrow> 'a set)\<Rightarrow> 'a set "
where
 "Collector_Request Req Collector_Value \<equiv> listunionMap Collector_Value (snd (snd Req))" 

definition Collector_EContext:: "EContext \<Rightarrow>  (Value \<Rightarrow> 'a set)\<Rightarrow> 'a set"
where
 "Collector_EContext EC Collector_Value\<equiv> Union (Collector_Value ` (ran (EC_locs EC))) \<union>  Collector_Stl (EC_Stl EC) Collector_Value" 

primrec Collector_ActiveObject:: "ActiveObject \<Rightarrow> (Value \<Rightarrow> 'a set)\<Rightarrow>(FutName \<Rightarrow> 'a set)\<Rightarrow>  'a set"
 where
 "Collector_ActiveObject (AO l \<sigma> tasks Rq) Collector_Value Collector_FutName= 
        Union ((\<lambda>x. Collector_Storable x Collector_Value Collector_FutName) ` (ran \<sigma>)) 
           \<union> listunionMap (\<lambda> x . Collector_Request x Collector_Value) Rq 
           \<union> Union {listunionMap (\<lambda>x. Collector_EContext x Collector_Value)  ECl| ECl. ECl\<in>ran tasks}"

primrec Collector_FutValue:: "FutValue \<Rightarrow> (Value \<Rightarrow> 'a set)\<Rightarrow> (FutName \<Rightarrow> 'a set)\<Rightarrow>  'a set"
 where
 "Collector_FutValue Undefined Collector_Value Collector_FutName= {}" |
 "Collector_FutValue (FutVal v \<sigma>) Collector_Value Collector_FutName= Collector_Value v 
                                   \<union> Union ((\<lambda>x. Collector_Storable x Collector_Value Collector_FutName)` (ran \<sigma>)) "

(* variable name collector: a set of function that collects  a kind of name (vars, methods or classes)
 in different parts of a configuration *)
primrec VarNameCollector_Expression:: "Expression \<Rightarrow> VarName set"
where
 "VarNameCollector_Expression (Val v) = {}" |
 "VarNameCollector_Expression (Var x)= (case x of Id x \<Rightarrow>{x} | This \<Rightarrow> {})" |
 "VarNameCollector_Expression (e +\<^sub>A e') = 
            VarNameCollector_Expression e \<union> VarNameCollector_Expression e'" |
 "VarNameCollector_Expression (e &\<^sub>A e')= 
            VarNameCollector_Expression e \<union> VarNameCollector_Expression e' " |
 "VarNameCollector_Expression (e ==\<^sub>A e')= 
            VarNameCollector_Expression e \<union> VarNameCollector_Expression e' " 

primrec VarNameCollector_Rhs:: "Rhs \<Rightarrow>VarName set"
where
 "VarNameCollector_Rhs (Expr e) = VarNameCollector_Expression e " |
 "VarNameCollector_Rhs (e.\<^sub>Am(el)) = 
            VarNameCollector_Expression e \<union> (listunionMap (\<lambda>x. VarNameCollector_Expression x) el )" |
 "VarNameCollector_Rhs (new C(el)) =   (listunionMap (\<lambda>x. VarNameCollector_Expression x) el)" |
 "VarNameCollector_Rhs (newActive C(el)) =  (listunionMap (\<lambda>x. VarNameCollector_Expression x) el)" |
 "VarNameCollector_Rhs (Hole) =  {}"

primrec NameCollector_Stl:: "Statement list \<Rightarrow>(Expression \<Rightarrow> 'a set)\<Rightarrow>(Rhs \<Rightarrow> 'a set)\<Rightarrow> 'a set"
(*and NameCollector_Stl_2:: "Statement list \<Rightarrow>(Expression \<Rightarrow> 'a set) \<Rightarrow>(Rhs \<Rightarrow> 'a set)\<Rightarrow> 'a set"*)
and NameCollector_Statement:: "Statement \<Rightarrow>(Expression \<Rightarrow> 'a set)  \<Rightarrow>(Rhs \<Rightarrow> 'a set)\<Rightarrow> 'a set"  
where
 "NameCollector_Stl []  NameCollector_Expression NameCollector_Rhs= {}" |
 "NameCollector_Stl (S;;Stl) NameCollector_Expression NameCollector_Rhs= 
        NameCollector_Statement S NameCollector_Expression NameCollector_Rhs\<union> NameCollector_Stl Stl NameCollector_Expression NameCollector_Rhs" |
(* "NameCollector_Stl_2 [] NameCollector_Expression NameCollector_Rhs= {}" |
 "NameCollector_Stl_2 (S;;Stl) NameCollector_Expression NameCollector_Rhs=
        NameCollector_Statement S NameCollector_Expression NameCollector_Rhs\<union> NameCollector_Stl_2 Stl NameCollector_Expression NameCollector_Rhs" |*)
 "NameCollector_Statement (x=\<^sub>Ae) NameCollector_Expression NameCollector_Rhs= NameCollector_Rhs e" |
 "NameCollector_Statement (Return e) NameCollector_Expression NameCollector_Rhs= NameCollector_Expression e" |
 "NameCollector_Statement (IF e THEN Stl ELSE Stl') NameCollector_Expression NameCollector_Rhs= 
           NameCollector_Expression e 
           \<union> (NameCollector_Stl Stl NameCollector_Expression NameCollector_Rhs)
           \<union> (NameCollector_Stl Stl' NameCollector_Expression NameCollector_Rhs) " 

abbreviation EmptyCollector where
"EmptyCollector x \<equiv>{}"


primrec ClassNameCollector_Rhs:: "Rhs \<Rightarrow>ClassName set"
where
 "ClassNameCollector_Rhs (Expr e) = {} " |
 "ClassNameCollector_Rhs (e.\<^sub>Am(el)) = {}" |
 "ClassNameCollector_Rhs (new C(el)) =   {C}" |
 "ClassNameCollector_Rhs (newActive C(el)) =  {C}" |
 "ClassNameCollector_Rhs (Hole) =  {}"


(* location reference collectors *)
definition Referenced_locations_Value:: "Value \<Rightarrow> Location set"
where  "Referenced_locations_Value v \<equiv> (case v of ObjRef l \<Rightarrow>{l} | _ \<Rightarrow> {})"

definition Referenced_locations_Stl:: "Statement list \<Rightarrow> Location set"
where  "Referenced_locations_Stl stl \<equiv> Collector_Stl stl Referenced_locations_Value"

definition Referenced_locations_Storable:: "Storable \<Rightarrow> Location set"
where  "Referenced_locations_Storable x \<equiv> Collector_Storable x Referenced_locations_Value EmptyCollector"

(* AO reference collectors *)

definition Referenced_AOs_Value:: "Value \<Rightarrow> ActName set"
where  "Referenced_AOs_Value v \<equiv> (case v of ActRef a \<Rightarrow>{a} | _ \<Rightarrow> {})"

definition Referenced_AOs_Stl:: "Statement list \<Rightarrow> Location set"
where  "Referenced_AOs_Stl stl \<equiv> Collector_Stl stl Referenced_AOs_Value"

definition Referenced_AOs_ActiveObject:: "ActiveObject \<Rightarrow> ActName set"
where  "Referenced_AOs_ActiveObject x \<equiv> Collector_ActiveObject x Referenced_AOs_Value EmptyCollector"

definition Referenced_AOs_FutValue:: "FutValue \<Rightarrow> ActName set"
where  "Referenced_AOs_FutValue x \<equiv> Collector_FutValue x Referenced_AOs_Value EmptyCollector"

(* Future reference collectors *)
definition Future_Collector:: "FutName \<Rightarrow> FutName set"
where  "Future_Collector \<equiv> \<lambda> x. {x}"

definition Referenced_futures_ActiveObject:: "ActiveObject \<Rightarrow> FutName set"
where  "Referenced_futures_ActiveObject x \<equiv> Collector_ActiveObject x EmptyCollector Future_Collector"

definition Referenced_futures_FutValue:: "FutValue \<Rightarrow> FutName set"
where  "Referenced_futures_FutValue x \<equiv> Collector_FutValue x EmptyCollector Future_Collector"

(*VarName collector*)
definition VarName_Collector_Stl:: "Statement list \<Rightarrow> VarName set"
where  "VarName_Collector_Stl stl\<equiv> NameCollector_Stl stl VarNameCollector_Expression VarNameCollector_Rhs"

(*ClassName collector*)
definition ClassName_Collector_Stl:: "Statement list \<Rightarrow> ClassName set"
where  "ClassName_Collector_Stl stl\<equiv> NameCollector_Stl stl EmptyCollector ClassNameCollector_Rhs"

section{*Definition of well formed programs*}


definition Well_formed_method
where
"Well_formed_method IL field_list CL M\<equiv>case MethSignature M of Method itfN methN  param_list \<Rightarrow>
  Interface_set_from_variable_list param_list\<subseteq>set IL \<and>
  Interface_set_from_variable_list (LocalVariables M)\<subseteq>set IL \<and>
  distinct (map snd param_list@map snd (LocalVariables M)) \<and>
  VarName_Collector_Stl (Body M)\<subseteq> set (map snd (field_list @(LocalVariables M)@param_list)) \<and>
                    (* referenced variables are declared *)
  Referenced_locations_Stl (Body M)={} \<and>  (* no location reference *)
  Referenced_AOs_Stl (Body M)={} \<and>   (* no AO reference *)
  ClassName_Collector_Stl (Body M)\<subseteq>set (map Name CL)   (* referenced classnames declared *)
"

definition Well_formed_Class
where
"Well_formed_Class IL CL C \<equiv> let field_list = (ClassParameters C)@(StateVariables C) in
  set (Interfaces C)\<subseteq>set IL \<and>
  Interface_set_from_variable_list (ClassParameters C)\<subseteq>set IL \<and>
  Interface_set_from_variable_list (StateVariables C)\<subseteq>set IL \<and>
  distinct (map snd field_list) \<and>
                        (* fields, i.e. state vars and class parameters all have distinct names *)
  (\<forall> M\<in>set (Methods C). Well_formed_method IL field_list CL M)
"
definition Well_formed_Program
where
"Well_formed_Program prog\<equiv> case prog of (Prog IL CL vars stl) \<Rightarrow>
  let itf_names = (map IName IL) in
    distinct  itf_names\<and>   (* all interfaces have distinct names*)
    distinct (map Name CL) \<and> (* all classes have distinct names*)
    (\<forall> C \<in> set CL. Well_formed_Class itf_names CL C) (* all classes are well formed*) \<and>
    Referenced_locations_Stl stl={} \<and>  (* no location *)
    Referenced_AOs_Stl stl={}\<and> (* no AO reference *)
    VarName_Collector_Stl stl\<subseteq>set (map snd vars) \<and> (* referenced variables are declared *)
    ClassName_Collector_Stl stl\<subseteq>set (map Name CL) \<and> (* referenced classnames declared *)
    emptyObjClass\<in>set CL
"

section{*Definition of Well Formed configurations *}
(* WELL FORMED *)
                                 
primrec Well_formed_activity :: " Program \<Rightarrow>ActiveObject \<Rightarrow>bool"
where
"Well_formed_activity prog  (AO l \<sigma> P Q)= (l\<in>dom \<sigma> \<and> (*l refers to a loc in the store*)
                                      (\<forall>l' x.  (*references inside the store are not dangling*)
                                        (\<sigma> l'=Some x) \<longrightarrow>(Referenced_locations_Storable x\<subseteq>dom \<sigma>) ) \<and>
                     (*references in request parameters point to the store *)
                                       (\<forall> f m vl l'' j. (( (f,m,vl)\<in>dom P) \<or> (j<length Q\<and>(Q!j) = (f,m,vl)))\<longrightarrow> 
                                          (\<forall>i<length vl. ((vl!i) = ObjRef l'' \<longrightarrow>l''\<in>dom \<sigma>))) \<and> 
                                       (\<forall> f m vl EcL l'' j x. 
                                          (((P (f,m,vl)= Some EcL\<and>j<length EcL)\<longrightarrow>
                                            ( (EC_locs(EcL!j)) x=Some (ObjRef l'') \<or>
                                              l''\<in>Referenced_locations_Stl (EC_Stl(EcL!j)))        
                                             \<longrightarrow>l''\<in>dom \<sigma>))) \<and>
                    (* referenced variables are declared *) 
                                       (\<forall> f m vl EcL j. 
                                          ((P (f,m,vl)= Some EcL\<and>j<length EcL)\<longrightarrow>
                                            (\<exists>  fields CN. 
                                             \<sigma> (EC_location (EcL!j)) = Some (Obj (fields, CN)) \<and>
                                              VarName_Collector_Stl (EC_Stl(EcL!j))\<subseteq>dom(EC_locs(EcL!j))\<union>dom(fields)))) \<and>
                    (* Class of the object in the store is defined and with the same fields *)
                                        (\<forall>l' obj_fields CN.  
                                         ( \<sigma> l' = Some (Obj (obj_fields, CN)) 
                                         \<longrightarrow> ((\<exists>C. fetchClass prog CN = Some C) \<and>
                                              dom obj_fields = set (fields prog CN) \<union> set (params prog CN) ))) \<and>
                    (* classes referenced in new exist*)
                                       (\<forall> f m vl EcL j. 
                                          ((P (f,m,vl)= Some EcL\<and>j<length EcL)\<longrightarrow>
                                           ClassName_Collector_Stl (EC_Stl(EcL!j))\<subseteq>DefinedClassNames prog))
)"

primrec Well_formed_future :: " FutValue \<Rightarrow> bool"
where
"Well_formed_future (Undefined) = True" |
"Well_formed_future (FutVal v \<sigma>) = ((\<forall> l  x. (\<sigma> l = Some x\<longrightarrow>(Referenced_locations_Storable x\<subseteq>dom \<sigma>))) \<and>
                                   (\<forall> l''. v =  (ObjRef l'') \<longrightarrow>l''\<in>dom \<sigma>))" 

primrec Computed_futures:: "ActiveObject \<Rightarrow> FutName set"
 where
 "Computed_futures (AO l \<sigma> tasks Rq) = {f. (\<exists> m vl. (f,m,vl)\<in>set Rq)}
                                         \<union> {f.(\<exists> m vl.  (f,m,vl)\<in>dom tasks)} "

primrec Well_formed :: "Program \<Rightarrow>Configuration \<Rightarrow> bool"
where
  "Well_formed prog (Cn AOs futures) = 
        ((\<forall> \<alpha> ao. (AOs \<alpha> =Some ao \<longrightarrow> Well_formed_activity prog ao)) \<and>
        (\<forall> f fv. (futures f = Some fv \<longrightarrow> Well_formed_future fv)) \<and>
        (\<forall> \<alpha> ao. (AOs \<alpha> =Some ao \<longrightarrow> (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject ao. \<beta>\<in>dom AOs))) \<and>
        (\<forall> f fv. (futures f = Some fv \<longrightarrow> (\<forall>\<beta>\<in>Referenced_AOs_FutValue fv. \<beta>\<in>dom AOs))) \<and>
        (\<forall> \<alpha> ao. (AOs \<alpha> =Some ao \<longrightarrow> (\<forall>f'\<in>Referenced_futures_ActiveObject ao. f'\<in>dom futures))) \<and>
        (\<forall> f fv. (futures f = Some fv \<longrightarrow>  (\<forall>f'\<in>Referenced_futures_FutValue fv. f'\<in>dom futures))) \<and>
        (\<forall> f . (futures f = Some Undefined =(\<exists> \<beta> ao. (AOs \<beta>) = Some ao \<and>f \<in>Computed_futures ao))))
        "

inductive Comp2 :: "(Request * Request) \<Rightarrow>bool"
 where
  symmetric_compatible: " Comp2 (x,y) \<Longrightarrow>Comp2 (y,x) "

section{* simple lemmas on collectors*}
lemma Computed_futureD: "f\<in>Computed_futures (AO l \<sigma> tasks Rq) \<Longrightarrow> (\<exists> m vl. (f,m,vl)\<in>set Rq)\<or>(\<exists> m vl.  (f,m,vl)\<in>dom tasks)"
(* computed future def applied to the case where we have an element f in the set *)
by (auto simp: Computed_futures_def)

lemma Referenced_AOs_FutValue_Undefined[simp]: "Referenced_AOs_FutValue Undefined={}"
(* an undefined future references no AO *)
by (auto simp: Referenced_AOs_FutValue_def)

lemma Referenced_futures_FutValue_Undefined[simp]: "Referenced_futures_FutValue Undefined={}"
(* an undefined future references no future *)
by (auto simp: Referenced_futures_FutValue_def)

lemma emptycollector_Expression_empty: "Collector_Expression e EmptyCollector={}"
(* empty collector returns an empty set - expression case*)
by (induct_tac e, auto)

lemma emptycollector_empty[simp]: " Collector_Statement s EmptyCollector={}"
(* empty collector returns an empty set statement case*)
apply (rule Collector_Statement.induct[where ?P2.0="\<lambda>list. Collector_Stl list EmptyCollector={}" ])
apply (case_tac x2)
apply (auto simp: emptycollector_Expression_empty)
done

lemma emptycollector_Stl_empty[simp]: " Collector_Stl stl EmptyCollector={}"
(* empty collector returns an empty set statement list case*)
by (induct_tac stl, auto)

lemma emptycollector_EContext_empty[simp]: " Collector_EContext E EmptyCollector={}"
(* empty collector returns an empty set EContext case*)
by (induct E, auto simp: Collector_EContext_def)

declare Referenced_locations_Value_def[simp] Referenced_locations_Storable_def[simp] Referenced_locations_Stl_def[simp]
 Referenced_AOs_Value_def[simp]
VarName_Collector_Stl_def[simp] Referenced_AOs_Stl_def[simp] ran_def[simp] listunionMap_def[simp] 

lemma Referenced_location_storable_emptyobj[simp]: "Referenced_locations_Storable emptyObj = {}"
(* an empty object references no location*)
by (auto simp: emptyObj_def)

lemma Collector_storable_emptyobj[simp]: "Collector_Storable emptyObj EmptyCollector Future_Collector={}"
(* an empty object references no future*)
by (auto simp: emptyObj_def)

lemma Referenced_AOs_Value_ref[simp]: "Referenced_AOs_Value (ObjRef l) ={}"
(* an location ref references no AO*)
by auto

lemma Referenced_AOs_Value_null[simp]: "Referenced_AOs_Value (null) ={}"
(* an null references no AO*)
by auto

lemma Collector_Stl_append_pre: 
" Collector_Stl (Stl @ [a]) f = Collector_Stl Stl f\<union>Collector_Statement a f"
by (induct_tac Stl,auto)

lemma Collector_Stl_append[rule_format, simp]: 
"\<forall> Stl. Collector_Stl (Stl @ Stl') f = Collector_Stl Stl f\<union>Collector_Stl Stl' f"
(*collector of concatenation of statement lists is union of collectors *)
apply (induct_tac Stl')
apply simp
apply clarify
apply (drule_tac x="Stl@[a]" in spec)
apply (auto simp: Collector_Stl_append_pre)
done

lemma NameCollector_Stl_append_pre: 
" NameCollector_Stl (Stl @ [a]) f g= NameCollector_Stl Stl f g\<union>NameCollector_Statement a f g"
by (induct_tac Stl,auto)

lemma NameCollector_Stl_append[rule_format, simp]: 
(*Name collector of concatenation of statement lists is union of Name collectors *)
"\<forall> Stl. NameCollector_Stl (Stl @ Stl') f g= NameCollector_Stl Stl f g\<union>NameCollector_Stl Stl' f g"
apply (induct_tac Stl')
apply simp
apply clarify
apply (drule_tac x="Stl@[a]" in spec)
apply (auto simp: NameCollector_Stl_append_pre)
done

lemma ClassNameCollector_Stl_append[simp]: 
"ClassName_Collector_Stl (Stl @ Stl') = ClassName_Collector_Stl Stl \<union>ClassName_Collector_Stl Stl'"
(*lemma NameCollector_Stl_append above applied to classname *)
by (simp add: ClassName_Collector_Stl_def)

(*lemma Collector_Stl2_is_Collector_Stl: 
"Collector_Stl_2 Stl f = Collector_Stl Stl  f "
(* states that collector_STL_2 and collector_Stl compute the same thing *)
by (induct_tac Stl, auto)*)


(*lemma NameCollector_Stl2_is_NameCollector_Stl: 
"NameCollector_Stl_2 Stl f g= NameCollector_Stl Stl  f g"
(* states that Namecollector_STL_2 and Namecollector_Stl compute the same thing *)
by (induct_tac Stl, auto)
*)

lemma Collector_Stl_tail_Stl: 
       "j<length ((l_this, locs', Stl) # EcL) \<Longrightarrow>
         l'' \<in> Collector_Stl (EC_Stl (((l_this, locs', Stl) # EcL) ! j)) Referenced_locations_Value \<Longrightarrow>
        l'' \<in> Collector_Stl (EC_Stl (((l_this, locs, s;;Stl) # EcL) ! j)) Referenced_locations_Value"
by (cases j, auto)

lemma ClassName_Collector_Stl_tail_Stl: 
        "l'' \<in> ClassName_Collector_Stl (EC_Stl (((l_this, locs', Stl) # EcL) ! j)) \<Longrightarrow> 
         j<length ((l_this, locs', Stl) # EcL) \<Longrightarrow>
              l'' \<in> ClassName_Collector_Stl (EC_Stl (((l_this, locs, s;;Stl) # EcL) ! j)) "
by (cases j, auto simp: ClassName_Collector_Stl_def)

lemma ClassName_Collector_Stl_Then: 
        "l'' \<in> ClassName_Collector_Stl (EC_Stl (((l_this, locs', st@Stl) # EcL) ! j)) \<Longrightarrow> 
         j<length ((l_this, locs', Stl) # EcL) \<Longrightarrow>
              l'' \<in> ClassName_Collector_Stl (EC_Stl (((l_this, locs, (IF e THEN st ELSE se);;Stl) # EcL) ! j)) "
by (cases j, auto simp: ClassName_Collector_Stl_def)

lemma ClassName_Collector_Stl_Else: 
        "l'' \<in> ClassName_Collector_Stl (EC_Stl (((l_this, locs', se@Stl) # EcL) ! j)) \<Longrightarrow> 
         j<length ((l_this, locs', Stl) # EcL) \<Longrightarrow>
              l'' \<in> ClassName_Collector_Stl (EC_Stl (((l_this, locs, (IF e THEN st ELSE se);;Stl) # EcL) ! j)) "
by (cases j, auto simp: ClassName_Collector_Stl_def )


lemma AOs_Collector_Stl_tail_Stl: 
      "tasks R = Some ((l_this, locs, s;;Stl) # EcL) \<Longrightarrow>
       Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs, Stl) # EcL)) Rq) \<subseteq> Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks) Rq)"
apply (clarsimp simp: Referenced_AOs_ActiveObject_def)
apply (case_tac "R=(ab,ac,ba)")
apply (drule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) 
                           ((l_this, locs, s ;; Stl) # EcL)) {}" in spec)
apply (force simp: Collector_EContext_def)
apply (drule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) 
                           ECl) {}" in spec)
apply (force )
done

lemma AOs_Collector_Stl_Then: 
      "tasks R = Some ((l_this, locs, (IF e THEN st ELSE se);;Stl) # EcL) \<Longrightarrow>
       Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs, st@Stl) # EcL)) Rq) \<subseteq> Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks) Rq)"
apply (clarsimp simp: Referenced_AOs_ActiveObject_def)
apply (case_tac "R=(ab,ac,ba)")
apply (drule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) 
                           ((l_this, locs, (IF e THEN st ELSE se);; Stl) # EcL)) {}" in spec,clarsimp)
apply (force simp: Collector_EContext_def)
apply (drule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) 
                           ECl) {}" in spec)
apply (force)
done

lemma AOs_Collector_Stl_Else: 
      "tasks R = Some ((l_this, locs, (IF e THEN st ELSE se);;Stl) # EcL) \<Longrightarrow>
       Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs, se@Stl) # EcL)) Rq) \<subseteq> Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks) Rq)"
apply (clarsimp simp: Referenced_AOs_ActiveObject_def)
apply (case_tac "R=(ab,ac,ba)")
apply clarsimp
apply (drule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) 
                           ((l_this, locs, (IF e THEN st ELSE se);; Stl) # EcL)) {}" in spec)
apply (force simp: Collector_EContext_def)
apply (drule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) 
                           ECl) {}" in spec)
apply (force)
done

section {*well-formedness basic lemmas *}
lemma WF_class_in_program: "Well_formed_Program (Prog IL CL vl sl) \<Longrightarrow>C\<in>set CL\<Longrightarrow>Well_formed_Class (map IName IL) CL C"
by (auto simp add: Well_formed_Program_def Let_def)


lemma ActRef_EvalValue_pre: " (v,\<sigma>,val)\<in>EvalValue \<Longrightarrow> (\<forall>\<alpha>. val = ActRef \<alpha>\<longrightarrow> (v = ActRef \<alpha>\<or> (\<exists>l. \<sigma> l = Some (StoredVal (ActRef \<alpha>)))))"
by (erule EvalValue.induct, auto  )


lemma  ActRef_EvalValue: " (v,\<sigma>,ActRef \<alpha>)\<in>EvalValue \<Longrightarrow> v = ActRef \<alpha>\<or> (\<exists>l. \<sigma> l = Some (StoredVal (ActRef \<alpha>)))"
by (drule ActRef_EvalValue_pre ,auto  )


lemma ActRef_EvalExpr_pre: 
"(e,l, locs, \<sigma>,v)\<in>EvalExpr \<Longrightarrow> 
  (\<forall> \<alpha>. v = ActRef \<alpha> \<longrightarrow>  
     (e = Val (ActRef \<alpha>) \<or> 
     (\<exists>l. \<sigma> l = Some (StoredVal (ActRef \<alpha>))) \<or>
     (\<exists>x. locs x = Some (ActRef \<alpha>)) \<or> 
     (\<exists> l x obj_fields C.  (\<sigma> l = Some (Obj (obj_fields,C)) \<and> obj_fields x = Some (ActRef \<alpha>)))))"
apply (erule MultiASP.EvalExpr.induct)
apply ( auto )
apply (drule ActRef_EvalValue,blast)+
done

lemma  ActRef_EvalExpr: 
" (e,l, locs, \<sigma>,ActRef \<alpha>)\<in>EvalExpr \<Longrightarrow> 
  (e = Val (ActRef \<alpha>) \<or> 
     (\<exists>l. \<sigma> l = Some (StoredVal (ActRef \<alpha>))) \<or>
     (\<exists>x. locs x = Some (ActRef \<alpha>)) \<or> 
     (\<exists> l x obj_fields C.  (\<sigma> l = Some (Obj (obj_fields,C)) \<and> obj_fields x = Some (ActRef \<alpha>))))"
by (drule ActRef_EvalExpr_pre,auto  )

lemma ObjRef_EvalValue_pre: " (v,\<sigma>,val)\<in>EvalValue \<Longrightarrow> (\<forall> l. val = ObjRef l\<longrightarrow> l\<in>dom \<sigma>)"
by (erule EvalValue.induct, auto  )


lemma  ObjRef_EvalValue: " (v,\<sigma>,ObjRef l)\<in>EvalValue \<Longrightarrow> l\<in>dom \<sigma>"
by (drule ObjRef_EvalValue_pre,auto  )


lemma ObjRef_EvalExpr_pre: "(e,l, locs, \<sigma>,v)\<in>EvalExpr \<Longrightarrow> (\<forall> l'. v = ObjRef l' \<longrightarrow> l'\<in>dom \<sigma>)"
apply (erule MultiASP.EvalExpr.induct)
apply ( auto )
apply (drule ObjRef_EvalValue,blast)+
done

lemma  ObjRef_EvalExpr: " (e,l, locs, \<sigma>,ObjRef l')\<in>EvalExpr \<Longrightarrow> l'\<in>dom \<sigma>"
by (drule ObjRef_EvalExpr_pre,auto  )

lemma WF_ObjRef_ObjInStore: "
  Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
  Well_formed P (Cn Activities Futures) \<Longrightarrow>
       \<sigma> l = Some (Obj (obj_fields, C)) \<Longrightarrow>
  obj_fields xa = Some (ObjRef l') \<Longrightarrow>
     l'\<in>dom \<sigma>"
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec)
   apply (drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, simp)+
   apply clarsimp
   apply (drule_tac x=l in spec)+
   apply clarsimp
   apply (drule subsetD)
   apply auto
done

lemma WF_ActRef_store: "
  Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
  Well_formed P (Cn Activities Futures) \<Longrightarrow>
  \<sigma> l = Some (StoredVal (ActRef \<beta>)) \<Longrightarrow>
     \<beta>\<in>dom Activities"
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec, drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, simp)+
   apply (drule_tac x=\<beta> in bspec, simp add: Referenced_AOs_ActiveObject_def)
   apply auto
done

lemma WF_ActRef_ObjInStore: "
  Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
  Well_formed P (Cn Activities Futures) \<Longrightarrow>
  obj_fields xa = Some (ActRef \<beta>) \<Longrightarrow>
       \<sigma> l = Some (Obj (obj_fields, C)) \<Longrightarrow>
     \<beta>\<in>dom Activities"
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec, drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, simp)+
   apply (drule_tac x=\<beta> in bspec, simp add: Referenced_AOs_ActiveObject_def)
   apply (rule disjI1)
   apply (rule_tac x= "Obj (obj_fields, C)" in exI)
   apply auto
done

lemma WF_ActRef_locs: "
  Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
  Well_formed P (Cn Activities Futures) \<Longrightarrow>
  tasks Q = Some ((l, locs, Stl) # EcL) \<Longrightarrow>
  locs x =  Some (ActRef \<beta>) \<Longrightarrow>
     \<beta>\<in>dom Activities"
apply clarsimp
apply (drule_tac x=\<alpha> in spec, drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, simp)+
apply (drule_tac x=\<beta> in bspec, simp add: Referenced_AOs_ActiveObject_def)
 apply (rule disjI2, rule disjI2)
 apply clarsimp
 apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l, locs,Stl) # EcL)) {}" in exI)
 apply clarsimp
 apply rule 
(*3*)
  apply (rule_tac x="((l, locs,Stl) # EcL)" in exI)
  apply simp
  apply (case_tac Q,rename_tac ff mm vv, rule_tac x=ff in exI, rule_tac x=mm in exI, rule_tac x=vv in exI,blast)
 apply (auto  simp: Collector_EContext_def)
done

lemma WF_Serialize: 
"  Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
  Well_formed P (Cn Activities Futures) \<Longrightarrow>
serialize v \<sigma> \<sigma>' \<longrightarrow>
  (\<forall>l' x.    (\<sigma>' l'=Some x) \<longrightarrow>(Referenced_locations_Storable x\<subseteq>dom \<sigma>') ) "
 (*references inside the store are not dangling*)
apply (induct_tac v)
apply auto
sorry

lemma WF_Serialise: "
  Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
  Well_formed P (Cn Activities Futures) \<Longrightarrow>
   \<forall> i< length vl. serialize (vl!i) \<sigma> \<sigma>'' \<longrightarrow>
     Well_formed P (Cn (Activities(\<beta>\<mapsto>(AO l_\<beta> \<sigma>'' tasks' Rq'))) Futures)"
apply (induct_tac vl)
apply clarsimp
apply clarsimp
(*apply (clarsimp simp: serialize.def*)
sorry

section{* fetching lemmas *}
lemma find_emptyObjClass_pre[rule_format]: 
"distinct (map Name CL) \<longrightarrow>emptyObjClass \<in> set CL \<longrightarrow> 
  fetchClass (Prog IL CL vars stl) ''EmptyObjectClass'' = Some emptyObjClass"
apply (induct_tac CL, auto simp: emptyObjClass_def fetchClass_def)
apply ( drule_tac f=Name in imageI,simp )
done

lemma find_emptyObjClass: "Well_formed_Program (Prog IL CL vars stl) \<Longrightarrow>emptyObjClass \<in> set CL 
                            \<Longrightarrow> fetchClass (Prog IL CL vars stl) ''EmptyObjectClass'' = Some emptyObjClass"
(* states that fetchclass emptyclass succeeds for an initial configuration*)
by (rule find_emptyObjClass_pre, auto simp: Well_formed_Program_def Let_def)

lemma fetchClassI_pre: 
"distinct  (map Name CL)  \<Longrightarrow>C\<in>set CL\<Longrightarrow> Name C = CN
  \<Longrightarrow> fetchClass (Prog IL CL vars stl) CN = Some C "
by (induct CL, auto simp: fetchClass_def)

lemma fetchClassI[intro]: 
(* Intro rule for fetch class *)
"Well_formed_Program (Prog IL CL vars stl) \<Longrightarrow>C\<in>set CL\<Longrightarrow> Name C = CN
  \<Longrightarrow> fetchClass (Prog IL CL vars stl) CN = Some C "
by (rule fetchClassI_pre, auto simp: Well_formed_Program_def Let_def)

lemma fetchClass_CLI[intro]: 
(* Kind of Elim rule for fetch class *)
" fetchClass (Prog IL CL vars stl) CN = Some C 
  \<Longrightarrow> C\<in>set CL"
by (induct CL,auto simp: fetchClass_def split: split_if_asm)

lemma WF_program_fetchClass: 
"Well_formed_Program (Prog IL CL vars stl) \<Longrightarrow>Well_formed_activity (Prog IL CL vars stl) (AO l \<sigma> tasks Rq)
  \<Longrightarrow> \<sigma> l' = Some (Obj (obj_fields, CN))
  \<Longrightarrow> \<exists> C \<in>set CL. fetchClass (Prog IL CL vars stl) CN = Some C \<and> 
                   dom obj_fields = set (fields (Prog IL CL vars stl) CN) \<union> set (params (Prog IL CL vars stl) CN) "
(* in WF activities, for  all object in the store fetchclass succeeds and the object fields are the class parameters + the class fields*)
apply (clarsimp simp: Well_formed_activity_def Let_def)
apply (drule_tac x=l' in spec,drule_tac x=obj_fields in spec)
apply (auto)
done

section {* well-formed initial configuration&*}

lemma WF_init_vars_and_stl: "\<lbrakk>Referenced_locations_Stl sl={};Referenced_AOs_Stl sl={};
                  VarName_Collector_Stl sl\<subseteq>set vl; ClassName_Collector_Stl sl\<subseteq> DefinedClassNames prog;
                  fetchClass prog ''EmptyObjectClass'' = Some emptyObjClass
                  \<rbrakk> 
                \<Longrightarrow> Well_formed prog (BuildInitialConfigurationfromVarsStl vl sl)"
by (auto simp: Referenced_AOs_ActiveObject_def Referenced_futures_ActiveObject_def emptyObj_def BuildInitialConfigurationfromVarsStl_def Collector_EContext_def fields_def emptyObjClass_def params_def split: split_if_asm)

section{* bind-related lemmas*}
lemma Bind_referenced_locations: 
"Bind P l_this C m vla = Some (l,locs, s) \<Longrightarrow> locs x = Some (ObjRef l') \<Longrightarrow>(l'=l_this \<or>ObjRef l' \<in>set vla)"
apply (auto simp: Bind_def split: Program.split_asm option.split_asm split_if_asm)
apply (drule ran_map_of_zip,auto)
done

lemma Bind_same_location: "Bind (Prog IL CL vl sl) l_This C m vla = Some (l,locs, s) \<Longrightarrow> l=l_This"
by (clarsimp simp: Bind_def  fetchClass_def split: option.split_asm split_if_asm)


(* add class of instanciated objects in CL *)
lemma Bind_C_in_CL_distinct[rule_format]: 
" distinct (map Name CL) \<longrightarrow>  (Bind (Prog IL CL vl sl) l_This C m vla = Some (l,locs, s) 
\<longrightarrow>(\<exists>! C'\<in>set CL. Name C'=C \<and> 
    (\<exists> M'\<in>set (Methods C'). MName M'=m \<and>
            length (MParams M') = length vla \<and>
           ( locs =  ((map_of (zip (map snd (LocalVariables M')) (replicate (length (map snd (LocalVariables M'))) null)))
                    ++ (map_of (zip (map snd (MParams M')) vla))) \<and>
             s=Body M'))))"
apply (induct_tac CL)
apply (clarsimp simp: Bind_def Well_formed_Program_def fetchClass_def)
apply (clarsimp simp: Bind_def Well_formed_Program_def fetchClass_def Let_def  split: split_if_asm)
apply (case_tac "Name a = C")
(*2*)
 apply (clarsimp simp: Bind_def Well_formed_Program_def fetchClass_def Let_def  split: split_if_asm)
 apply (rule_tac a=a in ex1I)
  apply (clarsimp)
  apply (case_tac "fetchMethodInClass  a m", clarsimp simp: fetchMethodInClass_def, clarsimp simp: fetchMethodInClass_def)
  apply (case_tac "(List.find (\<lambda>method. MName method = m) (Methods a))")
   apply simp
  apply (clarsimp simp: List.find_Some_iff)
  apply (rule_tac x="Methods a ! i" in bexI,simp add: split_if split_if_asm)
(*4*)
   apply (case_tac "length (MParams (Methods a ! i)) = length vla")
    apply (clarsimp )
    apply (rule fun_cong,simp+)
(*2*)
 apply clarsimp
 apply ( drule_tac f=Name in imageI,simp )
apply blast
done

lemma Bind_C_in_CL_WF: 
" Well_formed_Program (Prog IL CL vl sl) \<Longrightarrow>  Bind (Prog IL CL vl sl) l_This C m vla = Some (l_This,locs, s) 
\<Longrightarrow> (\<exists>! C'\<in>set CL. Name C'=C \<and> 
    (\<exists> M'\<in>set (Methods C'). MName M'=m \<and> 
            length (MParams M') = length vla \<and>
           ( locs =  ((map_of (zip (map snd (LocalVariables M')) (replicate (length (map snd (LocalVariables M'))) null)))
                    ++ (map_of (zip (map snd (MParams M')) vla))) \<and>
             s=Body M')))"
by (rule Bind_C_in_CL_distinct, auto simp: Well_formed_Program_def Let_def)


lemma Bind_returned_code: 
"Bind (Prog IL CL vl sl) l_This C m vla = Some (l_This,locs, s) \<Longrightarrow> Well_formed_Program (Prog IL CL vl sl) 
\<Longrightarrow>  \<sigma> l_This = Some (Obj (obj_fields,C ))
\<Longrightarrow> (dom obj_fields = set (fields  (Prog IL CL vl sl) C) \<union> set (params  (Prog IL CL vl sl) C) ) \<Longrightarrow>
         VarName_Collector_Stl s\<subseteq> dom obj_fields \<union> dom locs \<and>
  Referenced_locations_Stl s={} \<and>  
  Referenced_AOs_Stl s={} \<and>  
  ClassName_Collector_Stl s\<subseteq>set (map Name CL)"
apply (frule Bind_C_in_CL_WF,simp)
apply clarify
apply (subgoal_tac "\<exists> fields . (Well_formed_method (map IName IL) fields CL M' \<and> set (map snd fields) = dom  obj_fields)")
 apply (auto)
(*5*)
    apply (simp add: Well_formed_method_def  split: Signature.splits)
    apply (drule subsetD,simp)
    apply force
   apply (simp add: Well_formed_method_def  split: Signature.splits)
  apply (simp add: Well_formed_method_def  split: Signature.splits)
 apply (simp add: Well_formed_method_def  split: Signature.splits)
 apply force
(*1*)
apply (frule_tac WF_class_in_program,auto simp: Well_formed_Class_def)
apply (rule_tac x="(ClassParameters C' @ StateVariables C')" in exI,simp)
apply (simp add: fields_def params_def)
 apply (subgoal_tac "fetchClass  (Prog IL CL vl sl) (Name C') =Some C'")
apply auto
done
lemma WF_init:  "Well_formed_Program P\<Longrightarrow> Well_formed P (InitialConfiguration P)"
(* initial configuration is well formed*)
proof(cases P)
case (Prog IL CL vars stl)
assume H1: "Well_formed_Program (P)"
assume H2: "P=(Prog IL CL vars stl)"
show "Well_formed P (InitialConfiguration (P))" using H1 H2
proof-
from H1 H2 have "Well_formed_Program (Prog IL CL vars stl)" by simp
then have "Referenced_locations_Stl stl={}\<and>Referenced_AOs_Stl stl={}\<and>
                  VarName_Collector_Stl stl\<subseteq>set (map snd vars) \<and> ClassName_Collector_Stl stl\<subseteq> DefinedClassNames (Prog IL CL vars stl)
                  \<and>                   fetchClass (Prog IL CL vars stl) ''EmptyObjectClass'' = Some emptyObjClass" 
              by (simp add: Well_formed_Program_def Let_def,rule find_emptyObjClass,auto )
then have "Well_formed (Prog IL CL vars stl) (BuildInitialConfigurationfromVarsStl (map snd vars) stl)" 
      by(clarify,drule_tac vl="map snd vars" in WF_init_vars_and_stl,auto simp: fetchClass_def)
then have "Well_formed (Prog IL CL vars stl) (InitialConfiguration (Prog IL CL vars stl))" by(simp add: InitialConfiguration_def Let_def)
then show  "Well_formed P (InitialConfiguration (P))" using H2 by simp 
qed
qed
(* OLD PROOF
apply (case_tac P)
apply (subgoal_tac "Referenced_locations_Stl list4={}\<and>Referenced_AOs_Stl list4={}\<and>
                  VarName_Collector_Stl list4\<subseteq>set (map snd list3)")
apply clarify
apply (drule_tac vl="map snd list3" in WF_init_vars_and_stl,simp,simp)
apply (simp  add: InitialConfiguration_def)
apply (simp add: Well_formed_Program_def Let_def)
done
 *)

section{* Well-formedness advanced lemmas *}
(*
REMOVED because too simple
lemma futures_Collector_Stl_tail_Stl: 
      "tasks R = Some ((l_this, locs, s;;Stl) # EcL) \<Longrightarrow>
       Referenced_futures_ActiveObject (AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs, Stl) # EcL)) Rq) \<subseteq> Referenced_futures_ActiveObject (AO l_\<alpha> \<sigma> (tasks) Rq)"
by (clarsimp simp: Referenced_futures_ActiveObject_def)
*)
lemma WF_Statement_reduction: (* states that if the first statement is removed, WF is preserved *)
      "AOs \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq)  \<Longrightarrow>
          tasks R= Some ((l_this,locs, s;;Stl)#EcL)  \<Longrightarrow>
         Well_formed P (Cn AOs Futs) \<Longrightarrow> Well_formed P (Cn (AOs(\<alpha>\<mapsto>AO l_\<alpha> \<sigma> (tasks(R\<mapsto>(l_this,locs,Stl)#EcL)) Rq)) Futs)"
apply clarsimp
apply (subgoal_tac "Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)") (* prerequisite well formed \<alpha> is useful! *)
prefer 2 
apply (drule_tac x=\<alpha> in spec,drule_tac x="AO l_\<alpha> \<sigma> tasks Rq" in spec, blast)

(*1*)
apply simp
apply (elim conjE)
apply (intro conjI allI impI)

(*10*)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)

(*9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*8 - same as 9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*7 almost the same*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,clarsimp,clarsimp)

(*6*)
   apply clarsimp
(*5*)
  apply clarsimp
  apply (case_tac j)
   apply (drule_tac locs=locs and s=s in   ClassName_Collector_Stl_tail_Stl,simp,simp)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp
   apply (drule subsetD,blast,blast)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
  apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
  apply simp
  apply (drule subsetD,blast,blast)

(*4*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp

(* 3 AO refs*)
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). \<beta> \<in> dom AOs)" in impE ,simp)
   apply (drule_tac l_\<alpha>=l_\<alpha> and \<sigma>=\<sigma> and Rq = Rq in AOs_Collector_Stl_tail_Stl)
   apply (drule subsetD,blast)
   apply (drule bspec,blast,blast)

(* 2 future refs*)
  apply (clarsimp simp: Referenced_futures_ActiveObject_def)

(*1 computed futures *)
 apply (drule_tac x=f in spec)+
 apply (clarsimp)
 apply rule
  apply clarsimp
  apply (rule_tac x=\<beta> in exI,simp)
  apply (case_tac "\<beta>=\<alpha>", simp)
   apply (drule_tac t=ao in sym,simp)
   apply blast
  apply blast
(*1*)
 apply clarsimp
 apply (case_tac "\<beta>=\<alpha>", simp)
  apply (rule_tac x=\<beta> in exI,simp)
  apply blast
 apply blast
done

lemma WF_Statement_reduction_then_case: 
  (* states that if some statements are removed because of ifthenelse reduction, WF is preserved - Case of the THEN branch *)
      "AOs \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq)  \<Longrightarrow>
          tasks R= Some ((l_this,locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl)#EcL)  \<Longrightarrow>
         Well_formed P (Cn AOs Futs) \<Longrightarrow> Well_formed P (Cn (AOs(\<alpha>\<mapsto>AO l_\<alpha> \<sigma> (tasks(R\<mapsto>(l_this,locs,s\<^sub>t @Stl)#EcL)) Rq)) Futs)"
(* the proof is very similar to the previous one: a few theorems used are different (those containing tail, and the instantiation of statements change *)
apply clarsimp
apply (subgoal_tac "Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)") (* prerequisite well formed \<alpha> is useful! *)
prefer 2 
apply (drule_tac x=\<alpha> in spec,drule_tac x="AO l_\<alpha> \<sigma> tasks Rq" in spec, blast)

(*1*)
apply simp
apply (elim conjE)
apply (intro conjI allI impI)

(*10*)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)

(*9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*8 - same as 9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*7 almost the same*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,clarsimp,clarsimp)

(*6*)
   apply clarsimp
(*5*)
  apply clarsimp
  apply (case_tac j)
   apply (drule_tac locs=locs and e=e and se=s\<^sub>e and st=s\<^sub>t in   ClassName_Collector_Stl_Then,simp,simp)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp
   apply (drule subsetD,blast,blast)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
  apply (drule_tac x="((l_this, locs,  (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
  apply simp
  apply (drule subsetD,blast,blast)

(*4*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp

(* 3 AO refs*)
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). \<beta> \<in> dom AOs)" in impE ,simp)
   apply (drule_tac l_\<alpha>=l_\<alpha> and \<sigma>=\<sigma> and Rq = Rq in AOs_Collector_Stl_Then)
   apply (drule subsetD,blast)
   apply (drule bspec,blast,blast)

(* 2 future refs*)
  apply (clarsimp simp: Referenced_futures_ActiveObject_def)

(*1 computed futures *)
 apply (drule_tac x=f in spec)+
 apply (clarsimp)
 apply rule
  apply clarsimp
  apply (rule_tac x=\<beta> in exI,simp)
  apply (case_tac "\<beta>=\<alpha>", simp)
   apply (drule_tac t=ao in sym,simp)
   apply blast
  apply blast
(*1*)
 apply clarsimp
 apply (case_tac "\<beta>=\<alpha>", simp)
  apply (rule_tac x=\<beta> in exI,simp)
  apply blast
 apply blast
done

lemma WF_Statement_reduction_else_case: 
  (* states that if some statements are removed because of ifthenelse reduction, WF is preserved - case of the ELSE branch*)
      "AOs \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq)  \<Longrightarrow>
          tasks R= Some ((l_this,locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl)#EcL)  \<Longrightarrow>
         Well_formed P (Cn AOs Futs) \<Longrightarrow> Well_formed P (Cn (AOs(\<alpha>\<mapsto>AO l_\<alpha> \<sigma> (tasks(R\<mapsto>(l_this,locs,s\<^sub>e @Stl)#EcL)) Rq)) Futs)"
(* the proof is AGAIN very similar to the previous one: beware the tricky points on Collector_Stl2 vs Collector_Stl *)
apply clarsimp
apply (subgoal_tac "Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)") (* prerequisite well formed \<alpha> is useful! *)
prefer 2 
apply (drule_tac x=\<alpha> in spec,drule_tac x="AO l_\<alpha> \<sigma> tasks Rq" in spec, blast)

(*1*)
apply simp
apply (elim conjE)
apply (intro conjI allI impI)

(*10*)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)

(*9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*8 - same as 9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp, blast,simp,blast)

(*7 almost the same*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,clarsimp ,clarsimp,clarsimp)

(*5*)
  apply clarsimp
  apply (case_tac j)
   apply (drule_tac locs=locs and e=e and se=s\<^sub>e and st=s\<^sub>t in   ClassName_Collector_Stl_Else,simp,simp)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp
   apply (drule subsetD,blast,blast)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
  apply (drule_tac x="((l_this, locs,  (IF e THEN s\<^sub>t ELSE s\<^sub>e);;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
  apply simp
  apply (drule subsetD,blast,blast)

(*4*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp

(* 3 AO refs*)
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). \<beta> \<in> dom AOs)" in impE ,simp)
   apply (drule_tac l_\<alpha>=l_\<alpha> and \<sigma>=\<sigma> and Rq = Rq in AOs_Collector_Stl_Else)
   apply (drule subsetD,blast)
   apply (drule bspec,blast,blast)

(* 2 future refs*)
  apply (clarsimp simp: Referenced_futures_ActiveObject_def)

(*1 computed futures *)
 apply (drule_tac x=f in spec)+
 apply (clarsimp)
 apply rule
  apply clarsimp
  apply (rule_tac x=\<beta> in exI,simp)
  apply (case_tac "\<beta>=\<alpha>", simp)
   apply (drule_tac t=ao in sym,simp)
   apply blast
  apply blast
(*1*)
 apply clarsimp
 apply (case_tac "\<beta>=\<alpha>", simp)
  apply (rule_tac x=\<beta> in exI,simp)
  apply blast
 apply blast
done

lemma WF_Statement_reduction_newalloc:
      "   Well_formed P (Cn AOs Futs) \<Longrightarrow>
          AOs \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq)  \<Longrightarrow>
          tasks R= Some ((l_this,locs, s;;Stl)#EcL)  \<Longrightarrow>
          l\<in>dom \<sigma>\<Longrightarrow>
    Well_formed P (Cn (AOs(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs, x =\<^sub>A Expr (Val (ObjRef l)) ;; Stl) # EcL)) Rq)) Futs)"
apply clarsimp
apply (subgoal_tac "Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)") (* prerequisite well formed \<alpha> is useful! *)
prefer 2 
apply (drule_tac x=\<alpha> in spec,drule_tac x="AO l_\<alpha> \<sigma> tasks Rq" in spec, blast)

(*1*)
apply simp
apply (elim conjE)
apply (intro conjI allI impI)

(*10*)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)

(*9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*8 - same as 9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*7 almost the same*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,clarsimp,clarsimp)

(*6*)
   apply clarsimp
(*5*)
  apply clarsimp
  apply (case_tac j)
   (* THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
   apply (subgoal_tac "xa \<in>ClassName_Collector_Stl (EC_Stl (((l_this, locs, Stl) # EcL) ! j))",rotate_tac -1)
(*7*)
    apply (drule_tac locs=locs and s=s in   ClassName_Collector_Stl_tail_Stl,simp,simp)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
    apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
    apply simp
    apply (drule subsetD,blast,blast)
   (*6 THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
   apply (clarsimp simp: ClassName_Collector_Stl_def)

  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
  apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
  apply simp
  apply (drule subsetD,blast,blast)

(*4*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp


(* 3 AO refs*)
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). \<beta> \<in> dom AOs)" in impE ,simp)
    (* THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
    apply (subgoal_tac "\<beta> \<in> Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs,  Stl) # EcL)) Rq)",rotate_tac -1)
   
     apply (drule_tac l_\<alpha>=l_\<alpha> and \<sigma>=\<sigma> and Rq = Rq in AOs_Collector_Stl_tail_Stl)
     apply (drule subsetD,blast)
     apply (drule bspec,blast,blast)
   (*3 THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
   apply( simp add: Referenced_AOs_ActiveObject_def)
   apply (elim disjE)
     apply blast
    apply blast
   apply (rule disjI2, rule disjI2)
   apply clarsimp
   apply (case_tac "R=(ab, ac, ba)",simp)
    apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l_this, locs,  Stl) # EcL) ) {}" in exI)
    apply simp
    apply rule
(*5*)
     apply (rule_tac x="(l_this, locs,  Stl) # EcL " in exI)
     apply simp
     apply blast
    apply (drule_tac t=ECl in sym,simp)
    apply (elim disjE)
     apply (clarsimp simp: Collector_EContext_def  )
    apply clarsimp
   apply clarsimp
(*3*)
   apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ECl) {}" in exI)
   apply clarsimp
   apply (intro conjI)
    apply (rule_tac x=" ECl " in exI)
    apply clarsimp
    apply (drule not_sym,blast)
   apply blast

(* 2 future refs*)
  apply (clarsimp simp: Referenced_futures_ActiveObject_def)

(*1 computed futures *)
 apply (drule_tac x=f in spec)+
 apply (clarsimp)
 apply rule
  apply clarsimp
  apply (rule_tac x=\<beta> in exI,simp)
  apply (case_tac "\<beta>=\<alpha>", simp)
   apply (drule_tac t=ao in sym,simp)
   apply blast
  apply blast
(*1*)
 apply clarsimp
 apply (case_tac "\<beta>=\<alpha>", simp)
  apply (rule_tac x=\<beta> in exI,simp)
  apply blast
 apply blast
done

lemma WF_Statement_reduction_newact:
      "   Well_formed P (Cn AOs Futs) \<Longrightarrow>
          AOs \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq)  \<Longrightarrow>
          tasks R= Some ((l_this,locs, s;;Stl)#EcL)  \<Longrightarrow>
          \<beta>\<in>dom AOs\<Longrightarrow>
    Well_formed P (Cn (AOs(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs, x =\<^sub>A Expr (Val (ActRef \<beta>)) ;; Stl) # EcL)) Rq)) Futs)"
apply clarsimp
apply (subgoal_tac "Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)") (* prerequisite well formed \<alpha> is useful! *)
prefer 2 
apply (drule_tac x=\<alpha> in spec,drule_tac x="AO l_\<alpha> \<sigma> tasks Rq" in spec, blast)

(*1*)
apply simp
apply (elim conjE)
apply (intro conjI allI impI)

(*10*)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)

(*9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*8 - same as 9*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1, drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,simp,blast,simp,blast)

(*7 almost the same*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply (case_tac j,clarsimp,clarsimp)

(*6*)
   apply clarsimp
(*5*)
  apply clarsimp
  apply (case_tac j)
   (* THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
   apply (subgoal_tac "xa \<in>ClassName_Collector_Stl (EC_Stl (((l_this, locs, Stl) # EcL) ! j))",rotate_tac -1)
(*7*)
    apply (drule_tac locs=locs and s=s in   ClassName_Collector_Stl_tail_Stl,simp,simp)
    apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
    apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
    apply simp
    apply (drule subsetD,blast,blast)
   (*6 THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
   apply (clarsimp simp: ClassName_Collector_Stl_def)
(*5*)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
  apply (drule_tac x="((l_this, locs, s;;Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec)+
  apply simp
  apply (drule subsetD,blast,blast)

(*4*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec)+
   apply (drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=j in spec)+
   apply simp


(* 3 AO refs*)
   apply clarsimp
   apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). \<beta> \<in> dom AOs)" in impE ,simp)
    (* THIS IS NEW TO DEAL WITH NEW KIND OF STATEMENT *) 
   apply (subgoal_tac "\<beta>'=\<beta>\<or>\<beta>' \<in> Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> (tasks(R \<mapsto> (l_this, locs,  Stl) # EcL)) Rq)")
    apply (elim disjE)
     apply blast
    apply (drule_tac l_\<alpha>=l_\<alpha> and \<sigma>=\<sigma> and Rq = Rq in AOs_Collector_Stl_tail_Stl)
    apply (drule subsetD,blast)
    apply (drule bspec,blast,blast)
   apply( simp add: Referenced_AOs_ActiveObject_def)
   apply (elim disjE)
(*5*)
     apply blast
    apply blast
   apply (elim exE conjE)
   apply (case_tac "R=(a, aa, b)",simp)
    apply (drule_tac t=ECl in sym,simp) 
    apply (case_tac "\<beta>'=\<beta>",simp,simp)
    apply (rule disjI2,rule disjI2)
    apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l_this, locs,  Stl) # EcL) ) {}" in exI)
    apply simp
    apply rule
(*5*)
     apply (rule_tac x="(l_this, locs,  Stl) # EcL " in exI)
     apply simp
     apply blast
    apply (clarsimp simp: Collector_EContext_def  ) 
 (*3*)
   apply (rule disjI2,rule disjI2,rule disjI2)
   apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ECl) {}" in exI)
   apply clarsimp
   apply (rule_tac x=" ECl " in exI)
   apply clarsimp
   apply (drule not_sym,blast)

(* 2 future refs*)
  apply (clarsimp simp: Referenced_futures_ActiveObject_def)

(*1 computed futures *)
 apply (drule_tac x=f in spec)+
 apply (clarsimp)
 apply rule
  apply clarsimp
  apply (rule_tac x=\<beta>' in exI,simp)
  apply (case_tac "\<beta>'=\<alpha>", simp)
   apply (drule_tac t=ao in sym,simp)
   apply blast
  apply blast
(*1*)
 apply clarsimp
 apply (case_tac "\<beta>'=\<alpha>", simp)
  apply (rule_tac x=\<beta>' in exI,simp)
  apply blast
 apply blast
done


lemma WF_activity_New_fetchClass:
"  Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
       tasks Q = Some ((l_this, locs, x =\<^sub>A new C(el) ;; Stl) # EcL) \<Longrightarrow> \<exists> Cl. fetchClass P C =Some Cl"
 apply simp
 apply (case_tac P,rename_tac IL CL vars stl)
 apply (case_tac Q,rename_tac ff mm vv,clarsimp)
 apply (drule_tac x=ff in spec, drule_tac x=mm in spec, drule_tac x=vv in spec)+
 apply (drule_tac x=0 in spec,simp add: ClassName_Collector_Stl_def fetchClass_def)+
 apply clarsimp
 apply (case_tac " List.find (\<lambda>class. Name class = Name xa) CL")
  apply (force simp: List.find_None_iff)
 apply force
done

declare [[simp_depth_limit = 5]]
(* next lemma is useful to simplify the well formed proof in all the cases where reduction is isolated in a single activity *)
(*TODO : in general it should be used in combination with the 2 previous lemmas on instruction reduction *)
lemma WF_only_local_update: "AOs \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq)  \<Longrightarrow>
          tasks R= Some ((l_this,locs, Stl)#EcL)  \<Longrightarrow>
          dom locs\<subseteq>dom locs' \<Longrightarrow>
          dom \<sigma>\<subseteq>dom \<sigma>' \<Longrightarrow>
           (\<forall>l x. \<sigma>' l\<noteq>\<sigma> l \<longrightarrow>  (\<sigma>' l=Some x) \<longrightarrow>Referenced_locations_Storable x\<subseteq>dom \<sigma>' ) \<Longrightarrow>
           (\<forall>l x. \<sigma>' l\<noteq>\<sigma> l \<longrightarrow>  (\<sigma>' l=Some x) \<longrightarrow>Collector_Storable x EmptyCollector Future_Collector\<subseteq>dom Futs ) \<Longrightarrow>
          (\<forall>l . \<sigma>' l\<noteq>\<sigma> l \<longrightarrow>  (case  \<sigma> l of
             None \<Rightarrow>   \<forall> obj_fields CN . (\<sigma>' l=Some  (Obj (obj_fields, CN)))  \<longrightarrow> ((\<exists>C. fetchClass P CN = Some C) \<and>
                                              dom obj_fields = set (fields P CN) \<union> set (params P CN) ) |
             Some storable \<Rightarrow> (case storable of
                      Obj (obj_fields, CN) \<Rightarrow> (\<exists> obj_fields'. ((\<sigma>' l) =  Some  (Obj (obj_fields', CN))\<and> dom obj_fields' = dom obj_fields)) |
                      FutRef f \<Rightarrow> \<forall> obj_fields CN . (\<sigma>' l=Some  (Obj (obj_fields, CN)))  \<longrightarrow> ((\<exists>C. fetchClass P CN = Some C) \<and>
                                              dom obj_fields = set (fields P CN) \<union> set (params P CN) ) |
                     StoredVal v \<Rightarrow> False (*a stored value is immutable *)
             )))
             \<Longrightarrow>
           (\<forall>  l x. locs' x\<noteq>locs x \<longrightarrow> locs' x=Some (ObjRef l)  \<longrightarrow>l\<in>dom \<sigma>') \<Longrightarrow>   
           (\<forall>  \<beta> x. locs' x\<noteq>locs x \<longrightarrow> locs' x=Some (ActRef \<beta>)  \<longrightarrow>\<beta>\<in>dom AOs) \<Longrightarrow>   
            (\<forall>l x. \<sigma>' l\<noteq>\<sigma> l \<longrightarrow>  (\<sigma>' l=Some x) \<longrightarrow> Collector_Storable x Referenced_AOs_Value EmptyCollector\<subseteq>dom AOs ) \<Longrightarrow>
         Well_formed P (Cn AOs Futs) \<Longrightarrow> Well_formed P (Cn (AOs(\<alpha>\<mapsto>AO l_\<alpha> \<sigma>' (tasks(R\<mapsto>(l_this,locs',Stl)#EcL)) Rq)) Futs)"
apply clarsimp
apply (subgoal_tac "Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)")
prefer 2 
apply (drule_tac x=\<alpha> in spec,drule_tac x="AO l_\<alpha> \<sigma> tasks Rq" in spec, blast)
apply simp
apply (elim conjE)
apply (intro conjI allI impI)
(*18*)
  apply (erule subsetD,assumption)
 apply (case_tac  "\<sigma>' l' = \<sigma> l'")
  apply simp
  apply (drule_tac x=l' in spec,drule_tac x=x in spec, blast)
 apply (drule_tac x=l' in spec, blast)

(*16*)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)
 apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)
apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec,drule_tac x=l'' in spec, blast)

(*13*)
   apply (case_tac j,elim conjE exE,simp)
    apply (case_tac  "locs' x = locs x",simp)
     apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x="((l_this, locs, Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=l'' in spec,rotate_tac -1,drule_tac x="0" in spec, simp)
     apply (erule subsetD)
     apply force
    apply (drule_tac x=l'' in spec,drule_tac x=x in spec, blast)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x="((l_this, locs, Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec, simp)
   apply (erule subsetD)
   apply force

(*12*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x="((l_this, locs, Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec, simp)
   apply (erule subsetD)
   apply (elim conjE)
   apply (case_tac j, simp, simp)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec, erule impE,blast)
  apply blast

(*10*)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=l'' in spec,rotate_tac -1,drule_tac x=j in spec, erule impE,blast)
   apply blast

  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x="((l_this, locs, Stl) # EcL)" in spec,rotate_tac -1,drule_tac x=j in spec,  erule impE,case_tac j, blast,force)
  apply (case_tac "\<sigma>' (EC_location (((l_this, locs', Stl) # EcL) ! j)) = \<sigma> (EC_location (((l_this, locs', Stl) # EcL) ! j))")
   apply clarsimp
   apply (rule_tac x=fieldsa in exI,simp)
   apply rule
    apply (rule_tac x=CN in exI)
    apply (case_tac j, simp,simp)

(*10*)
   apply (case_tac j, clarsimp)
    apply (drule subsetD,blast,blast)
   apply simp
  apply (subgoal_tac "let l = (EC_location (((l_this, locs', Stl) # EcL) ! j)) in l\<in>dom \<sigma>")
   apply (subgoal_tac "let l = (EC_location (((l_this, locs', Stl) # EcL) ! j)) in 
          (\<forall>obj_fields CN. \<sigma> l = Some (Obj (obj_fields, CN)) \<longrightarrow> (\<exists>obj_fields'. \<sigma>' l = Some (Obj (obj_fields', CN)) \<and> dom obj_fields' = dom obj_fields))")
    apply (simp add: Let_def)
    apply (drule_tac x="(EC_location (((l_this, locs', Stl) # EcL) ! j))" in spec)
    back
    apply simp
    apply (elim exE conjE)
    apply (drule_tac x=fieldsa in spec, drule_tac x=CN in spec,erule impE, case_tac j, simp,simp)
    apply (elim exE conjE)
    apply (drule_tac x=obj_fields' in exI,simp)
    apply (case_tac j, clarsimp)
     apply (drule subsetD,blast,blast)
    apply simp

(*10*)
   apply (simp add: Let_def split: option.split_asm Storable.split_asm)
   apply (drule_tac x="(EC_location (((l_this, locs', Stl) # EcL) ! j))" in spec, clarsimp)
   apply (drule_tac x="Obj (obj_fields, CNa)" in spec,simp)
  apply (simp add: Let_def,case_tac j, simp,blast)
  apply simp
  apply blast

(*8*)
   apply (elim conjE)
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x=EcLa in spec,rotate_tac -1,drule_tac x=j in spec,  erule impE,case_tac j, blast,force)
   apply (case_tac "\<sigma>' (EC_location (EcLa ! j)) = \<sigma> (EC_location (EcLa ! j))")
    apply clarsimp
   apply (subgoal_tac "let l = (EC_location (EcLa ! j)) in l\<in>dom \<sigma>")
    apply (subgoal_tac "let l = (EC_location (EcLa ! j)) in 
          (\<forall>obj_fields CN. \<sigma> l = Some (Obj (obj_fields, CN)) \<longrightarrow> (\<exists>obj_fields'. \<sigma>' l = Some (Obj (obj_fields', CN)) \<and> dom obj_fields' = dom obj_fields))")
     apply (drule_tac x="(EC_location (EcLa ! j))" in spec)
     back
     apply (simp add: Let_def)
     apply (elim exE conjE)
     apply (drule_tac x=fieldsa in spec, drule_tac x=CN in spec, erule impE, case_tac j, simp,simp)
     apply (elim exE conjE)
     apply (drule_tac x=obj_fields' in exI,simp)

(*9*)
   apply (simp add: Let_def  split: option.split_asm Storable.split_asm)
   apply (drule_tac x="(EC_location (EcLa ! j))" in spec, clarsimp)
   apply (drule spec,elim conjE,(erule impE,simp)+)
   apply (drule_tac x=fieldsa in  spec, drule spec,erule impE,blast)
   apply simp

  apply (simp add: Let_def,blast)

(*7*)
   apply (case_tac  "\<sigma>' l' = \<sigma> l'")
    apply simp
   apply (case_tac "l'\<in>dom \<sigma>")
    apply clarify
    apply (case_tac ya)
      apply (case_tac x1)
      apply ((drule_tac x=l' in spec)+,simp split: split_if_asm)+
   apply (case_tac "\<sigma> l'",simp,blast)

(*6*)
   apply (case_tac  "\<sigma>' l' = \<sigma> l'")
    apply simp
    apply (case_tac "l'\<in>dom \<sigma>")
     apply clarify
     apply (case_tac ya)
      apply (case_tac x1)
      apply ((drule_tac x=l' in spec)+,simp split: split_if_asm)+
   apply (case_tac "\<sigma> l'",simp,blast)

(*5*)
   apply clarsimp
   apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x="(l_this, locs,  Stl) # EcL" in spec,rotate_tac -1,drule_tac x=j in spec,  erule impE,case_tac j, blast,force)
   back
   apply (case_tac j, simp)
    apply (drule subsetD,blast,blast)
  apply clarsimp
   apply (drule subsetD,blast,blast)
  apply (drule_tac x=f in spec,drule_tac x=m in spec,drule_tac x=vl in spec, drule_tac x="EcLa" in spec,rotate_tac -1,drule_tac x=j in spec,  erule impE,case_tac j, blast,force,blast)

(*3*) (* AO references *)
   apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>\<beta>\<in>Referenced_AOs_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). \<beta> \<in> dom AOs)" in impE ,simp)
   apply rule
   apply ( simp add: Let_def Referenced_AOs_ActiveObject_def)
   apply (elim disjE)

(*5*)
   apply clarsimp
   apply (case_tac "\<sigma>' a = \<sigma> a")
    apply (drule_tac x=\<beta> in bspec,simp,rule,rule,blast) (* bspec condition  *)
    apply blast
   apply (drule_tac x=a in spec,blast)
  apply (drule_tac x=\<beta> in bspec,simp,blast) (* bspec condition  and conclude*)

(*3*)
(* the difficult case is when locs change*)
   apply (clarsimp split: split_if_asm)
   apply (elim disjE)
    apply simp
    apply (drule_tac t=ECl in sym,simp)
    apply (elim disjE)
    apply (simp add: Collector_EContext_def)
    apply (elim disjE)
     apply clarsimp
     apply (case_tac "locs' ad = locs ad")
      apply simp

(*7*)
   apply (drule_tac x=\<beta> in bspec,simp)
    apply simp
    apply ( rule disjI2,rule disjI2)
    apply (rule_tac x= "foldr op \<union>
                       (map (\<lambda>x. (\<Union>x\<in>{b. \<exists>a. EC_locs x a = Some b}.
                                      case x of null \<Rightarrow> {} | ASPInt x \<Rightarrow> EmptyCollector x | ASPBool x \<Rightarrow> EmptyCollector x | ActRef a \<Rightarrow> {a} | ObjRef x \<Rightarrow> EmptyCollector x) \<union>
                                  Collector_Stl (EC_Stl x) Referenced_AOs_Value)
                         ((l_this, locs, Stl) # EcL) )
                       {}" in exI)
    apply clarsimp
    apply (rule)
     apply (rule_tac x="((l_this, locs, Stl) # EcL) " in  exI)
     apply simp
     apply blast
    apply blast
   apply blast

(*6*)
   apply (drule_tac x=\<beta> in spec,drule_tac x=ad in spec,elim impE,simp)
    back
    apply simp
    apply (case_tac x,simp+)
   apply blast

  apply (drule_tac x=\<beta> in bspec,simp)
   apply simp
   apply ( rule disjI2,rule disjI2)
   apply (rule_tac x= "foldr op \<union>
                       (map (\<lambda>x. (\<Union>x\<in>{b. \<exists>a. EC_locs x a = Some b}.
                                      case x of null \<Rightarrow> {} | ASPInt x \<Rightarrow> EmptyCollector x | ASPBool x \<Rightarrow> EmptyCollector x | ActRef a \<Rightarrow> {a} | ObjRef x \<Rightarrow> EmptyCollector x) \<union>
                                  Collector_Stl (EC_Stl x) Referenced_AOs_Value)
                         ((l_this, locs, Stl) # EcL) )
                       {}" in exI)
   apply clarsimp
   apply (rule_tac x="((l_this, locs, Stl) # EcL) " in  exI)
   apply simp
   apply blast
  apply blast

(*4*)
   apply (drule_tac x=\<beta> in bspec,simp)
   apply ( rule disjI2,rule disjI2)
   apply (rule_tac x= "foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l_this, locs, Stl) # EcL)) {}" in exI)
   apply clarsimp
   apply (intro conjI)
    apply (rule_tac x="((l_this, locs, Stl) # EcL) " in  exI)
    apply simp
    apply blast
   apply blast
  apply blast

(*3*)
   apply (drule_tac x=\<beta> in bspec,simp)
   apply ( rule disjI2,rule disjI2)
   apply (rule_tac x= "foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) (ECl)) {}" in exI)
   apply clarsimp
   apply (intro conjI)
    apply (rule_tac x=ECl in  exI)
    apply simp
    apply blast
   apply blast
  apply blast

(*2*) (* now future references *)
  apply (drule_tac x=\<alpha> in spec,drule_tac x= "(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule_tac Q=" (\<forall>f'\<in>Referenced_futures_ActiveObject (AO l_\<alpha> \<sigma> tasks Rq). f' \<in> dom Futs)" in impE ,simp)
  apply (clarsimp simp: Let_def Referenced_futures_ActiveObject_def)
  apply (elim disjE)

(*3*)
  apply clarsimp
  apply (case_tac "\<sigma>' a = \<sigma> a")
   apply (drule_tac x=f' in bspec,simp,rule,rule,blast) (* bspec condition  *)
   apply blast
  apply (drule_tac x=a in spec,blast)
 apply (drule_tac x=f' in bspec,simp,blast) (* bspec condition  and conclude*)

(* last condition: computed futures*)
 apply clarsimp
 apply rule
  apply clarsimp
  apply (rule_tac x=\<beta> in exI, clarsimp)
 apply clarsimp
 apply (rule_tac x=\<beta> in exI, clarsimp)
 apply (drule_tac x=m in spec, drule_tac x=vl in spec,blast)
done

section{* finally the well-formedness thm*}
lemma Well_formed_reduction_SERVE:
 " Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks (Rq @ R # Rq')) \<Longrightarrow>
       R = (f, m, vl) \<Longrightarrow>
       Ready R tasks Rq \<Longrightarrow>
       \<sigma> l_\<alpha> = Some (Obj (obj, C)) \<Longrightarrow>
       Bind P l_\<alpha> C m vl = Some EC \<Longrightarrow>
       Well_formed_Program P \<Longrightarrow>
       Well_formed P (Cn Activities Futures) \<Longrightarrow> 
       Well_formed P (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(R \<mapsto> [EC])) (Rq @ Rq'))) Futures)"
apply (subgoal_tac "Well_formed_activity  P (AO l_\<alpha> \<sigma> tasks (Rq @ R # Rq'))")
 apply clarsimp
apply (intro conjI allI impI)
(*12*)
   apply clarsimp
   apply (drule_tac x=f in spec)+
   apply (drule_tac x=m in spec)+
   apply (drule_tac x=vl in spec)+
   apply (drule_tac x=l'' in spec)+
   apply clarsimp
   apply (rotate_tac -1,erule impE)
    apply (rule_tac x="length Rq" in exI)
    apply force
   apply simp
   apply (drule_tac x=i in spec)
   apply force

(*11*)
   apply clarify
   apply (drule_tac x=fa in spec)+
   apply (drule_tac x=ma in spec)+
   apply (drule_tac x=vla in spec)+
   apply (drule_tac x=l'' in spec)+
   apply clarsimp
   apply (rotate_tac -1,erule impE)
    apply (case_tac "j<length Rq")
     apply (rule_tac x=j in exI)
     apply (force simp: nth_append)
(*12*)
   apply (rule_tac x="j+1" in exI)
   apply (force simp: nth_append)
  apply simp
  apply (drule_tac x=i in spec)
  apply force

(*10*)
   apply clarsimp
   apply (case_tac P,case_tac EC,simp)
   apply (frule_tac Bind_same_location)
   apply (drule Bind_referenced_locations,simp)
   apply (elim disjE)
    apply force
   apply (drule_tac x=f in spec)+
   apply (drule_tac x=m in spec)+
   apply (drule_tac x=vl in spec)+
   apply (drule_tac x=l'' in spec)+
   apply clarsimp
   apply (rotate_tac -1,erule impE)
    apply (rule_tac x="length Rq" in exI)
    apply force
(*10*)
   apply (clarsimp simp: List.set_conv_nth)
   apply (drule_tac x=i in spec)+
   apply force

(*9*)
  apply (case_tac P,rename_tac IL CL vars stl, case_tac EC,rename_tac l locsB StlB,simp)
  apply (frule Bind_same_location,simp)
  apply (frule_tac \<sigma>=\<sigma> and obj_fields=obj and C=C in Bind_returned_code,simp+)

(*8*)
  apply (case_tac P,rename_tac IL CL vars stl, case_tac EC,rename_tac l locsB StlB,simp)
  apply (frule Bind_same_location,simp)
  apply (frule_tac \<sigma>=\<sigma> and obj_fields=obj and C=C in Bind_returned_code,simp+)
  apply blast

(*7*)
  apply clarify
  apply (drule_tac x=fa in spec)+
  apply (drule_tac x=ma in spec)+
  apply (drule_tac x=vla in spec)+
  apply (drule_tac x=EcL in spec)+
  apply (drule_tac x=j in spec)+
  apply clarsimp

(*6*)
  apply (case_tac P,rename_tac IL CL vars stl, case_tac EC,rename_tac l locsB StlB,simp)
  apply (frule Bind_same_location,simp)
  apply (frule_tac \<sigma>=\<sigma> and obj_fields=obj and C=C in Bind_returned_code,simp+)
(*5*)
  apply (drule_tac x=fa in spec)+
  apply (drule_tac x=ma in spec)+
  apply (drule_tac x=vla in spec)+
  apply (drule_tac x=EcL in spec)+
  apply (drule_tac x=j in spec)+
  apply clarsimp
(*4*)
  apply clarsimp
  apply (drule_tac x=\<alpha> in spec)+
  apply clarsimp
  apply (drule_tac x=\<beta> in bspec,simp add: Referenced_AOs_ActiveObject_def)
  apply (elim disjE)
   apply simp
   apply (rule disjI2, rule disjI1)
   apply (rule foldr_Un_larger,assumption)
   apply (elim exE conjE)
   apply (case_tac "a = f \<and> aa = m \<and> b = vl")
(*6*)
  apply (elim conjE,simp)
  apply (rule disjI2, rule disjI1)
  apply (rule foldr_Un_other)
  apply clarsimp
  apply (case_tac P,rename_tac IL CL vars stl, case_tac EC,rename_tac l locsB StlB,simp)
  apply ( simp add: Collector_Request_def Collector_EContext_def)
  apply (frule Bind_same_location,simp)
  apply (frule_tac \<sigma>=\<sigma> and obj_fields=obj and C=C in Bind_returned_code,simp+)
  apply (clarsimp simp: Bind_def split: option.split_asm)
  apply (subgoal_tac "length ac = length vl",clarsimp)
   apply (elim disjE)
    apply (subgoal_tac "Referenced_AOs_Value x \<in> Referenced_AOs_Value ` set vl")
     apply (rule_tac x=x in bexI)
      apply force
     apply (rule AuxiliaryFunctions.ran_map_of_zip,simp,simp)

(*8*)
   apply (rule_tac f=Referenced_AOs_Value in imageI)
   apply (erule ran_map_of_zip)
   apply simp
  apply (clarsimp split: split_if_asm)
 apply (clarsimp split: split_if_asm)

(*5*)
   apply simp
   apply (rule disjI2, rule disjI2)
   apply (rule_tac x=x in exI,simp)
   apply (rule_tac x=ECl in exI,simp)
   apply blast
  apply blast

(*3*)
   apply (clarsimp simp: Referenced_futures_ActiveObject_def)
   apply (drule_tac x=\<alpha> in spec)+
   apply simp
   apply (drule_tac x=f' in bspec,simp)
    apply (rule disjE)
      apply blast
     apply blast
   apply (rule disjI2,rule foldr_Un_larger,assumption) 
   apply blast

(*2*)
  apply rule
   apply clarsimp
   apply (rule_tac x=\<beta> in exI)
   apply (case_tac "\<beta>=\<alpha>")
    apply (simp,drule sym,simp)
     apply (case_tac "fa = f ")
      apply blast
     apply clarsimp
    apply simp
(*2*)
  apply clarsimp
  apply (rule_tac x=\<beta> in exI)
  apply (case_tac "\<beta>=\<alpha>",simp)
   apply (case_tac "fa = f ")
    apply blast
   apply simp
  apply simp

(*1*)
apply (clarsimp simp: Well_formed_def )
apply (drule_tac x=\<alpha> in spec)+
apply clarsimp
done

lemma Well_formed_reduction_ASSIGNLOCAL:
" Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
       tasks Q = Some ((l, locs, x =\<^sub>A Expr e ;; Stl) # EcL) \<Longrightarrow>
       x \<in> dom locs \<Longrightarrow>
       (e, l, locs, \<sigma>, v) \<in> EvalExpr \<Longrightarrow>
       Well_formed_Program P \<Longrightarrow>
       Well_formed P (Cn Activities Futures) \<Longrightarrow> Well_formed P (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l, locs(x \<mapsto> v), Stl) # EcL)) Rq)) Futures)"
apply (subgoal_tac "(tasks(Q \<mapsto> (l, locs, Stl) # EcL)) Q = Some ((l, locs, Stl) # EcL)")
apply (rotate_tac -1, frule_tac P=P and \<sigma>'=\<sigma> and locs=locs and locs'="locs(x \<mapsto> v)" and Futs=Futures in WF_only_local_update,simp)
(*11*)
    apply force
   apply simp+
(*6*)
   apply clarsimp
   apply (drule ObjRef_EvalExpr)
   apply force
(*5*)
  apply clarsimp
  apply (drule ActRef_EvalExpr)
  apply simp
  apply (elim disjE)
     apply clarsimp
     apply (drule_tac x=\<alpha> in spec, drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, simp)+
     apply (drule_tac x=\<beta> in bspec, simp add: Referenced_AOs_ActiveObject_def)
      apply (rule disjI2, rule disjI2)
      apply clarsimp
      apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l, locs,x =\<^sub>A Expr (Val (ActRef \<beta>)) ;; Stl) # EcL)) {}" in exI)
      apply clarsimp
      apply rule 
       apply (rule_tac x="((l, locs,x =\<^sub>A Expr (Val (ActRef \<beta>)) ;; Stl) # EcL)" in exI)
       apply simp
       apply (case_tac Q,rename_tac ff mm vv, rule_tac x=ff in exI, rule_tac x=mm in exI, rule_tac x=vv in exI,blast)
      apply (rule disjI1)
      apply (simp add: Collector_EContext_def)
     apply blast
(*7*)
   apply clarsimp
   apply (drule WF_ActRef_store,simp+)
   apply blast

(*6*)
   apply clarsimp
   apply (drule WF_ActRef_locs,simp+)
   apply blast

(*5*)
   apply clarsimp
   apply (drule_tac l=la and \<beta>=\<beta> and obj_fields = obj_fields in WF_ActRef_ObjInStore,simp+)
   apply blast

(*4*)
  apply clarsimp
(*3*)
  apply clarsimp
(*2*)
  apply (subgoal_tac "(Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l, locs(x \<mapsto> v), x =\<^sub>A Expr e ;; Stl) # EcL)) Rq)) \<alpha> = Some (AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l, locs(x \<mapsto> v), x =\<^sub>A Expr e ;; Stl) # EcL)) Rq)")
  apply (drule_tac AOs = "(Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l, locs(x \<mapsto> v),  x =\<^sub>A Expr e ;; Stl) # EcL)) Rq))" and  R=Q and Futs=Futures and P=P  
                             in WF_Statement_reduction,simp+)
done

lemma Well_formed_reduction_ASSIGNFIELD:
" Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
       tasks Q = Some ((l, locs, x =\<^sub>A Expr e ;; Stl) # EcL) \<Longrightarrow>
       x \<notin> dom locs \<Longrightarrow>
       \<sigma> l_this = Some (Obj obj) \<Longrightarrow>
       x \<in> dom (GetObject obj) \<Longrightarrow>
       (e, l_this, locs, \<sigma>, v) \<in> EvalExpr \<Longrightarrow>
       \<sigma>' = \<sigma>(l_this \<mapsto> Obj (obj.[x]:=v)) \<Longrightarrow>
       Well_formed_Program P \<Longrightarrow>
       Well_formed P (Cn Activities Futures) \<Longrightarrow> Well_formed P (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma>' (tasks(Q \<mapsto> (l, locs, Stl) # EcL)) Rq)) Futures)"
apply (subgoal_tac "(tasks(Q \<mapsto> (l, locs, Stl) # EcL)) Q = Some ((l, locs, Stl) # EcL)")
apply (rotate_tac -1, frule_tac P=P and \<sigma>'=\<sigma>' and locs=locs and locs'=locs and Futs=Futures in WF_only_local_update,simp)
(*11*)
    apply force
   apply force
  
(*9*)
   apply clarsimp
   apply (case_tac xaa,simp+)
   apply (case_tac obj, rename_tac fields CN)
   apply (case_tac "a=x")
    apply simp+
    apply (drule ObjRef_EvalExpr)
    apply force
   apply (drule_tac obj_fields = fields and C = CN and l'= x5 and xa=a in   WF_ObjRef_ObjInStore,simp+)
   apply blast
(*8*)   
   apply simp+
   apply force
  apply simp+
(*4*)
   apply clarsimp
   apply (case_tac "a=x")
    apply simp+
    apply (case_tac xaa,simp+)
     apply (drule ActRef_EvalExpr)
     apply (rename_tac act)
      apply (elim disjE)
(*9*)
     apply clarsimp
     apply (drule_tac x=\<alpha> in spec, drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, simp)+
     apply (drule_tac x=act in bspec, simp add: Referenced_AOs_ActiveObject_def)
      apply (rule disjI2, rule disjI2)
      apply clarsimp
      apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l, locs,x =\<^sub>A Expr (Val (ActRef act)) ;; Stl) # EcL)) {}" in exI)
      apply clarsimp
      apply rule 
       apply (rule_tac x="((l, locs,x =\<^sub>A Expr (Val (ActRef act)) ;; Stl) # EcL)" in exI)
       apply simp
       apply (case_tac Q,rename_tac  ff mm vvl)
       apply (rule_tac x=ff in exI, rule_tac x=mm in exI, rule_tac x=vvl in exI,blast)
(*10*)
      apply (rule disjI1)
      apply (simp add: Collector_EContext_def)
     apply blast
    apply clarsimp
    apply (drule_tac  l= la and \<beta>=act in   WF_ActRef_store,simp+)
    apply force
(*7*)
    apply clarsimp
    apply (drule_tac   \<beta>=act in   WF_ActRef_locs,simp+)
    apply blast
   apply clarsimp
   apply (drule_tac obj_fields = obj_fields and C = C and l= la and xa=xb in   WF_ActRef_ObjInStore,simp+)
   apply blast
  apply force
(*4*)
   apply clarsimp
   apply (case_tac obj, rename_tac fields CN)
   apply (drule_tac obj_fields = fields and C = CN  and \<beta>=xa and xa = a in   WF_ActRef_ObjInStore,simp+)
     apply (case_tac xaa,simp+)
   apply blast
  apply force
(*2*)
 apply (subgoal_tac "((Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma>' (tasks(Q \<mapsto> (l, locs, x =\<^sub>A Expr e ;; Stl) # EcL)) Rq))) \<alpha> = Some (AO l_\<alpha> \<sigma>' (tasks(Q \<mapsto> (l, locs, x =\<^sub>A Expr e ;; Stl) # EcL)) Rq)")
  apply (rotate_tac -1, drule_tac P=P  and s=" x =\<^sub>A Expr e" in WF_Statement_reduction,simp+,blast,blast)
  apply (simp only: Fun.fun_upd_upd)
  apply simp+
done

lemma Well_formed_reduction_NEW:
"Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
       tasks Q = Some ((l_this, locs, (x =\<^sub>A new C(el)) ;; Stl) # EcL) \<Longrightarrow>
       MultiASP.fields P C = field_list \<Longrightarrow>
       params P C = param_list \<Longrightarrow>
       l \<notin> dom \<sigma> \<Longrightarrow>
       length param_list = length el \<Longrightarrow>
       length param_list = length value_list \<Longrightarrow>
       \<forall>i<length value_list. (el ! i, l_this, locs, \<sigma>, value_list ! i) \<in> EvalExpr \<Longrightarrow>
       \<sigma>' = \<sigma>(l \<mapsto> Obj (map_of (zip field_list (replicate (length field_list) null)) ++ map_of (zip param_list value_list), C)) \<Longrightarrow>
       Well_formed_Program P \<Longrightarrow>
       Well_formed P (Cn Activities Futures) \<Longrightarrow>
       Well_formed P (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma>' (tasks(Q \<mapsto> (l_this, locs, (x =\<^sub>A Expr (Val (ObjRef l))) ;; Stl) # EcL)) Rq)) Futures)"
apply (rotate_tac -1, frule_tac P=P and \<sigma>'=\<sigma>' and locs=locs and locs'=locs and Futs=Futures in WF_only_local_update,simp)
(*10*)
   apply simp
  apply force
  apply  (intro allI impI)

(*8*)
  apply (case_tac "la=l")
   apply simp
   apply (drule_tac t=xa in sym)
   apply clarsimp
   apply (case_tac xb,simp+)
   apply (erule disjE)
(*10*)
    apply clarsimp
    apply (subgoal_tac "length (params P C) = length value_list",rotate_tac -1)
     apply (frule_tac  AuxiliaryFunctions.ran_map_of_zip,simp)
     apply (simp add: set_conv_nth)
     apply clarsimp
     apply (drule_tac x=i in spec,simp)
     apply (drule_tac s="ObjRef x5" in sym,simp)
     apply (drule ObjRef_EvalExpr)
     apply blast
    apply simp
   apply (clarsimp split: split_if_asm)
  apply simp

(* 7 now for futures *)
   apply  (intro allI impI)
   apply (case_tac "la=l")
    apply clarsimp
   apply force

(*6*)
   apply  (intro allI impI)
   apply (case_tac "\<sigma> la",simp+)
    apply (case_tac P)
    apply (subgoal_tac " Well_formed_activity P (AO l_\<alpha> \<sigma> tasks Rq)") 
     apply (drule WF_activity_New_fetchClass,simp+)
     apply (clarsimp simp: params_def fields_def fetchClass_def)
     apply force
    apply (elim conjE)
    apply (drule_tac x=\<alpha> in spec)+
    apply (drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule impE,assumption,assumption)
(*6*)
   apply simp+
   apply (case_tac a)
     apply (case_tac x1)
     apply clarsimp
    apply clarsimp
   apply clarsimp
   apply (case_tac "la=l",simp+)

(*3*)
  apply clarsimp
  apply (erule disjE) 
   apply (drule AuxiliaryFunctions.ran_map_of_zip,simp)
   apply (clarsimp simp: set_conv_nth split: Value.split_asm)
   apply (drule_tac x=i in spec,simp)
   apply (drule ActRef_EvalExpr,simp)
   apply (erule disjE)
   apply (rename_tac act i)
(*5*)
   apply (drule_tac x=\<alpha> in spec)+
   apply (drule_tac x="(AO l_\<alpha> \<sigma> tasks Rq)" in spec, erule impE,assumption)
   apply clarsimp
   apply (drule_tac x=act  in bspec)
    apply (simp add: Referenced_AOs_ActiveObject_def)
    apply (rule disjI2,rule disjI2)
    apply (case_tac Q,rename_tac ff mm vv,clarsimp)
    apply (rule_tac x="foldr op \<union> (map (\<lambda>x. Collector_EContext x Referenced_AOs_Value) ((l_this, locs, x =\<^sub>A new C(el) ;; Stl) # EcL)) {}" in exI)
    apply clarsimp
    apply (intro conjI)
     apply (rule_tac x=" ((l_this, locs, x =\<^sub>A new C(el) ;; Stl) # EcL)" in exI)
     apply clarsimp
     apply (rule_tac x=ff in exI, rule_tac x=mm in exI, rule_tac x=vv in exI)
     apply clarsimp
(*6*)
    apply (rule disjI1)
    apply (clarsimp simp: Collector_EContext_def  )
    apply (rule_tac x="el!i" in bexI)
     apply force
    apply (clarsimp simp: set_conv_nth)
    apply (rule_tac x=i in exI,simp)
   apply blast
(*4*)
  apply (rename_tac act i)
  apply (elim disjE)
(*6*)
    apply clarsimp
    apply (drule_tac  l= la and \<beta>=act in   WF_ActRef_store,simp+)
    apply force
   apply clarsimp
   apply (drule_tac   \<beta>=act in   WF_ActRef_locs,simp+)
   apply blast
  apply clarsimp
(*4*)
  apply (drule_tac  obj_fields = obj_fields and l= la and \<beta>=act in   WF_ActRef_ObjInStore,simp+)
  apply blast
 apply (clarsimp split: split_if_asm)
apply simp

(*1*)
 apply(subgoal_tac "Well_formed P (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma>' (tasks) Rq)) Futures)",rotate_tac -1)
  apply (drule_tac   \<alpha>=\<alpha> and l=l  in WF_Statement_reduction_newalloc,simp,simp,simp,simp)
 apply (drule_tac t=tasks in Map.map_upd_triv)
 apply simp
done

lemma map_upd_upd_diff:
" a\<noteq>b \<Longrightarrow> m(a\<mapsto>x,b\<mapsto>y) = m(b\<mapsto>y,a\<mapsto>x)"
apply force
done
lemma Well_formed_reduction_NEWACTIVE:
"      Activities \<alpha> = Some (AO l_\<alpha> \<sigma> tasks Rq) \<Longrightarrow>
       tasks Q = Some ((l_this, locs, x =\<^sub>A newActive C(el) ;; Stl) # EcL) \<Longrightarrow>
       MultiASP.fields P C = field_list \<Longrightarrow>
       params P C = param_list \<Longrightarrow>
       \<gamma> \<notin> dom Activities \<Longrightarrow>
       length param_list = length el \<Longrightarrow>
       length param_list = length value_list \<Longrightarrow>
       \<forall>i<length value_list. (el ! i, l_this, locs, \<sigma>, value_list ! i) \<in> EvalExpr \<and> serialize (value_list ! i) \<sigma> \<sigma>\<^sub>0 \<Longrightarrow>
       l \<notin> dom \<sigma>\<^sub>0 \<Longrightarrow>
       \<sigma>' = \<sigma>\<^sub>0(l \<mapsto> Obj (map_of (zip field_list (replicate (length field_list) null)) ++ map_of (zip param_list value_list), C)) \<Longrightarrow>
       Well_formed_Program P \<Longrightarrow>
       Well_formed P (Cn Activities Futures) \<Longrightarrow>
          Well_formed P
            (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l_this, locs, x =\<^sub>A Expr (Val (ActRef \<gamma>)) ;; Stl) # EcL)) Rq, 
                            \<gamma> \<mapsto> AO l \<sigma>' Map.empty [])) 
                 Futures)"
apply (subgoal_tac "\<gamma> \<noteq> \<alpha>")
apply (subgoal_tac "Well_formed P 
            (Cn (Activities(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l_this, locs, x =\<^sub>A newActive C(el) ;; Stl) # EcL)) Rq, 
                            \<gamma> \<mapsto> AO l \<sigma>' Map.empty [])) 
                 Futures)")
apply (subgoal_tac "Well_formed P 
            (Cn (Activities(\<gamma> \<mapsto> AO l \<sigma>' Map.empty [])) 
                 Futures)")
apply (subgoal_tac " Well_formed P
     (Cn (Activities(\<gamma> \<mapsto> AO l \<sigma>' Map.empty [])(\<alpha> \<mapsto> AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l_this, locs, x =\<^sub>A Expr (Val (ActRef \<gamma>)) ;; Stl) # EcL)) Rq)) Futures)
")
apply (drule_tac m=Activities and y="AO l_\<alpha> \<sigma> (tasks(Q \<mapsto> (l_this, locs, x =\<^sub>A Expr (Val (ActRef \<gamma>)) ;; Stl) # EcL)) Rq"
                 and x= "AO l \<sigma>' Map.empty []" in map_upd_upd_diff,rotate_tac -1,simp)
apply (rule WF_Statement_reduction_newact,simp,simp,simp,simp)
apply simp
apply (intro allI conjI)
(*
ADD LEMMA ON DEEP COPY AND WF
apply blast
apply simp
apply 

apply (rotate_tac -1, drule_tac Stl="x =\<^sub>A Expr (Val (ActRef \<gamma>)) ;; Stl" and P=P and \<sigma>'=\<sigma> and locs=locs and locs'=locs and Futs=Futures in WF_only_local_update,simp)
apply blast+

apply (thin_tac ?P)
apply (rule WF_Statement_reduction_newact)
apply blast+


theorem Well_formed_reduction[rule_format]: " (P\<turnstile>Cn AOs Futs \<leadsto>Cn AOs' Futs' ) \<longrightarrow> Well_formed_Program P \<longrightarrow>(Well_formed P (Cn AOs Futs)\<longrightarrow>Well_formed P (Cn AOs' Futs'))"
apply (rule impI, erule  reduction.induct)
(*13*)
apply (intro impI)
apply (erule Well_formed_reduction_SERVE)
apply (simp,simp,simp,simp,simp,simp) (* simp all hypotheses of lemma Well_formed_reduction_SERVE*)
(*12*)
apply (intro impI)
apply (erule Well_formed_reduction_ASSIGNLOCAL)
apply (simp,simp,simp,simp,simp) (* simp all hypotheses of lemma Well_formed_reduction_ASSIGNLOCAL*)
(*11*)
apply (intro impI)
apply (erule Well_formed_reduction_ASSIGNFIELD)
apply (simp,simp,simp,simp,simp,simp,force,simp,simp) (* simp/force all hypotheses of lemma Well_formed_reduction_ASSIGNFIELD*)
(*10*)
apply (intro impI)
apply (erule Well_formed_reduction_NEW)
apply (simp,simp,simp,simp,simp,simp,simp,force,simp,simp) (* simp/force all hypotheses of lemma Well_formed_reduction_NEW*)
(*9*)

(* useless
lemma drop_Suc_Cons[rule_format]:  "\<forall> n .  drop n list' = a # list \<longrightarrow>drop (Suc n) list' = list"
apply (induct_tac list')
apply ( auto simp: List.drop_Suc )
apply (case_tac n,simp)
apply (case_tac lista)
apply auto
done
*)

