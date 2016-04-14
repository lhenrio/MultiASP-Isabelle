(*  Title:      MultiASP.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       Multi-active object formalisation
                For the moment methods and parameter bindings are done statically, 
                  without inheritance but with interfaces
                  this could be improved
*)
theory Serialization imports StoreDefinition Main AuxiliaryFunctions begin
axiomatization where 
finite_map: "finite (dom (\<sigma>::Store))"
and
finite_obj: "V=Obj(f,C) \<Longrightarrow>finite (dom f)"

abbreviation isnotObjRef where "isnotObjRef V \<equiv>\<forall>l'. V\<noteq>ObjRef l'"



lemma finite_ran_obj:
"V=Obj(f,C) \<Longrightarrow>finite (ran f)"
apply (drule finite_obj)
apply (auto simp: ran_and_dom)
done

 definition Referenced_locations_Value:: "Value \<Rightarrow> Location set"
where  "Referenced_locations_Value v \<equiv> (case v of ObjRef l \<Rightarrow>{l} | _ \<Rightarrow> {})"

definition Referenced_locations_Location:: "Store \<Rightarrow>Location \<Rightarrow> Location set"
where  "Referenced_locations_Location \<sigma> l \<equiv> 
case \<sigma> l of 
None \<Rightarrow>{} |
Some (Obj obj) \<Rightarrow> \<Union>(Referenced_locations_Value`ran(fst(obj))) |
Some (StoredVal (ObjRef l')) \<Rightarrow> {l'} |
_\<Rightarrow>{}
"

definition Well_Formed_Store where
"Well_Formed_Store \<sigma> \<equiv> \<forall> l\<in> dom \<sigma>. Referenced_locations_Location \<sigma> l\<subseteq>dom \<sigma>"


subsection {* serialization and location renaming *}

inductive serialize :: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
(*serialize v \<sigma> \<sigma>' is true if all the references pointed recursively by v are in sigma' 
(v refers originally to location in sigma and sigma'should be a subset of sigma) 
NB: one should expect that the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ran(fst(obj)). \<exists>\<sigma>''. (serialize v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
     \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |

    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (StoredVal v) \<and>  (serialize v \<sigma> \<sigma>')\<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |

     "serialize (null) \<sigma> \<sigma>' " 
     (*|
         " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (FutRef f)  \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
     "(serialize (ActRef f) \<sigma> \<sigma>')" |
     "serialize (ASPInt n) \<sigma> \<sigma>'" | 
     "serialize (ASPBool b) \<sigma> \<sigma>'"
*)
lemma serialize_composable_inductive_proof:     "serialize v \<sigma> \<sigma>' \<Longrightarrow> (\<forall> v \<sigma> \<sigma>'. serialize v \<sigma> \<sigma>' \<longrightarrow> Q v \<sigma> \<sigma>') \<Longrightarrow>
    (\<And>\<sigma>' l \<sigma> obj.
        \<sigma>' l = \<sigma> l \<and> \<sigma> l = Some (Obj obj) \<and> (\<forall>v\<in>ran (fst obj). \<exists>\<sigma>''. (serialize v \<sigma> \<sigma>'' \<and> P v \<sigma> \<sigma>''\<and> Q v \<sigma> \<sigma>'') \<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>') \<Longrightarrow> P (ObjRef l) \<sigma> \<sigma>') \<Longrightarrow>
    (\<And>\<sigma>' l \<sigma> v. \<sigma>' l = \<sigma> l \<and> \<sigma> l = Some (StoredVal v) \<and> serialize v \<sigma> \<sigma>' \<and> P v \<sigma> \<sigma>'\<and> Q v \<sigma> \<sigma>' \<Longrightarrow> P (ObjRef l) \<sigma> \<sigma>') \<Longrightarrow>
    (\<And>\<sigma> \<sigma>'. P null \<sigma> \<sigma>'\<and> Q null \<sigma> \<sigma>') \<Longrightarrow> P  v \<sigma> \<sigma>'"
apply (erule serialize.induct,auto)
 apply (subgoal_tac " (\<forall>v\<in>ran a. \<exists>\<sigma>''. serialize v \<sigma> \<sigma>'' \<and> P v \<sigma> \<sigma>'' \<and> Q v \<sigma> \<sigma>'' \<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>' )")
  apply auto
 apply (drule_tac x=v  in bspec,auto)
apply (subgoal_tac " serialize v \<sigma> \<sigma>' \<and> P v \<sigma> \<sigma>' \<and> Q v \<sigma> \<sigma>'")
 apply auto
done


lemma Referenced_locations_Value_obj[simp]: "Referenced_locations_Value (ObjRef l) = {l}"
apply (auto simp: Referenced_locations_Value_def)
done

section {* serialization filter*}

function (sequential) serialization_filter :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialization_filter v \<sigma> L  is the set of locations that are recursively referenced by the value v
  locations in L are EXCLUDED from the set (to prevent looping definition) *)
  where
    "
    (serialization_filter l \<sigma> L) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      None \<Rightarrow>{} |
      Some (Obj obj) \<Rightarrow> {l}\<union>\<Union>( (\<lambda>x.(serialization_filter x \<sigma> (L\<union>{l}))) 
                `( (\<Union>(Referenced_locations_Value`ran(fst(obj)))))) |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (serialization_filter l' \<sigma> (L\<union>{l}))|
      _ \<Rightarrow> {l}))" 
by auto
termination 
apply (relation "measure (\<lambda>(l,\<sigma>,L). card (dom \<sigma> - L))") 
  apply auto
 apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
  apply (subgoal_tac "finite ((dom \<sigma>-L))")
(*4*)
   apply (drule_tac x=l in Finite_Set.card.remove)+
    apply (insert finite_map)
    apply auto
(*1*)
apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
 apply (subgoal_tac "finite ((dom \<sigma>-L))")
  apply (drule_tac x=l in Finite_Set.card.remove)+
   apply (insert finite_map)
   apply auto
done

abbreviation serialize2:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
(* a second definition of serialisation based on the serialisation filter: 
sigma' is exactly the store captured by the algorithm (the smallest necessary sub-store *)
where
"serialize2 l \<sigma> \<equiv>  \<sigma> |` serialization_filter l \<sigma> {}" 

lemma SFI1SG1: "(\<And>a b. l \<notin> L \<Longrightarrow>
               \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
               \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a). P (serialization_filter x \<sigma> (L \<union> {l})) x \<sigma> (L \<union> {l}) \<Longrightarrow>
               P ({l} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (L \<union> {l})) ` \<Union>(Referenced_locations_Value ` ran a))) l \<sigma> L) \<Longrightarrow>
       ((\<sigma> l=None \<or>l\<in>L)\<longrightarrow>P {} l \<sigma> L) \<Longrightarrow>
        (\<And>x2 prod x.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = Obj prod \<Longrightarrow>
           x \<in> \<Union>(Referenced_locations_Value ` ran (fst prod)) \<Longrightarrow> P (serialization_filter x \<sigma> (L \<union> {l})) x \<sigma> (L \<union> {l})) \<Longrightarrow>
        \<sigma> l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (serialization_filter l \<sigma> L) l \<sigma> L"
(* intermediary lemma *)
apply (case_tac prod)
apply clarsimp
apply blast
done

lemma  SFI1SG2:"(\<And>x2 v nat.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = StoredVal v \<Longrightarrow> v = ObjRef nat \<Longrightarrow> P (serialization_filter nat \<sigma> (L \<union> {l})) nat \<sigma> (L \<union> {l})) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (serialization_filter l' \<sigma> (L \<union> {l})) l' \<sigma> (L \<union> {l}) \<Longrightarrow> P ({l} \<union> serialization_filter l' \<sigma> (L \<union> {l})) l \<sigma> L) \<Longrightarrow>
  \<sigma> l = Some a \<Longrightarrow>  ((\<sigma> l=None \<or>l\<in>L)\<longrightarrow>P {} l \<sigma> L)\<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (serialization_filter l \<sigma> L) l \<sigma> L
  "
(* intermediary lemma *)
apply clarsimp
done

(* INDUCTION PRINCIPLE on Filtering 
1 - is with an additional variable for the induciton set (often useful)
2 - is the most natural one
*)
lemma serialization_filter_induct_1: "   
(\<And>l \<sigma> L. \<sigma> l=None\<or>l\<in>L \<longrightarrow> P {} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L V. l\<notin>L \<Longrightarrow>  \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L f C.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (f,C)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran f)). 
                          P (serialization_filter x \<sigma> (L\<union>{l})) x \<sigma> (L\<union>{l})) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. serialization_filter x \<sigma> (L \<union> {l}))` \<Union>(Referenced_locations_Value`ran(f))))) l \<sigma> L)  \<Longrightarrow>
(\<And>l \<sigma> L l'.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (serialization_filter l' \<sigma> (L\<union>{l})) l' \<sigma>  (L\<union>{l}))\<Longrightarrow>
           (P ({l}\<union>(serialization_filter l' \<sigma> (L\<union>{l}))) l \<sigma> L))         \<Longrightarrow>   
   P (serialization_filter l' \<sigma>' L') l' \<sigma>' L'"
apply (rule serialization_filter.induct)
apply (rotate_tac 1,drule_tac x=l in meta_spec)+
apply (rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+
apply (rotate_tac -1,drule_tac x=L in meta_spec)+
apply (case_tac "\<sigma> l")
(*2*)
 apply force
apply (case_tac a)
 apply (erule SFI1SG1,simp,simp,simp,simp)
apply (rename_tac val)
apply (case_tac val)
 apply force
apply (erule SFI1SG2,simp+)
done

lemma serialization_filter_induct_2: "   (\<And>l \<sigma> L. P {} ) \<Longrightarrow>
(\<And>l \<sigma> L V.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} ) \<Longrightarrow> 
(\<And>l \<sigma> L f C.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (f,C)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran f)). P (serialization_filter x \<sigma> (L\<union>{l})) ) \<Longrightarrow>
           P ({l}\<union>(\<Union> ((\<lambda> x. serialization_filter x \<sigma> (L \<union> {l}))` \<Union>(Referenced_locations_Value`ran(f))))) )   \<Longrightarrow> 
(\<And>l \<sigma> L l'.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (serialization_filter l' \<sigma> (L\<union>{l})) )\<Longrightarrow>
           (P ({l}\<union>(serialization_filter l' \<sigma> (L\<union>{l}))))) 
  \<Longrightarrow>    
   P (serialization_filter l \<sigma> L) "
apply (insert  serialization_filter_induct_1 [of "(\<lambda> S l \<sigma> L. (P S))" ])
apply auto
done

lemma serialization_filter_subset: "serialization_filter l \<sigma> L \<subseteq> dom \<sigma>"
apply (rule_tac P= "\<lambda> S l \<sigma> L. (S \<subseteq> dom \<sigma>)" in   serialization_filter_induct_1)
   apply auto
apply (drule_tac x=xb in bspec)
 apply auto
apply (drule_tac x=xa in bspec)
 apply (auto split: option.splits )
done

lemma serialize_subset: "dom (serialize2 l \<sigma>) \<subseteq> dom \<sigma>"
apply (insert serialization_filter_subset, auto)
done

lemma serialize_value: "(serialize2 l \<sigma>) l' = Some x \<Longrightarrow> \<sigma> l' = Some x"
apply (subgoal_tac "l'\<in>(serialization_filter l \<sigma> {})")
 apply (drule_tac m=\<sigma> in Map.restrict_in)
 apply force
apply (rule Map_restrict_Some,blast)
done



lemma Referenced_locations_LocationI_Obj[intro]:
"\<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
            a x = Some (ObjRef l') \<Longrightarrow> l'\<in> Referenced_locations_Location \<sigma> l"
apply (auto simp: Referenced_locations_Location_def Referenced_locations_Value_def)
apply (rule_tac x="ObjRef l'" in bexI)
 apply auto
apply (rule ranI,blast)
done


lemma Referenced_locations_LocationI_ref[intro]:
"\<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>  l'\<in> Referenced_locations_Location \<sigma> l"
apply (auto simp: Referenced_locations_Location_def Referenced_locations_Value_def)
done
lemma Well_Formed_StoreD_obj[intro]: 
"\<sigma> la = Some (Obj (f, C)) \<Longrightarrow>  Well_Formed_Store \<sigma> \<Longrightarrow> f x = Some (ObjRef l) \<Longrightarrow>   l \<in> dom \<sigma>"
apply (auto simp: Well_Formed_Store_def )
done

lemma Well_Formed_StoreD_ref[intro]: 
"\<sigma> la = Some (StoredVal (ObjRef l)) \<Longrightarrow>  Well_Formed_Store \<sigma> \<Longrightarrow> l \<in> dom \<sigma>"
apply (auto simp: Well_Formed_Store_def )
done

lemma serialization_filter_WF_1step_obj[rule_format]: 
  "l\<in>serialization_filter l'' \<sigma> L \<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some (ObjRef l') 
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  l'\<in>L\<or>l'\<in>serialization_filter l'' \<sigma> L "
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. l\<in>S \<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some ( ObjRef l')   \<longrightarrow>Well_Formed_Store \<sigma>
\<longrightarrow>   l'\<in>L\<or>l'\<in>S" in   serialization_filter_induct_1)
(*4*)
   apply force
  apply clarsimp
 apply (case_tac "l'=la")
  apply simp
 apply (case_tac "l=la")
  apply clarsimp
  apply (drule_tac x="( ObjRef l')" in bspec)
   apply (rule ranI)
   apply blast
  apply (drule_tac x=l' in bspec,simp,simp)
  apply (auto split: split_if_asm )
(*2*)
 apply (drule_tac x=l' in bspec,simp)
  apply (rule_tac x="( ObjRef l')" in bexI)
  apply simp
  apply (rule ranI,simp)
 apply (clarsimp split: option.splits Storable.splits simp: Well_Formed_Store_def)
  apply (drule_tac x=l in bspec,blast)
  apply (drule Referenced_locations_LocationI_Obj, simp+)
  apply force
(*2*)
 apply (simp split: Value.splits)
apply (drule_tac x=l' in bspec,simp)
 apply (rule_tac x="( ObjRef l')" in bexI)
  apply simp
 apply (rule ranI,simp)
apply auto
done

lemma serialization_filter_WF_1step_ref[rule_format]: 
  "l\<in>serialization_filter l'' \<sigma> L \<longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) 
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  l'\<in>L\<or>l'\<in>serialization_filter l'' \<sigma> L "
apply (rule_tac P= "\<lambda> S l'' \<sigma> L. l\<in>S \<longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) 
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  l'\<in>L\<or>l'\<in>S" in   serialization_filter_induct_1)
   apply force
  apply clarsimp
(*2*)
 apply (case_tac "l'=la")
  apply simp
 apply (case_tac "l=la")
  apply clarsimp
 apply clarsimp
 apply (auto split: split_if_asm )
apply (clarsimp split: option.splits Storable.splits simp: Well_Formed_Store_def)
(*2*)
 apply (drule_tac x=l in bspec,blast)
 apply (drule Referenced_locations_LocationI_ref)
 apply force
apply (simp split: Value.splits)
done

lemma Serialization_excluded_set_subset[rule_format]: "\<forall> L . L\<subseteq>L' \<longrightarrow> serialization_filter l \<sigma> L' \<subseteq> serialization_filter l \<sigma> L"
apply (rule_tac P= "\<lambda> S l \<sigma> L'. (\<forall>L. L\<subseteq>L' \<longrightarrow> S \<subseteq> serialization_filter l \<sigma> L)" in   serialization_filter_induct_1)
(*4*)
   apply clarsimp
  apply (clarsimp split: Value.splits)
  apply blast
 apply clarsimp
 apply rule
  apply blast
 apply clarsimp
 apply (drule_tac x=xb in bspec,blast) 
 apply (rotate_tac -1,drule_tac x=xa in bspec,blast) 
 apply clarsimp
 apply (drule_tac x="insert l La" in spec)
 apply clarsimp 
 apply (erule impE, blast)
 apply (drule_tac x=xa in bspec,blast) 
 apply (case_tac "xa\<in>La")
(*3*)
  apply clarsimp
 apply clarsimp
 apply blast
apply (intro impI allI)
apply (drule_tac x="La \<union> {l}" in spec)
apply auto
done

lemma Serialization_WF: "Well_Formed_Store \<sigma> \<Longrightarrow> Well_Formed_Store (serialize2 l \<sigma>)"
apply (unfold Well_Formed_Store_def)
apply (intro ballI)
apply (fold Well_Formed_Store_def)
apply (subgoal_tac " la \<in> dom \<sigma>")
 apply (case_tac "\<sigma> la")
  apply blast
 apply rule
 apply (unfold Referenced_locations_Location_def)
(*2*)
 apply (case_tac  "serialize2 l \<sigma> la")
  apply blast
 apply (drule serialize_value)
 apply (subgoal_tac "a=aa")
  apply clarify
  apply (case_tac aa,rename_tac obj')
  apply (case_tac obj')
   apply (frule serialize_value)
   apply  clarsimp
   apply (subgoal_tac "serialize2 l \<sigma> la = Some (Obj (ab, ba))")
(*5*)
    apply clarsimp
    apply (simp add: ran_def Referenced_locations_Value_def,clarify)
    apply (subgoal_tac "la\<in>serialization_filter l \<sigma> {}")
     apply (drule serialization_filter_WF_1step_obj,simp, force split: Value.splits)
       apply (simp split: Value.splits,simp)
     apply (simp split: Value.splits)
     apply (drule Well_Formed_StoreD_obj,simp,simp)
     apply blast
    apply (rule Map_restrict_Some,force)
   apply simp
  apply (frule serialize_value)
  apply simp
(*3*)
  apply (subgoal_tac "la\<in>serialization_filter l \<sigma> {}")
   apply (drule serialization_filter_WF_1step_ref,simp, simp split: Value.splits,simp,simp)
   apply (simp split: Value.splits)
   apply (drule Well_Formed_StoreD_ref,simp)
   apply blast
(*3*)
  apply (rule Map_restrict_Some,force)
 apply force
apply (insert serialize_subset[of \<sigma> l])
apply blast
done

section{*renaming*}
primrec subst_Value :: " Value \<Rightarrow> (Location\<Rightarrow>Location) \<Rightarrow> Value"
where
  "subst_Value (ObjRef l) \<psi> = ObjRef (\<psi>(l))" |
  "subst_Value (null) \<psi> = null" 

definition check_subst :: "Store \<Rightarrow> (Location\<Rightarrow>Location) \<Rightarrow> Store \<Rightarrow> bool"
where
  "check_subst  \<sigma> \<psi> \<sigma>' \<equiv>
    ( inj \<psi> \<and> dom \<sigma>' =  \<psi> ` (dom(\<sigma>)) 
    \<and> (\<forall> f C l . (\<sigma>(l) = Some (Obj (f,C))  
      \<longrightarrow> (\<exists> f' C'. (\<sigma>'(\<psi>(l)) = Some (Obj (f',C')) \<and> dom f= dom f'
      \<and>(\<forall> x  v. (f x = Some v) \<longrightarrow> (f' x=Some (subst_Value v \<psi>))))))
    \<and>   (\<forall> v l . (\<sigma>(l) = Some (StoredVal v) \<longrightarrow> 
      \<sigma>'(\<psi>(l)) = Some (StoredVal (subst_Value v \<psi>))))))"



lemma "check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> (\<forall> l \<in> dom \<sigma>. \<exists> l' \<in> dom \<sigma>'. l'= \<psi>(l))"
apply (auto simp: check_subst_def)
done

lemma subst_dom: "check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> \<psi> ` (dom \<sigma>) \<subseteq> dom \<sigma>'"
apply (auto simp: check_subst_def)
done

lemma subst_ref_dom: " \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> (l' \<in> dom \<sigma>) \<Longrightarrow> \<psi>(l') \<in> dom \<sigma>'"
apply (auto simp: check_subst_def)
done

lemma subst_follow_ref: 
"check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> 
        \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>  (l' \<in> dom \<sigma>) \<Longrightarrow>
        \<sigma>' l'' = Some (StoredVal (ObjRef l''')) \<Longrightarrow>  (l''' \<in> dom \<sigma>') \<Longrightarrow> 
        l'' = \<psi>(l) 
        \<Longrightarrow> l''' = \<psi>(l')"
apply (auto simp: check_subst_def)
done


lemma subst_referenced_locations: " check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> 
       ( (\<psi> `(Referenced_locations_Location \<sigma> l)) = (Referenced_locations_Location \<sigma>' (\<psi> l)) )" 
apply(auto simp: check_subst_def)
 apply (case_tac "\<sigma> l")
  apply(auto simp: Referenced_locations_Location_def Referenced_locations_Value_def )
 apply (case_tac a)
  apply clarsimp
(*3*)
  apply (drule_tac x=aa in spec)
  apply (drule_tac x=b in spec)
  apply (drule_tac x=l in spec)
  apply (clarsimp simp: ran_def, rename_tac Val x f C)
  apply ( drule_tac x=x in spec)
  apply (rotate_tac -1, drule_tac x=Val in spec)
  apply clarsimp
  apply (rule_tac x="(subst_Value Val \<psi>)" in exI)
  apply (rule conjI)
(*4*)
   apply (rule_tac x=x in exI)
   apply (auto simp: Referenced_locations_Value_def split: Value.splits)
(*1*)
apply (case_tac "\<sigma>' (\<psi> l)")
 apply(auto simp: Referenced_locations_Location_def Referenced_locations_Value_def )
apply (case_tac "\<sigma> l")
 apply clarsimp
 apply (subgoal_tac "\<psi> l\<in>dom \<sigma>'")
  apply (clarsimp simp: inj_on_def)
  apply (drule_tac x=l in spec)
  apply (drule_tac x=xa in spec)
  apply clarsimp
 apply force

(*1*)
apply (case_tac a)
 apply (case_tac aa)
  apply clarsimp
  apply (drule_tac x=ac in spec)
  apply (drule_tac x=ba in spec)
  apply (drule_tac x=l in spec)
  apply (clarsimp simp: ran_def)
  apply ( drule_tac x=a in spec)
  apply clarsimp
  apply (subgoal_tac "\<exists> v . ac a = Some v")
   apply clarsimp
   apply (clarsimp simp: Referenced_locations_Value_def)
(*4*)
   apply (case_tac "subst_Value v \<psi>")
    apply force
   apply (case_tac v,clarsimp)
   apply (clarsimp )
   apply (rule,simp+)
   apply (rename_tac oref)
   apply (rule_tac x="ObjRef oref" in exI,force)
  apply blast
 apply force
(*1*)
apply (case_tac aa)
 apply force
apply (rename_tac val)
apply (case_tac val,auto)
done


lemma check_subst_rev: "check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow>  l\<in>dom \<sigma>' \<Longrightarrow> \<exists>l'\<in>dom \<sigma>. l=\<psi> l'"
apply (auto simp:  check_subst_def)
done

lemma " Well_Formed_Store \<sigma> \<Longrightarrow> check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> Well_Formed_Store \<sigma>'"
apply (auto simp:  Well_Formed_Store_def)
apply (frule_tac check_subst_rev,force,clarsimp)
apply (frule_tac l ="l'" in subst_referenced_locations)
apply (subgoal_tac "\<exists> y \<in>Referenced_locations_Location \<sigma> l' . x=\<psi> y")
 apply clarsimp
 apply (frule_tac x=yb in bspec,clarsimp)
  apply blast
(*2*)
 apply (auto simp: check_subst_def)
apply (subgoal_tac "yb\<in>dom \<sigma>")
 apply blast
apply blast
done

lemma serialize_substore: "serialize (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow>\<sigma>'\<subseteq>\<^sub>m  \<sigma>''\<longrightarrow> Well_Formed_Store \<sigma>'' \<longrightarrow> serialize (ObjRef l) \<sigma> \<sigma>''"
apply (erule serialize.induct)
(*3*)
  apply auto
(* 3 obj case *)
  apply (rule serialize.intros,auto)
   apply (force simp: map_le_def)
  apply (drule_tac x=v in bspec)
   apply assumption
  apply clarsimp
  apply (rule_tac x=\<sigma>''' in exI)
 apply (force simp: map_le_def)
(* 2 storedval*)
 apply (rule serialize.intros(2))
 apply (force simp: map_le_def)
(*1 null *)
apply (rule serialize.intros(3))
done

lemma serialization_filter_dom_subset_pre: 
          "serialize v \<sigma> \<sigma>' \<Longrightarrow> \<forall> L. case v of ObjRef l \<Rightarrow> serialization_filter l \<sigma> L \<subseteq> dom \<sigma>' | null \<Rightarrow> {}\<subseteq> dom \<sigma>' "
apply (erule serialize.induct)
  apply auto
 apply (split option.splits)
  apply auto
(*2*)
 apply (drule_tac x=xb in bspec)
  apply auto
 apply (case_tac xb)
  apply (auto simp: Referenced_locations_Value_def)
 apply (drule_tac x="insert l L" in spec)
 apply  (force simp: map_le_def)
apply (drule_tac x="insert l L" in spec)
apply (case_tac v)
 apply auto
done


lemma serialization_filter_dom_subset: "serialize (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow>  serialization_filter l \<sigma> L \<subseteq> dom \<sigma>' "
by (drule serialization_filter_dom_subset_pre[of "ObjRef l" \<sigma> \<sigma>'],auto)

lemma serialization_filter_coincide_val: "serialize v \<sigma> \<sigma>' \<Longrightarrow> (\<forall> L. case v of ObjRef l \<Rightarrow> l'\<in>serialization_filter l \<sigma> L \<longrightarrow> \<sigma>' l' = \<sigma> l' | null \<Rightarrow> True) "
apply (erule_tac Q="\<lambda> v \<sigma> \<sigma>'. (\<forall> L. case v of ObjRef l \<Rightarrow> serialization_filter l \<sigma> L \<subseteq> dom \<sigma>' | null \<Rightarrow> {}\<subseteq> dom \<sigma>')" in serialize_composable_inductive_proof)
(*4*)
   apply (clarsimp)
   apply (drule serialization_filter_dom_subset_pre,force)
  apply auto
 apply (drule_tac x=xa in bspec)
  apply force
 apply (case_tac xa)
  apply (force simp: Referenced_locations_Value_def)
(*2*)
 apply clarsimp
 apply (drule_tac x="insert l L" in spec)
 apply (erule impE)
  apply (rule_tac x="insert l L" in exI)
  apply force
 apply  (force simp: map_le_def)
(*1*)
apply (drule_tac x="insert l L" in spec)
apply (case_tac v,simp,simp)
apply (erule disjE,clarsimp)
apply (erule impE)
 apply (drule_tac x="insert l L" in spec)
 apply auto
done



theorem serializationfilter_smallest_serialize: "serialize (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow> (serialize2 l \<sigma>) \<subseteq>\<^sub>m \<sigma>'"
apply (rule map_le_eq)
 apply (frule serialization_filter_dom_subset[of l \<sigma> \<sigma>' "{}"])
 apply force
apply rule
apply (frule_tac l'=x in serialization_filter_coincide_val)
apply (drule_tac x="{}" in spec)
apply (auto simp: restrict_map_def)
done

lemma serialization_filter_origin: "\<sigma> l = Some y\<Longrightarrow>l\<in> serialization_filter l \<sigma> {}"
by (auto split: Storable.splits Value.splits option.splits)



lemma serilalize2_verifies_axiomatic_serialize_1:
    "  ((serialize2 l' \<sigma>)  l=\<sigma>  l\<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ran(fst(obj)). \<exists>\<sigma>''. (serialize v \<sigma> (serialize2 l' \<sigma>))))
     \<Longrightarrow> (serialize (ObjRef l) \<sigma> (serialize2 l' \<sigma>))" 
apply (rule serialize.intros)
apply auto
done

lemma serilalize2_verifies_axiomatic_serialize_2:
    " (serialize2 l' \<sigma>)(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (StoredVal v) \<and>  (serialize v \<sigma> (serialize2 l' \<sigma>))\<Longrightarrow> (serialize (ObjRef l) \<sigma> (serialize2 l' \<sigma>))" 
apply (rule serialize.intros(2))
apply auto
done

lemma serilalize2_verifies_axiomatic_serialize_2:
     "serialize (null) \<sigma>   (serialize2 l' \<sigma>)" 



theorem serialization_filter_verifies_axiomatic_def: "Well_Formed_Store \<sigma> \<longrightarrow> l\<in>dom \<sigma>\<longrightarrow> serialize (ObjRef l) \<sigma> (serialize2 l \<sigma>)"
apply (case_tac "\<sigma> l")
apply auto
apply (frule_tac l=l in Serialization_WF)
apply (case_tac "a")
apply auto
apply ()

theorem serialization_filter_verifies_axiomatic_def: "l\<in>dom \<sigma>\<longrightarrow>Well_Formed_Store \<sigma> \<longrightarrow> serialize (ObjRef l) \<sigma> (\<sigma>|`((\<Union>l\<in>L. serialization_filter l \<sigma> {})\<union>(serialization_filter l \<sigma> L)))"
apply (rule_tac P="\<lambda> S l \<sigma> L. l\<in>dom \<sigma>\<longrightarrow>serialize  (ObjRef l) \<sigma> (\<sigma>|`((\<Union>l\<in>L. serialization_filter l \<sigma> {})\<union>(serialization_filter l \<sigma> L)))" in serialization_filter_induct_1)
apply auto
apply (drule serialization_filter_origin,auto)
apply (rule serialize.intros)
apply (insert serialization_filter_dom_subset[of l \<sigma> "serialize2 l \<sigma>" "{}"])
apply auto
sorry
(*"
sorry
*)

section{*RMI filtering*}


function (sequential) RMI_filter :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set\<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (RMI_filter l \<sigma> L T) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      None => {} |
      Some (Obj obj) \<Rightarrow> (fold (\<lambda>l' S.  (S\<union>(RMI_filter l' \<sigma> (L\<union>{l}\<union>S)   (T\<union>(\<Union>(Referenced_locations_Value`ran(fst(obj))))))) ) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) ({l}))  |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (RMI_filter l' \<sigma> (L\<union>{l}) T)|
      _ \<Rightarrow> {l}))" 

by auto
termination
apply (relation "measure (\<lambda>(l,\<sigma>,L,T). card (dom \<sigma> - L))") 
  apply auto
 apply (subgoal_tac  "card (dom \<sigma> -  insert l (L \<union> xa)) \<le>card (dom \<sigma> - insert l L)")
  apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
   apply (subgoal_tac "finite ((dom \<sigma>-L))")
(*5*)
    apply (drule_tac x=l in Finite_Set.card.remove)+
     apply (insert finite_map)
     apply auto
 apply (subgoal_tac "dom \<sigma> - insert l (L \<union> xa) \<subseteq>(dom \<sigma> - insert l L)")
  apply (subgoal_tac "dom \<sigma> - insert l (L \<union> xa) =(dom \<sigma> - insert l L)\<or>dom \<sigma> -insert l (L \<union> xa) \<subset>(dom \<sigma> - insert l L)")
   apply (elim disjE)
    apply force
(*4*)
   apply (subgoal_tac "finite ((dom \<sigma>- insert l L))")
    apply (drule_tac A="dom \<sigma>-insert l (L \<union> xa)" in Finite_Set.psubset_card_mono)
     apply auto
(*1*)
apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
 apply (subgoal_tac "finite ((dom \<sigma>-L))")
  apply (drule_tac x=l in Finite_Set.card.remove)+
   apply (insert finite_map)
   apply auto
done


(*function (sequential) RMI_filter :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (RMI_filter l \<sigma> L) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      None => {} |
      Some (Obj obj) \<Rightarrow> (fold (\<lambda>l' S.  (S\<union>(RMI_filter l' \<sigma> (L\<union>{l}\<union>S))) ) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) ({l}))  |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (RMI_filter l' \<sigma> (L\<union>{l}))|
      _ \<Rightarrow> {l}))" 
by auto
termination
apply (relation "measure (\<lambda>(l,\<sigma>,L). card (dom \<sigma> - L))") 
  apply auto
 apply (subgoal_tac  "card (dom \<sigma> -  insert l (L \<union> xa)) \<le>card (dom \<sigma> - insert l L)")
  apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
   apply (subgoal_tac "finite ((dom \<sigma>-L))")
(*5*)
    apply (drule_tac x=l in Finite_Set.card.remove)+
     apply (insert finite_map)
     apply auto
 apply (subgoal_tac "dom \<sigma> - insert l (L \<union> xa) \<subseteq>(dom \<sigma> - insert l L)")
  apply (subgoal_tac "dom \<sigma> - insert l (L \<union> xa) =(dom \<sigma> - insert l L)\<or>dom \<sigma> -insert l (L \<union> xa) \<subset>(dom \<sigma> - insert l L)")
   apply (elim disjE)
    apply force
(*4*)
   apply (subgoal_tac "finite ((dom \<sigma>- insert l L))")
    apply (drule_tac A="dom \<sigma>-insert l (L \<union> xa)" in Finite_Set.psubset_card_mono)
     apply auto
(*1*)
apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
 apply (subgoal_tac "finite ((dom \<sigma>-L))")
  apply (drule_tac x=l in Finite_Set.card.remove)+
   apply (insert finite_map)
   apply auto
done
*)
lemma  finite_ran_obj_Referenced_locations_Value: "V=Obj(f,C) \<Longrightarrow>finite (\<Union>l'\<in>ran f. Referenced_locations_Value l')"
apply (drule finite_ran_obj)
apply (auto simp: Referenced_locations_Value_def split: Value.splits)
done

abbreviation serialize_RMI:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
where
"serialize_RMI l \<sigma> \<equiv>  \<sigma> |` RMI_filter l \<sigma> {} {}" 

lemma SF_fold_to_Union[rule_format]: "\<forall>LS . ((distinct fieldlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) T)) ) fieldlist (LS) 
      = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x) T) `(set fieldlist)))))"
apply (induct_tac fieldlist)
apply auto
apply (drule_tac x= "(LS \<union> SF a \<sigma> (insert l (L \<union> LS)) T)" in spec,clarsimp)
apply (rule_tac x="F(a:= LS)" in exI)
apply (auto split: split_if_asm)
done
 
lemma SF_fold_to_Union_what_F[rule_format]: "\<forall>LS . ((distinct fieldlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) T)) ) fieldlist (LS) 
      = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x) T) `(set fieldlist)) \<and> 
  (\<forall> n <length fieldlist. \<forall> l'\<in>F (fieldlist!n). l'\<in>LS \<or> (\<exists> n'<n . (l'\<in>SF (fieldlist!n') \<sigma> (L\<union>{l}\<union>F (fieldlist!n')) T)) ))))"
apply (induct_tac fieldlist)
apply auto
apply (drule_tac x= "(LS \<union> SF a \<sigma> (insert l (L \<union> LS)) T)" in spec,clarsimp)
apply (rule_tac x="F(a:= LS)" in exI)
apply (auto split: split_if_asm)
apply (case_tac n)
apply clarsimp
apply simp
apply (drule_tac x=nat in spec,erule impE,blast)
apply (drule_tac x=l' in bspec)
apply clarsimp
apply auto
apply (drule_tac x="Suc n'" in spec,clarsimp)
done

lemma Union_list_unfold_one: "(\<Union>n\<in>{n'. n' < Suc (length list)}. G ((a # list)!n)  n) = (G a 0) \<union>(\<Union> n\<in>{n'. n' <  (length list)}. (G  (list!n)  (Suc n))) "
apply (subgoal_tac "{n'. n' < Suc (length list)} = insert 0 {Suc n'| n' . n' < (length list)}")
apply  clarsimp
apply force
apply rule
apply rule
apply (case_tac x,simp,force)
apply force
done
lemma Union_list_unfold_one_generalised[rule_format]: "N\<le>(length list)\<longrightarrow>(\<Union>n\<in>{n'. n' < Suc N}. G ((a # list)!n)  n) = (G a 0) \<union>(\<Union> n\<in>{n'. n' <  N}. (G  (list!n)  (Suc n))) "
apply (subgoal_tac "{n'. n' < Suc N} = insert 0 {Suc n'| n' . n' < N}")
apply  clarsimp
apply force
apply rule
apply rule
apply (case_tac x,simp,force)
apply force
done

lemma SF_fold_to_Union_what_F2[rule_format]: "\<forall>LS . ((distinct locationlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) T)) ) locationlist (LS) 
      = LS\<union> \<Union>((\<lambda> n . SF (locationlist!n) \<sigma> (L\<union>{l}\<union>F n) T) `{n'. n'<length locationlist}) \<and> 
(F = (\<lambda>n. if n < length locationlist then 
                  (fold (\<lambda>l' S.  (S\<union>(SF l' \<sigma> (L\<union>{l}\<union>S) T)) ) 
                                        (take n locationlist) (LS)) else {})))))"
apply (induct_tac locationlist)
apply auto
apply (case_tac xa)
apply auto
done

lemma SFI2SG1: "
       (\<And>l \<sigma> L a b S T.
           l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
                     \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a). P (RMI_filter x \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a))) x \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a)) \<Longrightarrow>
                     P ({l} \<union> \<Union>((\<lambda>x. RMI_filter x \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a))) ` \<Union>(Referenced_locations_Value ` ran a))) l \<sigma> L T) \<Longrightarrow>
       (\<And>l \<sigma> L l' T. l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> P (RMI_filter l' \<sigma> (L \<union> {l}) T) l' \<sigma> (L \<union> {l}) T \<Longrightarrow> P ({l} \<union> RMI_filter l' \<sigma> (L \<union> {l}) T) l \<sigma> L T) \<Longrightarrow>
       (\<And>x2 prod x xa.
           l \<notin> L \<Longrightarrow> \<sigma> l = Some x2 \<Longrightarrow>
                     x2 = Obj prod \<Longrightarrow>
                     x \<in> set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
                     P (RMI_filter x \<sigma> (L \<union> {l} \<union> xa) (T \<union> \<Union>(Referenced_locations_Value ` ran (fst prod)))) x \<sigma> (L \<union> {l} \<union> xa) (T \<union> \<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
       (\<And>l \<sigma> L  T. P {} l \<sigma> L T) \<Longrightarrow> \<sigma> l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (RMI_filter l \<sigma> L T) l \<sigma> L T
"
apply (case_tac prod,rename_tac f C)
apply clarsimp
apply (subgoal_tac 
  "set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (f)))) = 
    \<Union>(Referenced_locations_Value ` ran (f))")
 apply clarsimp
(*2*)
 apply (drule_tac x=l in meta_spec)
 apply (drule_tac x=\<sigma> in meta_spec)
 apply (drule_tac x=L in meta_spec)
 apply (drule_tac x=f in meta_spec)
 apply (rotate_tac -1, drule_tac x=C in meta_spec)
 apply simp
 apply (drule_tac x=l in meta_spec)
 apply (drule_tac x=\<sigma> in meta_spec)
 apply (drule_tac x=L in meta_spec)
 apply (drule_tac x="Obj(f,C)" in meta_spec)
 apply (drule_tac x=f in meta_spec)
 apply (drule_tac x=C in meta_spec)
 apply simp
(*2*)
 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>(Referenced_locations_Value ` (ran (f)))))")
  apply (drule_tac SF=RMI_filter and \<sigma> = \<sigma> and LS ="{l}" and l=l and L=L and T="T\<union>UNION (ran f) Referenced_locations_Value" in SF_fold_to_Union,simp)
(*SF_fold_to_Union[rule_format]: "((distinct fieldlist)\<longrightarrow>(\<exists> F . (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) T)) ) fieldlist (LS)  = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x) T) `(set fieldlist)))))"*)
  apply clarsimp
(*3*)
  apply (drule_tac x=F in meta_spec)
  apply (drule_tac x="T" in meta_spec)
   apply (erule meta_impE)
   apply clarsimp
   apply (rotate_tac 7,drule_tac x=x in meta_spec, drule_tac x="F x" in meta_spec)
   apply (clarsimp)
   apply (rotate_tac -1,erule meta_impE)
    apply force
(*4*)
   apply (case_tac "\<sigma> x",force)
   apply (case_tac "aaa",force,simp)
   apply (force split: Value.splits)
  apply force
(*2*)
 apply (rule distinct_sorted_list_of_set)
 apply (subgoal_tac "finite (\<Union>l'\<in>ran (f). Referenced_locations_Value l')")
 apply force
apply (rule finite_ran_obj_Referenced_locations_Value)
apply force
done

lemma  SFI2SG2:"(\<And>x2 Value nat.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = StoredVal Value \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> 
           P (RMI_filter nat \<sigma> (L \<union> {l}) T) nat \<sigma> (L \<union> {l}) T) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (RMI_filter l' \<sigma> (L \<union> {l}) T) l' \<sigma> (L \<union> {l}) T \<Longrightarrow>
              P ({l} \<union> RMI_filter l' \<sigma> (L \<union> {l}) T) l \<sigma> L T) \<Longrightarrow>
  \<sigma> l = Some a \<Longrightarrow>  P {} l \<sigma> L T\<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (RMI_filter l \<sigma> L T) l \<sigma> L T
  "
apply clarsimp
done

lemma RMI_filter_induct_1: "   
(\<And>l \<sigma> L T. P {} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L V T.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L a b S T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (RMI_filter x \<sigma> (L\<union>{l}\<union>(S x)) (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) x \<sigma> (L\<union>{l}\<union>(S x)) 
                                     (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. RMI_filter x \<sigma> (L \<union> {l}\<union>S x) (T\<union>\<Union>(Referenced_locations_Value`(ran a))))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L T)  \<Longrightarrow>
(\<And>l \<sigma> L l' T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (RMI_filter l' \<sigma> (L\<union>{l}) T) l' \<sigma>  (L\<union>{l}) T)\<Longrightarrow>
           (P ({l}\<union>(RMI_filter l' \<sigma> (L\<union>{l}) T)) l \<sigma> L T))         \<Longrightarrow>   
   P (RMI_filter l' \<sigma>' L' T) l' \<sigma>' L' T"
apply (rule RMI_filter.induct)
apply (case_tac "\<sigma> l")
 apply (simp)
(*1*)
apply (case_tac a)
 apply (erule SFI2SG1,simp,simp,simp,simp,simp)
apply (rename_tac val,case_tac val)
 apply force
apply (erule SFI2SG2,simp+)
done



lemma RMI_filterD_L:"x\<in>RMI_filter l \<sigma> L T\<Longrightarrow> l\<notin>L"
apply force
done

lemma RMI_filterD_L_contrapos:"l\<notin>RMI_filter l \<sigma> L T \<Longrightarrow> l\<in>L \<or> \<sigma> l = None"
apply (simp split: option.splits Storable.splits split_if_asm )
apply (clarsimp,rename_tac f C)
apply (subgoal_tac "l\<in>{l}",drule_tac F="\<lambda> l' S . (if l' = l \<or> l' \<in> L \<or> l' \<in> S then {}
                                  else case \<sigma> l' of None \<Rightarrow> {}
                                                 | Some (Obj obj) \<Rightarrow>
                                                     fold (\<lambda>l'a Sa. Sa \<union> RMI_filter l'a \<sigma> (insert l (L \<union> S) \<union> {l'} \<union> Sa) (T \<union> UNION (ran (fst (f, C))) Referenced_locations_Value \<union> \<Union>(Referenced_locations_Value ` ran (fst obj))))
                                                      (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {l'}
                                                 | Some (StoredVal null) \<Rightarrow> {l'} | Some (StoredVal (ObjRef l'a)) \<Rightarrow> {l'} \<union> RMI_filter l'a \<sigma> (insert l (L \<union> S) \<union> {l'}) (T \<union> UNION (ran (fst (f, C))) Referenced_locations_Value))" in AuxiliaryFunctions.foldr_Un_init
       ,blast)
apply blast
apply (simp split: Value.splits Storable.splits split_if_asm )
done

lemma RMI_filter_no_l[simp]:"l\<notin>RMI_filter l \<sigma> L T= (l\<in>L \<or> \<sigma> l = None)"
apply rule
apply (rule RMI_filterD_L_contrapos,simp)
apply auto
done

lemma RMI_filterD_cases: "x\<in>RMI_filter l \<sigma> L T\<Longrightarrow> 
                                   ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(RMI_filter l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(fields)))))) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>RMI_filter l' \<sigma> (L\<union>{l}) T)))"
apply (case_tac "\<sigma> l")
apply (simp split: option.splits Storable.splits split_if_asm )
apply (case_tac "x=l",force)
apply (case_tac a)
apply (force split: option.splits Storable.splits split_if_asm Value.splits)
apply (force split: Value.splits split_if_asm)
done

lemma RMI_filterI_cases: "l\<notin>L\<Longrightarrow> ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(RMI_filter l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(fields))))) ) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>RMI_filter l' \<sigma> (L\<union>{l}) T)) ) 
                                   \<Longrightarrow> x\<in>RMI_filter l \<sigma> L T"
apply (elim disjE)
apply (clarsimp split: Storable.splits split_if_asm)
apply (clarsimp split: Storable.splits split_if_asm )
(*3*)
apply (case_tac y,rename_tac obj',case_tac obj')
apply (subgoal_tac "l\<in>{l}",drule AuxiliaryFunctions.foldr_Un_init,simp,blast)
apply (simp split: Value.splits)
apply force
done

lemma RMI_filter_def2: "x\<in>RMI_filter l \<sigma> L T = (l\<notin>L \<and> ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(RMI_filter l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(fields))))) ) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>RMI_filter l' \<sigma> (L\<union>{l}) T)) )) 
                       "
apply rule 
apply (frule RMI_filterD_cases, drule RMI_filterD_L,blast)
apply (rule RMI_filterI_cases,blast,blast)
done

declare RMI_filter.simps[simp del]

lemma RMI_filter_empty[simp]: "(RMI_filter l \<sigma> L T ={}) = (l\<in>L\<or> \<sigma> l = None)"
apply rule
apply (case_tac "l\<in>(RMI_filter l \<sigma> L T)")
apply force
apply (drule RMI_filterD_L_contrapos)
apply simp
apply (clarsimp simp: RMI_filter.simps)
done

lemma serialize_value_RMI: "(serialize_RMI l \<sigma>) l' = Some x \<Longrightarrow> \<sigma> l' = Some x"
apply (subgoal_tac "l'\<in>(RMI_filter l \<sigma> {} {})")
 apply (drule_tac m=\<sigma> in Map.restrict_in)
 apply force
apply (rule Map_restrict_Some,blast)
done

lemma SFI3SG1: "
       (\<And>l \<sigma> L T. P {} l \<sigma> L T) \<Longrightarrow>
       (\<And>l \<sigma> L a b  T .
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
           \<Union>(Referenced_locations_Value ` ran a) = {} \<Longrightarrow>P {l} l \<sigma> L T) \<Longrightarrow>
       (\<And>l \<sigma> L a b S T locationlist.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
           locationlist = sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran a)) \<Longrightarrow>
           locationlist \<noteq> [] \<Longrightarrow>
           S = (\<lambda>n. if n < length locationlist then 
                  (fold (\<lambda>l' S.  (S\<union>(RMI_filter l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(a))))) ) 
                                        (take n locationlist) ({l})) else {}) \<Longrightarrow>
           \<forall>i<length locationlist.
              P (RMI_filter (locationlist!i) \<sigma> (L \<union> {l} \<union> S i) (T \<union> \<Union>(Referenced_locations_Value ` ran a))) (locationlist!i) \<sigma> (L \<union> {l} \<union> S i) (T \<union> \<Union>(Referenced_locations_Value ` ran a)) \<Longrightarrow>
           P ({l} \<union> \<Union>((\<lambda>x. RMI_filter (locationlist!x) \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a))) ` {0..length(locationlist) - 1})) l \<sigma> L T) \<Longrightarrow>
       (\<And>x2 prod x xa.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = Obj prod \<Longrightarrow>
           x \<in> set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
           P (RMI_filter x \<sigma> (L \<union> {l} \<union> xa) (T \<union> \<Union>(Referenced_locations_Value ` ran (fst prod)))) x \<sigma> (L \<union> {l} \<union> xa) (T \<union> \<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
       \<sigma> l = Some (Obj (f,C)) \<Longrightarrow> P (RMI_filter l \<sigma> L T) l \<sigma> L T
"
apply clarsimp
apply (subgoal_tac 
  "set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (f)))) = 
    \<Union>(Referenced_locations_Value ` ran (f))")
 apply clarsimp

(*2*)
 apply (rotate_tac 2, drule_tac x=l in meta_spec)
 apply (drule_tac x=\<sigma> in meta_spec)
 apply (drule_tac x=L in meta_spec)
 apply (drule_tac x=f in meta_spec)
 apply (rotate_tac -1, drule_tac x=C in meta_spec)
 apply simp
 apply (drule_tac x=l in meta_spec)
 apply (drule_tac x=\<sigma> in meta_spec)
 apply (drule_tac x=L in meta_spec)
 apply (drule_tac x="Obj(f,C)" in meta_spec)
 apply (drule_tac x=f in meta_spec)
 apply (drule_tac x=C in meta_spec)
 apply (drule_tac x=l in meta_spec)
 apply (drule_tac x=\<sigma> in meta_spec)
 apply (drule_tac x=L in meta_spec)
 apply (drule_tac x="Obj(f,C)" in meta_spec)
 apply (drule_tac x=f in meta_spec)
 apply (drule_tac x=C in meta_spec)
 apply (simp(no_asm) add: RMI_filter.simps)
apply clarsimp
(*2*)
 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>(Referenced_locations_Value ` (ran (f)))))")
  apply (drule_tac SF=RMI_filter and \<sigma> = \<sigma> and LS ="{l}" and l=l and L=L and T="T\<union>(\<Union>x\<in>ran f. Referenced_locations_Value x)" in SF_fold_to_Union_what_F2,clarsimp)
(*3*)
  apply (drule_tac x=" (\<lambda>n. if n < length (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x))
                 then fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (L \<union> {l} \<union> S) (T \<union> \<Union>(Referenced_locations_Value ` ran f))) (take n (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x))) {l} else {}) "in meta_spec)
  apply (rotate_tac -1,drule_tac x="T" in meta_spec)
  apply (rotate_tac -1,drule_tac x="sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x)" in meta_spec)
   apply (simp,rotate_tac -1,erule meta_impE)
   apply clarsimp
   apply (drule_tac x="sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x)!i" in meta_spec)
      apply (rotate_tac -1,drule_tac x="fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (insert l (L \<union> S)) (T \<union> (\<Union>x\<in>ran f. Referenced_locations_Value x)))
                                (take i (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x))) {l}" in meta_spec)
      apply (erule meta_impE)
      apply force
      apply force

(*3*)
   apply (subgoal_tac 
"(\<Union>x\<in>{0..length (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x)) - 1}.
                    RMI_filter (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x) ! x) \<sigma>
                     (insert l (L \<union> (if x < length (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x))
                                      then fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (L \<union> {l} \<union> S) (T \<union> \<Union>(Referenced_locations_Value ` ran f)))
                                            (take x (sorted_list_of_set (UNION (ran f) Referenced_locations_Value))) {l}
                                      else {})))
                     (T \<union> (\<Union>x\<in>ran f. Referenced_locations_Value x)))
=(\<Union>l'\<in>{n'. n' < length (sorted_list_of_set (\<Union>l'\<in>ran f. Referenced_locations_Value l'))}.
                    RMI_filter (sorted_list_of_set (\<Union>l'\<in>ran f. Referenced_locations_Value l') ! l') \<sigma>
                     (insert l (L \<union> fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (insert l (L \<union> S)) (T \<union> (\<Union>l'\<in>ran f. Referenced_locations_Value l')))
                                      (take l' (sorted_list_of_set (\<Union>l'\<in>ran f. Referenced_locations_Value l'))) {l}))
                     (T \<union> (\<Union>l'\<in>ran f. Referenced_locations_Value l')))
")
   apply (rotate_tac -1,erule ssubst)
   back back
   apply (simp)
   apply (rule UNION_eqI)
   apply clarsimp
   apply rule
   apply (clarsimp)
   apply (rule_tac x=x in exI)
   apply clarsimp
   apply clarsimp
   apply (case_tac x)
   apply clarsimp
   apply blast
   apply (simp add1: le_less)
   apply (subgoal_tac x=length
   
   apply (rule UNION_UNION_eqI)
   apply (rule UNION_UNION_eqI)

  apply
(*
   apply force
   apply
(*   apply force
   apply (subgoal_tac "(\<Union>x\<in>ran f. \<Union>x\<in>Referenced_locations_Value x. RMI_filter x \<sigma> (insert l (L \<union> F x)) (T \<union> (\<Union>x\<in>ran f. Referenced_locations_Value x)))
= 
(\<Union>m\<in>{n'. n' < length (sorted_list_of_set (\<Union>l'\<in>ran f. Referenced_locations_Value l'))}.
                         RMI_filter (sorted_list_of_set (\<Union>l'\<in>ran f. Referenced_locations_Value l') ! m) \<sigma> (insert l (L \<union> F m)) (T \<union> (\<Union>l'\<in>ran f. Referenced_locations_Value l')))
")
   apply force
   apply (rule UNION_UNION_eqI)
   apply (clarsimp, rename_tac xf)
   
 (*  apply (subgoal_tac "finite (\<Union>l'\<in>ran (f). Referenced_locations_Value l')")*)
   apply (subgoal_tac "finite (\<Union>x\<in>ran f. Referenced_locations_Value x)")
   apply (drule_tac x=xf in  sorted_list_of_set_nthI)
   apply blast
   apply clarsimp
   apply (rule_tac x=n in exI)
   apply (subgoal_tac "card (\<Union>x\<in>ran f. Referenced_locations_Value x)= length (sorted_list_of_set (\<Union>x\<in>ran f. Referenced_locations_Value x))")
   apply simp
   apply (rule sorted_list_of_set_card_length)
   apply (clarsimp split: option.splits)
   apply (case_tac x2,simp,simp)

   apply (rule sorted_list_of_set_card_length)
   apply clarsimp
    apply force(*
   apply (erule meta_impE)
    apply clarsimp
   apply (rotate_tac 7,drule_tac x=x in meta_spec, drule_tac x="F x" in meta_spec)
   apply (clarsimp)
(*4*)
   apply (case_tac "\<sigma> x",force)
   apply (case_tac "aaa",force,simp)
   apply (force split: Value.splits)
  apply force
(*2*)
 apply (rule distinct_sorted_list_of_set)
 apply (subgoal_tac "finite (\<Union>l'\<in>ran (f). Referenced_locations_Value l')")
 apply force
apply (rule finite_ran_obj_Referenced_locations_Value)
apply force
done
*)
*)
lemma RMI_filter_induct_2: "   
(\<And>l \<sigma> L T. P {} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L V T.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L a b S T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
        let locationlist = sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(a))) in
           S = (\<lambda> n . (if (n< length locationlist) then (L\<union>{l}\<union> (\<Union>k\<in>{n'. n'<n}. (RMI_filter ((locationlist)!k) \<sigma> (L\<union>{l}\<union>S k) T))) else {})) \<Longrightarrow>
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (RMI_filter x \<sigma> (L\<union>{l}\<union>(S x)) (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) x \<sigma> (L\<union>{l}\<union>(S x)) 
                                     (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. RMI_filter x \<sigma> (L \<union> {l}\<union>S x) (T\<union>\<Union>(Referenced_locations_Value`(ran a))))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L T)  \<Longrightarrow>
(\<And>l \<sigma> L l' T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (RMI_filter l' \<sigma> (L\<union>{l}) T) l' \<sigma>  (L\<union>{l}) T)\<Longrightarrow>
           (P ({l}\<union>(RMI_filter l' \<sigma> (L\<union>{l}) T)) l \<sigma> L T))         \<Longrightarrow>   
   P (RMI_filter l' \<sigma>' L' T) l' \<sigma>' L' T"
apply (rule RMI_filter.induct)
apply (case_tac "\<sigma> l")
 apply (simp add: RMI_filter.simps)
(*1*)
apply (case_tac a)

 apply (erule SFI2SG1,simp,simp,simp,simp,simp)
apply (case_tac Value)
(* apply force
apply (erule SFI2SG2,simp+)
done



lemma T_is_accessory_pre: "x\<in>RMI_filter l \<sigma> L T \<longrightarrow> x\<in>RMI_filter l \<sigma> L (T\<union>T')"
apply (rule_tac P="\<lambda> S l \<sigma> L T. x\<in>S \<longrightarrow>x\<in> RMI_filter l \<sigma> L (T\<union>T')" in RMI_filter_induct_1)
apply auto
apply (erule RMI_filterI_cases,force)
apply (erule RMI_filterI_cases,force)
apply (erule RMI_filterI_cases,simp)
apply (drule_tac x=xa in bspec,simp)
apply (drule_tac x=xaa in bspec,simp)
apply clarsimp
S too imprecise

lemma serialization_filter_WF_1step_obj[rule_format]: 
  "l\<in>RMI_filter l'' \<sigma> L T\<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some (ObjRef l') 
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  \<exists> t\<in>T. l'\<in>serialization_filter l'' \<sigma> L {} \<or>l'\<in>L\<or>l'\<in>serialization_filter l'' \<sigma> L T"
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. l\<in>S \<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some ( ObjRef l')   \<longrightarrow>Well_Formed_Store \<sigma>
\<longrightarrow>   l'\<in>L\<or>l'\<in>S" in   serialization_filter_induct_1)
(*4*)
   apply force
  apply clarsimp
 apply (case_tac "l'=la")
  apply simp
 apply (case_tac "l=la")
  apply clarsimp
  apply (drule_tac x="( ObjRef l')" in bspec)
   apply (rule ranI)
   apply blast
  apply (drule_tac x=l' in bspec,simp,simp)
  apply (auto split: split_if_asm )
(*2*)
 apply (drule_tac x=l' in bspec,simp)
  apply (rule_tac x="( ObjRef l')" in bexI)
  apply simp
  apply (rule ranI,simp)
 apply (clarsimp split: option.splits Storable.splits simp: Well_Formed_Store_def)
  apply (drule_tac x=l in bspec,blast)
  apply (drule Referenced_locations_LocationI_Obj, simp+)
  apply force
(*2*)
 apply (simp split: Value.splits)
apply (drule_tac x=l' in bspec,simp)
 apply (rule_tac x="( ObjRef l')" in bexI)
  apply simp
 apply (rule ranI,simp)
apply auto
done


lemma Serialization_WF: "Well_Formed_Store \<sigma> \<Longrightarrow> Well_Formed_Store (serialize_RMI l \<sigma>)"
apply (unfold Well_Formed_Store_def)
apply (intro ballI)
apply (fold Well_Formed_Store_def)
apply (subgoal_tac " la \<in> dom \<sigma>")
 apply (case_tac "\<sigma> la")
  apply blast
 apply rule
 apply (unfold Referenced_locations_Location_def)
(*2*)
 apply (case_tac  "serialize_RMI l \<sigma> la")
  apply blast
 apply (drule serialize_value)
 apply (subgoal_tac "a=aa")
  apply clarify
  apply (case_tac aa,case_tac prod)
   apply (frule serialize_value)
   apply  clarsimp
   apply (subgoal_tac "serialize2 l \<sigma> la = Some (Obj (ab, ba))")
(*5*)
    apply clarsimp
    apply (simp add: ran_def Referenced_locations_Value_def,clarify)
    apply (subgoal_tac "la\<in>serialization_filter l \<sigma> {}")
     apply (drule serialization_filter_WF_1step_obj,simp, force split: Value.splits)
       apply (simp split: Value.splits,simp)
     apply (simp split: Value.splits)
     apply (drule Well_Formed_StoreD_obj,simp,simp)
     apply blast
    apply (rule Map_restrict_Some,force)
   apply simp
  apply (frule serialize_value)
  apply simp
(*3*)
  apply (subgoal_tac "la\<in>serialization_filter l \<sigma> {}")
   apply (drule serialization_filter_WF_1step_ref,simp, simp split: Value.splits,simp,simp)
   apply (simp split: Value.splits)
   apply (drule Well_Formed_StoreD_ref,simp)
   apply blast
(*3*)
  apply (rule Map_restrict_Some,force)
 apply force
apply (insert serialize_subset[of \<sigma> l])
apply blast
done


lemma RMI_filter_union: (RMI_filter l' \<sigma> L\<union>L')\<union>L' = (RMI_filter l' \<sigma> L\<union>L')

lemma fold_union_init[rule_format]: "\<forall> L'' . fold (\<lambda>l' S. S \<union> (RMI_filter l' \<sigma> S)) list (L \<union> L'') = (fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> S) list L) \<union> L''"
apply (induct_tac list)
apply force
apply clarsimp
apply (drule_tac x="L''\<union>L'' \<union> RMI_filter a \<sigma> (L \<union> L'')" in spec) 
apply simp
apply (subgoal_tac "(L'' \<union> F a (L \<union> L'')) =   (L'' \<union> (F a (L \<union> L'')))")
apply simp
apply blast
apply blast
done
lemma "\<forall> L' . l \<in> fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (L' \<union> S)) list L = (l\<in>L\<or> 
            ( \<exists> i<length list . let S =  fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (L' \<union> S)) (take i list) L  in  (l\<in>RMI_filter (list!i) \<sigma> (L' \<union> S) \<and> l\<notin>S)))"
apply (induct_tac list)
apply force
apply (clarsimp)
apply (subgoal_tac "fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (L' \<union> S)) list (L \<union> RMI_filter a \<sigma> (L' \<union> L)) = fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (L' \<union> S)) list L \<union> RMI_filter a \<sigma> (L' \<union> L)")
defer
apply (rule_tac list=list and L''="RMI_filter a \<sigma> (L' \<union> L)"  in fold_union_init)
apply clarsimp
apply (case_tac "l\<in>L")
apply force
apply clarsimp
apply rule
apply (case_tac "l \<in> RMI_filter a \<sigma> (L' \<union> L)")
apply clarsimp
apply (rule_tac x=0 in exI)
apply clarsimp
apply (clarsimp simp: Let_def)

apply (rule_tac x="Suc i" in exI)
apply (clarsimp simp: Let_def)

lemma " \<forall> x . l \<in> RMI_filter l' \<sigma> L \<longrightarrow>
                    x \<in> RMI_filter l \<sigma> L \<longrightarrow>x \<in> RMI_filter l' \<sigma> L"
apply (rule_tac P = " \<lambda> l' \<sigma> L .\<forall> x .l \<in> RMI_filter l' \<sigma> L \<longrightarrow>
                    x \<in> RMI_filter l \<sigma> L \<longrightarrow>x \<in> RMI_filter l' \<sigma> L" in RMI_filter.induct)
apply (case_tac "l=la")
apply clarsimp
apply clarsimp
apply (frule RMI_filterD_L)
apply (frule RMI_filterD_L)
apply (drule RMI_filterD_cases,clarsimp)
apply (elim disjE)
apply clarsimp
apply(thin_tac "(\<And>x2 Value nat. False \<Longrightarrow> x2 = StoredVal (ObjRef nat) \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> l \<in> RMI_filter nat \<sigma> (insert la L) \<longrightarrow> (\<forall>x. x \<in> RMI_filter l \<sigma> (insert la L) \<longrightarrow> x \<in> RMI_filter nat \<sigma> (insert la L))) ")
apply (drule_tac x= "Obj(fields,C)" in meta_spec)
apply (drule_tac x= "fields" in meta_spec)
apply (drule_tac x= C in meta_spec)
apply (rule RMI_filterI_cases)
apply clarsimp
apply clarsimp

(*
DO NOT DO FOLD TO UNION FIND BETTER
*)

 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>x\<in>ran fields. Referenced_locations_Value x))")
apply (drule_tac SF=RMI_filter and \<sigma> = \<sigma> and LS ="{la}" and l=la and L="L" in SF_fold_to_Union)
apply clarsimp
apply (drule_tac x= xa in meta_spec)
apply (drule_tac x= "F xa" in meta_spec)
apply clarsimp
apply (rule_tac x=xa in bexI)
apply (drule_tac x=x in spec)
apply clarsimp
apply (erule disjE,simp)

lemma RMI_filter_induct_double_union[rule_format]: "   
   \<forall>  l'. ( RMI_filter l \<sigma> L \<subseteq> RMI_filter l' \<sigma> L \<union> RMI_filter l \<sigma> (L\<union>RMI_filter l' \<sigma> L))"
apply (rule_tac P = " \<lambda> l \<sigma> L . \<forall>  l'. ( RMI_filter l \<sigma> L \<subseteq> RMI_filter l' \<sigma> L \<union> RMI_filter l \<sigma> (L\<union>RMI_filter l' \<sigma> L))" in RMI_filter.induct)
apply clarsimp
apply (erule contrapos_np)
apply (frule RMI_filterD_L)
apply (frule RMI_filterD_cases,simp)
apply (elim disjE)
apply clarsimp
apply(thin_tac "       (\<And>x2 Value nat. False \<Longrightarrow> x2 = StoredVal (ObjRef nat) \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> \<forall>l'. RMI_filter nat \<sigma> (insert l L) \<subseteq> RMI_filter l' \<sigma> (insert l L) \<union> RMI_filter nat \<sigma> (insert l (L \<union> RMI_filter l' \<sigma> (insert l L)))) ")
apply (drule_tac x= "Obj(fields,C)" in meta_spec)
apply (drule_tac x= "fields" in meta_spec)
apply (drule_tac x= C in meta_spec)
apply clarsimp
apply (rule RMI_filterI_cases)
apply clarsimp


apply (subgoal_tac "\<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I}\<subseteq> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I} \<union> RMI_filter l \<sigma> (L \<union> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I})")
apply (erule Set.subset_trans,simp)
apply blast
(*1*)
apply rule
defer
apply simp
apply (clarsimp)

apply clarsimp
apply (thin_tac "(\<And>x2 a b x xa. False \<Longrightarrow> x2 = Obj (a, b) \<Longrightarrow>
                                 x \<in> set (sorted_list_of_set (\<Union>x\<in>ran a. Referenced_locations_Value x)) \<Longrightarrow>
                                 ?P x2 a b x xa)")
apply (drule_tac x= "(StoredVal (ObjRef l'))" in meta_spec)
apply (drule_tac x= "((ObjRef l'))" in meta_spec)
apply (drule_tac x= l' in meta_spec)
apply simp
apply (drule_tac x=L' in spec)
apply (drule_tac x= S in spec)
apply (drule_tac x= I in spec)


lemma RMI_filter_induct_double[rule_format]: "   
   \<forall> L' S S' I ll LL. ((S\<subseteq>S'\<and>S'=\<Union>{RMI_filter (ll i) \<sigma> (LL i) | i . i\<in> I})\<longrightarrow>(S\<union>(RMI_filter l \<sigma> (L\<union>L'\<union>S))\<subseteq> S'\<union>(RMI_filter l \<sigma> (L\<union>S'))))"
apply (rule_tac P = " \<lambda> l \<sigma> L . \<forall> L' S S' I ll LL. ((S\<subseteq>S'\<and>S'=\<Union>{RMI_filter (ll i) \<sigma> (LL i) | i . i\<in> I})\<longrightarrow>(S\<union>(RMI_filter l \<sigma> (L\<union>L'\<union>S))\<subseteq> S'\<union>(RMI_filter l \<sigma> (L\<union>S'))))" in  RMI_filter.induct)
apply clarsimp
apply rule
apply (subgoal_tac "\<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I}\<subseteq> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I} \<union> RMI_filter l \<sigma> (L \<union> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I})")
apply (erule Set.subset_trans,simp)
apply blast
(*1*)
apply rule
apply (frule RMI_filterD_L)
apply (frule RMI_filterD_cases,simp)
apply (elim disjE)
defer
apply simp
apply (clarsimp)

apply clarsimp
apply (thin_tac "(\<And>x2 a b x xa. False \<Longrightarrow> x2 = Obj (a, b) \<Longrightarrow>
                                 x \<in> set (sorted_list_of_set (\<Union>x\<in>ran a. Referenced_locations_Value x)) \<Longrightarrow>
                                 ?P x2 a b x xa)")
apply (drule_tac x= "(StoredVal (ObjRef l'))" in meta_spec)
apply (drule_tac x= "((ObjRef l'))" in meta_spec)
apply (drule_tac x= l' in meta_spec)
apply simp
apply (drule_tac x=L' in spec)
apply (drule_tac x= S in spec)
apply (drule_tac x= I in spec)
apply (drule_tac x= ll in spec)
apply (drule_tac x= LL in spec)
apply simp
apply (subgoal_tac "x\<in>\<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I}\<or>x\<in>RMI_filter l' \<sigma> (insert l (L \<union> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I}))")
apply(case_tac "x \<in> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I}")
apply (blast)
apply clarsimp
apply (subgoal_tac "x \<in> RMI_filter l \<sigma> (L \<union> \<Union>{RMI_filter (ll i) \<sigma> (LL i) |i. i \<in> I})")
apply simp
apply (rule RMI_filterI_cases)
apply clarsimp
apply(subgoal_tac "RMI_filter l \<sigma> (L \<union> L' \<union> S) ={}")
apply blast
apply(subgoal_tac "l\<in>(L \<union> L' \<union> S)")
apply(thin_tac "x \<in> RMI_filter l \<sigma> (L \<union> L' \<union> S)")
apply clarsimp
apply(subgoal_tac "l\<in>S")
apply blast
apply (drule_tac c=l in Set.subsetD,simp)
apply (rule RMI_filterI_cases) 
 apply (simp (no_asm) add: RMI_filter.simps)
(*1*)
apply (case_tac a, case_tac prod)
apply (clarsimp simp del: RMI_filter.simps)
apply (rule)
apply (drule Set.Un_mono ,blast,simp)
apply (thin_tac "(\<And>x2 Value nat. ?P x2 Value nat\<Longrightarrow>?Q x2 Value nat \<Longrightarrow>?R x2 Value nat\<Longrightarrow>?U x2 Value nat\<Longrightarrow>?T x2 Value nat)")
apply (drule_tac x="Obj (aaa, ba)" in meta_spec)
apply (drule_tac x=aaa in meta_spec)
apply (drule_tac x=ba in meta_spec)
apply (clarsimp simp del: RMI_filter.simps)
apply (clarsimp)
apply (case_tac "l\<in>L",simp)
apply (case_tac "l\<in>L'",simp)
apply (case_tac "l\<in>S",simp)
apply (clarsimp simp del: RMI_filter.simps split: split_if_asm)
apply simp
 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>x\<in>ran aaa. Referenced_locations_Value x))")
  apply (drule_tac SF=RMI_filter and \<sigma> = \<sigma> and LS ="{l}" and l=l and L="L\<union>L'\<union>S" in SF_fold_to_Union,simp)
apply (clarsimp)
apply (case_tac "x=l",simp)
apply (rule_tac x="(case \<sigma> (ll i) of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow>  fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (LL i \<union> {ll i} \<union> S)) (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {ll i}
                                                                           | Some (StoredVal null) \<Rightarrow> {ll i} | Some (StoredVal (ObjRef l')) \<Rightarrow> {ll i} \<union> RMI_filter l' \<sigma> (LL i \<union> {ll i}))" in exI)
apply simp
apply (rule_tac x=i in exI)
apply simp
apply (clarsimp simp del: RMI_filter.simps )
apply (subgoal_tac "l'\<in>LL i \<or>l'\<in>RMI_filter (ll i) \<sigma> (LL i)") (* IF WELL FORMEDNESS IS PROVEN*)
apply (elim disjE)
apply (subgoal_tac "l'\<in>RMI_filter l \<sigma> (L\<union> \<Union>{RMI_filter (ll i) \<sigma> (LL i) | i . i\<in> I})")
apply (clarsimp  split: split_if_asm)
apply (drule_tac x="(case \<sigma> (ll i) of None \<Rightarrow> {}        
| Some (Obj obj) \<Rightarrow>fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (LL i \<union> {ll i} \<union> S)) (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {ll i}                                                
| Some (StoredVal null) \<Rightarrow> {ll i} | Some (StoredVal (ObjRef l')) \<Rightarrow> {ll i} \<union> RMI_filter l' \<sigma> (LL i \<union> {ll i}))" in spec)
apply simp
apply (drule_tac x= i in spec)
apply simp
apply (simp (no_asm))
apply (clarsimp simp del: RMI_filter.simps)
apply simp
apply (drule_tac x= i in spec)
apply simp
apply 
apply
(*
apply clarsimp
apply (case_tac "\<sigma> l'",simp)
apply (case_tac "\<sigma> (ll i)",simp)
apply clarsimp

apply (rule_tac x="(case \<sigma> (ll i) of None \<Rightarrow> {}
                                                                                                                 | Some (Obj obj) \<Rightarrow>
  fold (\<lambda>l' S. S \<union> RMI_filter l' \<sigma> (LL i \<union> {ll i} \<union> S)) (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {ll i}
                                                                                                                 | Some (StoredVal null) \<Rightarrow> {ll i} | Some (StoredVal (ObjRef l')) \<Rightarrow> {ll i} \<union> RMI_filter l' \<sigma> (LL i \<union> {ll i}))" in exI)
apply (clarsimp simp del: RMI_filter.simps )
apply (rule_tac x=i in exI)
apply simp

apply clarsimp
apply (drule_tac x="{}" in meta_pec) (*? ? ?*)
apply (case_tac "l\<in>L")
apply simp
apply (clarsimp simp del: RMI_filter.simps)
 apply (clarsimp split: option.splits Storable.splits)
apply (clarsimp split: Value.splits)
apply bast
sorry


(*induction useful\<Or>? (\<And>l \<sigma> L a b S L'.
        l \<notin> L \<Longrightarrow> l \<notin> L' \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
          (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). (\<forall> L'. 
                          (RMI_filter x \<sigma> (L\<union>L'\<union>{l}\<union>(S x))) \<subseteq>(RMI_filter x \<sigma> (L\<union>{l}\<union>(S x))))) \<Longrightarrow>
            ({l}\<union>(\<Union> ((\<lambda> x. RMI_filter x \<sigma> (L\<union>L' \<union> {l}\<union>S x))` 
                                             \<Union>(Referenced_locations_Value`ran(a)))))\<subseteq> ({l}\<union>(\<Union> ((\<lambda> x. RMI_filter x \<sigma> ((L) \<union> {l}\<union>S x))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) )  \<Longrightarrow>
(\<And>l \<sigma> L l' L'.
        l \<notin> L\<Longrightarrow> l\<notin> L' \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
           \<forall> L'. (RMI_filter l' \<sigma> (L\<union>L'\<union>{l}))\<subseteq> ( (RMI_filter l' \<sigma> (L\<union>{l})) )\<Longrightarrow>
           (({l}\<union>(RMI_filter l' \<sigma> (L\<union>L'\<union>{l})))\<subseteq>  ({l}\<union>(RMI_filter l' \<sigma> ((L)\<union>{l}))) ))         \<Longrightarrow>   
*)
lemma " S \<subseteq> S' \<Longrightarrow> \<sigma> l = Some (Obj (aaa, ba)) \<Longrightarrow>
                   (\<And>x xa. l \<notin> L \<Longrightarrow> x \<in> set (sorted_list_of_set (\<Union>x\<in>ran aaa. Referenced_locations_Value x)) \<Longrightarrow>
                                      \<forall>L' S S'. S \<subseteq> S' \<longrightarrow> S \<subseteq> S' \<union> RMI_filter x \<sigma> (insert l (L \<union> xa \<union> S')) \<and>
                                                            RMI_filter x \<sigma> (insert l (L \<union> xa \<union> L' \<union> S)) \<subseteq> S' \<union> RMI_filter x \<sigma> (insert l (L \<union> xa \<union> S'))) \<Longrightarrow>
                   x \<in> RMI_filter l \<sigma> (L \<union> L' \<union> S) \<Longrightarrow> x \<notin> RMI_filter l \<sigma> (L \<union> S') \<Longrightarrow> x \<in> S'"
apply(induct_tac list)
apply force
apply (clarsimp simp del: RMI_filter.simps)
apply (rotate_tac -1,frule_tac x="(La \<union> RMI_filter a \<sigma> (L  \<union> La))" in spec)
apply (drule_tac x="(La \<union> RMI_filter a \<sigma> (L\<union>L'  \<union> La))" in spec)
apply (clarsimp simp del: RMI_filter.simps)
apply auto
apply (case_tac "\<sigma> l'")
sorry
lemma RMI_filter_induct_double[rule_format]: "   
   \<forall> L'. (RMI_filter l \<sigma> (L\<union>L'))\<subseteq> (RMI_filter l \<sigma> (L))"
apply (rule_tac P = " \<lambda> l \<sigma> L . \<forall> L'. (RMI_filter l \<sigma> (L\<union>L'))\<subseteq> (RMI_filter l \<sigma> (L))" in  RMI_filter.induct)
apply (clarsimp simp del: RMI_filter.simps)
apply (case_tac "\<sigma> l")
 apply (clarsimp split: split_if_asm)
(*1*)
apply (case_tac a, case_tac prod)
apply (rotate_tac 2,drule_tac x=a in meta_spec)
apply (rotate_tac -1,drule_tac x=aa in meta_spec)
apply (rotate_tac -1,drule_tac x=b in meta_spec)
 apply (clarsimp split: Value.splits split_if_asm)
apply (erule Set.rev_subsetD)
apply (rule)
apply (case_tac Value)
 apply fore

apply (erule SFI2SG2,simp+)
done

lemma l_in_fold_union_selection[rule_format]: "
\<forall> L. l \<in> fold (\<lambda>l' S. S \<union> (F l' S))  list ({l}\<union>L)"
apply (induct_tac list)
apply auto
done

lemma l_in_fold_union_selection_empty[rule_format]: "
l \<in> fold (\<lambda>l' S. S \<union> (F l' S))  list {l}"
apply (insert l_in_fold_union_selection [of l F list "{}"])
apply auto
done

lemma Serialization_2_excluded_set_subset: "\<forall> L . L\<subseteq>L' \<longrightarrow> RMI_filter l \<sigma> L' \<subseteq> RMI_filter l \<sigma> L"
apply (rule_tac P= "\<lambda> S l \<sigma> L'. (\<forall>L. L\<subseteq>L' \<longrightarrow> S \<subseteq> RMI_filter l \<sigma> L)" in   RMI_filter_induct_1)
apply clarsimp
apply (clarsimp split: Value.splits)
apply blast
apply (clarsimp simp del: RMI_filter.simps)
apply rule
apply (subgoal_tac "l\<notin>La")
apply (clarsimp split: Value.splits Storable.splits)
apply (rule l_in_fold_union_selection_empty)
apply blast
apply (clarsimp simp del: RMI_filter.simps)
apply (drule_tac x=xa in bspec,blast) 
apply (drule_tac x=xb in bspec,blast) 
apply (drule_tac x="insert l (La \<union> S xb)" in spec)
apply (clarsimp simp del: RMI_filter.simps)
apply (erule impE, blast)

apply clarsimp
apply (rule)
apply (force split: Value.splits )
apply (clarsimp split: split_if )
apply blast
apply clarsimp
apply (subgoal_tac "distinct (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran a)))")
apply (drule_tac SF=RMI_filter  and \<sigma>=\<sigma> and l = l and L = "La" and LS="{l}" in SF_fold_to_Union_what_F)
apply clarsimp
apply (drule_tac x=xb in bspec,blast) 
apply (rotate_tac -1,drule_tac x=xa in bspec,blast) 
apply clarsimp
apply (drule_tac x="insert l (La \<union> S xa)" in spec)
apply clarsimp 
apply (drule_tac x=xa in bspec,simp)
apply (intro conjI,simp)
apply (subgoal_tac "finite (\<Union>x\<in>ran a. Referenced_locations_Value x)")
apply (drule sorted_list_of_set)
apply blast
apply (rule finite_ran_obj_Referenced_locations_Value,simp)
apply blast
apply (subgoal_tac "\<exists> n <length (sorted_list_of_set(\<Union>x\<in>ran a. Referenced_locations_Value x)). (xa = (sorted_list_of_set(\<Union>x\<in>ran a. Referenced_locations_Value x)!n)) ")
apply clarsimp
apply (drule_tac x=n in spec)
apply clarsimp
apply (drule_tac x="(sorted_list_of_set(\<Union>x\<in>ran a. Referenced_locations_Value x)!n)" in bspec)
apply clarsimp
apply (clarsimp split: split_if_asm option.splits)
apply (case_tac x2a)
apply clarsimp

(*
apply (intro impI allI)
apply (drule_tac x="La \<union> {l}" in spec)
apply auto
done
*)

lemma equivalence_filters_1:
"\<forall> L'. ((serialization_filter l \<sigma> L)  \<subseteq> (RMI_filter l \<sigma> L') \<union> L \<union> L')"
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. \<forall> L'. (S  \<subseteq> (RMI_filter l'' \<sigma> L') \<union> L \<union> L')" in   serialization_filter_induct_1)
apply blast
apply (clarsimp split: Value.splits)
apply (clarsimp)
apply (case_tac "l\<in>L'")
apply (clarsimp)
apply (case_tac aa)
apply simp
apply (drule_tac x=xb in bspec)
apply blast
apply clarsimp
apply (elim disjE,clarsimp)
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


lemma "serialization_filter l \<sigma> L \<subseteq> dom \<sigma>"
apply (induct l \<sigma> L rule: serialization_filter.induct)
apply (auto split: option.splits Storable.splits simp: listunionMap_def)
apply (drule AuxiliaryFunctions.foldr_Un_mapD)
apply (auto split: split_if_asm option.splits Storable.splits)
apply (drule_tac x="(Obj(a,b))" in meta_spec,drule_tac x=a in meta_spec,drule_tac x=b in meta_spec,
  drule_tac x=y in meta_spec,simp)
apply (case_tac ya, case_tac prod)
apply (drule_tac x=ya in spec, clarsimp)
apply (erule disjE,force)
apply clarsimp
apply (drule subsetD,simp)
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

