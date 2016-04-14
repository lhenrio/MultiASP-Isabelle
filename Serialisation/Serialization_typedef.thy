(*  Title:      MultiASP.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       This is a second version of Serialization.thy to illustrate
                how the finite map typedef can be integrated. It is based
                on an old version of
                "Multi-active object formalisation"
                The change is that is uses a different type Store from
                StoreDefintion_typedef that integrate the finite map typedef.
                It only is adapted at the beginning for illustration on the
                effects of changes and is on an old version of Serialization.
                DOES NOT RUN THROUGH 
*)
theory Serialization_typedef imports StoreDefinition_typedef Main AuxiliaryFunctions begin
axiomatization where 
(*finite_map: "finite (dom (\<sigma>::Store))"
and *)
finite_obj: "V=Obj(f,C) \<Longrightarrow>finite (dom f)"

(* there is  a lemma now *)
thm finite_dom_Store
(* finite dom\<^sub>f ?\<sigma>\<Colon>nat \<rightharpoonup>\<^sub>f Storable *)

lemma ran_and_dom: "ran f = the`f`dom f  "
apply (auto simp: ran_def dom_def)
apply (subgoal_tac "x=the (f a) ")
apply blast
apply force
done

lemma finite_ran_obj:
"V=Obj(f,C) \<Longrightarrow>finite (ran f)"
apply (drule finite_obj)
apply (auto simp: ran_and_dom)
done


subsection {* serialization and location renaming *}

inductive serialize :: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
     "\<lbrakk>((\<sigma>'$ l) = (\<sigma>$ l)) \<and> ((\<sigma>$ l) = Some(Obj obj)) \<and> (\<forall> v\<in> ran(fst(obj)). (\<exists>\<sigma>''. (serialize v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>f \<sigma>')))
     \<rbrakk> \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" 
     |
    "\<lbrakk>((\<sigma>'$ l) = (\<sigma>$ l)) \<and> ((\<sigma>$ l) = Some (StoredVal v)) \<and> (serialize v \<sigma> \<sigma>') \<rbrakk>
     \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" 
     |
     "serialize (null) \<sigma> \<sigma>'" 
     (*|
         " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (FutRef f)  \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |
     "(serialize (ActRef f) \<sigma> \<sigma>')" |
     "serialize (ASPInt n) \<sigma> \<sigma>'" | 
     "serialize (ASPBool b) \<sigma> \<sigma>'"
*)

 definition Referenced_locations_Value:: "Value \<Rightarrow> Location set"
where  "Referenced_locations_Value v \<equiv> (case v of ObjRef l \<Rightarrow>{l} | _ \<Rightarrow> {})"

definition Referenced_locations_Location:: "Store \<Rightarrow>Location \<Rightarrow> Location set"
where  "Referenced_locations_Location \<sigma> l \<equiv> 
case (\<sigma>)\<^sub>f l of 
None \<Rightarrow>{} |
Some (Obj obj) \<Rightarrow> \<Union>(Referenced_locations_Value`ran(fst(obj))) |
Some (StoredVal (ObjRef l')) \<Rightarrow> {l'} |
_\<Rightarrow>{}
"

lemma Referenced_locations_Value_obj[simp]: "Referenced_locations_Value (ObjRef l) = {l}"
apply (auto simp: Referenced_locations_Value_def)
done
function (sequential) serialization_filter :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (serialization_filter l \<sigma> L) = (if l\<in>L then {} else
      (case (\<sigma>)\<^sub>f(l) of
      None \<Rightarrow>{} |
      Some (Obj obj) \<Rightarrow> {l}\<union>\<Union>( (\<lambda>x.(serialization_filter x \<sigma> (L\<union>{l}))) 
                `( (\<Union>(Referenced_locations_Value`ran(fst(obj)))))) |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (serialization_filter l' \<sigma> (L\<union>{l}))|
      _ \<Rightarrow> {l}))" 
by auto
termination 
apply (relation "measure (\<lambda>(l,\<sigma>,L). card (dom (\<sigma>)\<^sub>f - L))") 
  apply auto
 apply (subgoal_tac "dom (\<sigma>)\<^sub>f - insert l L = (dom (\<sigma>)\<^sub>f - L) - {l}") 
  apply (subgoal_tac "finite ((dom (\<sigma>)\<^sub>f-L))")
(*4*)
   apply (drule_tac x=l in Finite_Set.card.remove)+
    apply (insert finite_dom_Store)
sorry
    (*    
    apply auto
(*1*)
apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
 apply (subgoal_tac "finite ((dom \<sigma>-L))")
  apply (drule_tac x=l in Finite_Set.card.remove)+
   apply (insert finite_map)
   apply auto
done
*)


abbreviation serialize2:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
where
"serialize2 l \<sigma> \<equiv>  Abs_fmap((\<sigma>)\<^sub>f |` serialization_filter l \<sigma> {})" 

(*lemma set_sorted_list_of_set: "set (sorted_list_of_set S) = S"
apply (rule Finite_Set.finite.induct)
*)
lemma SFI1SG1: "(\<And>a b. l \<notin> L \<Longrightarrow>
               \<sigma>$ l = Some (Obj (a, b)) \<Longrightarrow>
               \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a). P (serialization_filter x \<sigma> (L \<union> {l})) x \<sigma> (L \<union> {l}) \<Longrightarrow>
               P ({l} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (L \<union> {l})) ` \<Union>(Referenced_locations_Value ` ran a))) l \<sigma> L) \<Longrightarrow>
       P {} l \<sigma> L \<Longrightarrow>
        (\<And>x2 prod x.
           l \<notin> L \<Longrightarrow>
           \<sigma>$ l = Some x2 \<Longrightarrow>
           x2 = Obj prod \<Longrightarrow>
           x \<in> \<Union>(Referenced_locations_Value ` ran (fst prod)) \<Longrightarrow> P (serialization_filter x \<sigma> (L \<union> {l})) x \<sigma> (L \<union> {l})) \<Longrightarrow>
        \<sigma>$ l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (serialization_filter l \<sigma> L) l \<sigma> L"
apply (case_tac prod)
apply clarsimp
apply blast
done

lemma  SFI1SG2:"(\<And>x2 Value nat.
           l \<notin> L \<Longrightarrow>
           \<sigma>$ l = Some x2 \<Longrightarrow>
           x2 = StoredVal Value \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> P (serialization_filter nat \<sigma> (L \<union> {l})) nat \<sigma> (L \<union> {l})) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma>$ l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (serialization_filter l' \<sigma> (L \<union> {l})) l' \<sigma> (L \<union> {l}) \<Longrightarrow> P ({l} \<union> serialization_filter l' \<sigma> (L \<union> {l})) l \<sigma> L) \<Longrightarrow>
  \<sigma>$ l = Some a \<Longrightarrow>  P {} l \<sigma> L\<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (serialization_filter l \<sigma> L) l \<sigma> L
  "
apply clarsimp
done

abbreviation isnotObjRef where "isnotObjRef V \<equiv>\<forall>l'. V\<noteq>ObjRef l'"

lemma serialization_filter_induct_1: "   
(\<And>l \<sigma> L. P {} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L V. l\<notin>L \<Longrightarrow>  \<sigma>$ l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L a b.
        l \<notin> L \<Longrightarrow> \<sigma>$ l = Some (Obj (a,b)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (serialization_filter x \<sigma> (L\<union>{l})) x \<sigma> (L\<union>{l})) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. serialization_filter x \<sigma> (L \<union> {l}))` \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L)  \<Longrightarrow>
(\<And>l \<sigma> L l'.
        l \<notin> L \<Longrightarrow> \<sigma>$ l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (serialization_filter l' \<sigma> (L\<union>{l})) l' \<sigma>  (L\<union>{l}))\<Longrightarrow>
           (P ({l}\<union>(serialization_filter l' \<sigma> (L\<union>{l}))) l \<sigma> L))         \<Longrightarrow>   
   P (serialization_filter l' \<sigma>' L') l' \<sigma>' L'"
apply (rule serialization_filter.induct)
apply (rotate_tac 1,drule_tac x=l in meta_spec)+
apply (rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+
apply (rotate_tac -1,drule_tac x=L in meta_spec)+
apply (case_tac "\<sigma>$ l")
(*2*)
 apply force
apply (case_tac a)
 apply (erule SFI1SG1,simp,simp,simp,simp)
apply (case_tac Value)
 apply force
apply (erule SFI1SG2,simp+)
done

lemma serialization_filter_induct_2: "   (\<And>l \<sigma> L. P {} ) \<Longrightarrow>
(\<And>l \<sigma> L V.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} ) \<Longrightarrow> 
(\<And>l \<sigma> L a b.
        l \<notin> L \<Longrightarrow> \<sigma>$ l = Some (Obj (a,b)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). P (serialization_filter x \<sigma> (L\<union>{l})) ) \<Longrightarrow>
           P ({l}\<union>(\<Union> ((\<lambda> x. serialization_filter x \<sigma> (L \<union> {l}))` \<Union>(Referenced_locations_Value`ran(a))))) )   \<Longrightarrow> 
(\<And>l \<sigma> L l'.
        l \<notin> L \<Longrightarrow> \<sigma>$ l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (serialization_filter l' \<sigma> (L\<union>{l})) )\<Longrightarrow>
           (P ({l}\<union>(serialization_filter l' \<sigma> (L\<union>{l}))))) 
  \<Longrightarrow>   
  
   P (serialization_filter l \<sigma> L) "
apply (insert  serialization_filter_induct_1 [of "(\<lambda> S l \<sigma> L. (P S))" ])
apply auto
done

lemma serialization_filter_subset: "serialization_filter l \<sigma> L \<subseteq> dom\<^sub>f \<sigma>"
apply (rule_tac P= "\<lambda> S l \<sigma> L. (S \<subseteq> dom\<^sub>f \<sigma>)" in   serialization_filter_induct_1)
   apply auto
apply (drule_tac x=xb in bspec)
 apply auto
apply (drule_tac x=xa in bspec)
 apply (auto split: option.splits )
done

lemma serialize_subset: "dom\<^sub>f (serialize2 l \<sigma>) \<subseteq> dom\<^sub>f \<sigma>"
apply (insert serialization_filter_subset)
apply (unfold dom_f_def)

apply (subgoal_tac "dom (serialize2 l \<sigma>)\<^sub>f \<subseteq> serialization_filter l \<sigma> {} ")
apply (drule_tac x = l in meta_spec)
apply (drule_tac x = \<sigma> in meta_spec)
apply (drule_tac x = "{}" in meta_spec)
apply simp
apply (fold dom_f_def)
apply simp
apply (rule subsetI)
apply (case_tac "\<sigma>$ l")
apply auto
(* up to here checked *)
done

lemma serialize_value: "(serialize2 l \<sigma>) l' = Some x \<Longrightarrow> \<sigma> l' = Some x"
apply (subgoal_tac "l'\<in>(serialization_filter l \<sigma> {})")
 apply (drule_tac m=\<sigma> in Map.restrict_in)
 apply force
apply (rule Map_restrict_Some,blast)
done

definition Well_Formed_Store where
"Well_Formed_Store \<sigma> \<equiv> \<forall> l\<in> dom \<sigma>. Referenced_locations_Location \<sigma> l\<subseteq>dom \<sigma>"


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
lemma Well_Formed_StoreD_obj: 
"\<sigma> la = Some (Obj (f, C)) \<Longrightarrow>  Well_Formed_Store \<sigma> \<Longrightarrow> f x = Some (ObjRef l) \<Longrightarrow>   l \<in> dom \<sigma>"
apply (auto simp: Well_Formed_Store_def )
done
lemma Well_Formed_StoreD_ref: 
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
(*
lemma SE_contradict: "La\<subseteq>L\<Longrightarrow> x \<in> (case \<sigma> xa of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {xa} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (insert l L \<union> {xa})) ` \<Union>(Referenced_locations_Value ` ran (fst obj)))
             | Some (StoredVal null) \<Rightarrow> {xa} | Some (StoredVal (ObjRef l')) \<Rightarrow> {xa} \<union> serialization_filter l' \<sigma> (insert l L \<union> {xa})) \<Longrightarrow>
       x \<notin> (case \<sigma> xa of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {xa} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (insert l La \<union> {xa})) ` \<Union>(Referenced_locations_Value ` ran (fst obj)))
             | Some (StoredVal null) \<Rightarrow> {xa} | Some (StoredVal (ObjRef l')) \<Rightarrow> {xa} \<union> serialization_filter l' \<sigma> (insert l La \<union> {xa})) \<Longrightarrow>
             False"
apply (erule contrapos_np)
apply (simp split:   option.splits )
apply (simp split: Storable.splits )
apply (clarsimp)
apply (subgoal_tac "xaa \<in> Referenced_locations_Value xaaa")
apply (drule_tac x=xaa in bspec)

(* STRANGE isabelle behaviour
apply (clarsimp,rename_tac F C l'' f)
apply (drule_tac x=l'' in bspec)
*)
apply force 
apply (case_tac "\<sigma> l''")
apply simp+
apply (case_tac a)
apply auto
*)
lemma Serialization_excluded_set: "\<forall> L . L\<subseteq>L' \<longrightarrow> serialization_filter l \<sigma> L' \<subseteq> serialization_filter l \<sigma> L"
apply (rule_tac P= "\<lambda> S l \<sigma> L'. (\<forall>L. L\<subseteq>L' \<longrightarrow> S \<subseteq> serialization_filter l \<sigma> L)" in   serialization_filter_induct_1)
apply clarsimp
apply (clarsimp split: Value.splits)
apply blast
apply clarsimp
apply rule
apply blast
apply clarsimp
apply (drule_tac x=xa in bspec,blast) 
apply (subgoal_tac "
    x \<in> (case \<sigma> xa of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {xa} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (insert l L \<union> {xa})) ` \<Union>(Referenced_locations_Value ` ran (fst obj)))
             | Some (StoredVal null) \<Rightarrow> {xa} | Some (StoredVal (ObjRef l')) \<Rightarrow> {xa} \<union> serialization_filter l' \<sigma> (insert l L \<union> {xa})) \<Longrightarrow>
       x \<notin> (case \<sigma> xa of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {xa} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (insert l La \<union> {xa})) ` \<Union>(Referenced_locations_Value ` ran (fst obj)))
             | Some (StoredVal null) \<Rightarrow> {xa} | Some (StoredVal (ObjRef l')) \<Rightarrow> {xa} \<union> serialization_filter l' \<sigma> (insert l La \<union> {xa})) \<Longrightarrow>
             False")
apply blast
apply (thin_tac ?P)
apply (thin_tac ?P)
apply (thin_tac ?P)
apply (thin_tac ?P)
apply (thin_tac ?P)
apply blast

apply (case_tac "\<sigma> xa")
apply simp
apply simp
apply (clarsimp split: Storable.splits )
 apply 

apply
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
(*
definition myfold where "myfold L l' \<sigma>  l refs F = (foldr (\<lambda>l' S. S\<union>(F l' \<sigma> S)) 
                (sorted_list_of_set (refs)) (L\<union>{l}))"*)
(*function (sequential) serialization_filter_2 :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (serialization_filter_2 l \<sigma> L) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      Some (Obj obj) \<Rightarrow> (fold (\<lambda>l' S. (if (L\<union>{l}\<subseteq>S) then (S\<union>(serialization_filter_2 l' \<sigma> S)) else {})) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) (L\<union>{l}))  |
      _ \<Rightarrow> {}))" 
by auto
termination serialization_filter_2
apply (relation "measure (\<lambda>(l,\<sigma>,L). card (dom \<sigma> - L))") 
apply auto
apply (subgoal_tac  "card (dom \<sigma> - xa) \<le>card (dom \<sigma> - insert l L)")
apply (subgoal_tac "dom \<sigma> - insert l L = (dom \<sigma> - L) - {l}") 
apply (subgoal_tac "finite ((dom \<sigma>-L))")
apply (drule_tac x=l in Finite_Set.card.remove)+
apply (insert finite_map)
apply auto
apply (subgoal_tac "dom \<sigma> - xa \<subseteq>(dom \<sigma> - insert l L)")
apply (subgoal_tac "dom \<sigma> - xa =(dom \<sigma> - insert l L)\<or>dom \<sigma> - xa \<subset>(dom \<sigma> - insert l L)")
apply (elim disjE)
apply force
apply (subgoal_tac "finite ((dom \<sigma>- insert l L))")
apply (drule_tac A="dom \<sigma>-xa" in Finite_Set.psubset_card_mono)
apply auto
done*)
function (sequential) serialization_filter_2 :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (serialization_filter_2 l \<sigma> L) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      None => {} |
      Some (Obj obj) \<Rightarrow> (fold (\<lambda>l' S.  (S\<union>(serialization_filter_2 l' \<sigma> (L\<union>{l}\<union>S))) ) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) ({l}))  |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (serialization_filter_2 l' \<sigma> (L\<union>{l}))|
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

lemma  finite_ran_obj_Referenced_locations_Value: "V=Obj(f,C) \<Longrightarrow>finite (\<Union>l'\<in>ran f. Referenced_locations_Value l')"
apply (drule finite_ran_obj)
apply (auto simp: Referenced_locations_Value_def split: Value.splits)
done

abbreviation serialize_RMI:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
where
"serialize_RMI l \<sigma> \<equiv>  \<sigma> |` serialization_filter_2 l \<sigma> {}" 

lemma SF_fold_to_Union[rule_format]: "\<forall>LS . ((distinct fieldlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S))) ) fieldlist (LS) 
      = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x)) `(set fieldlist)))))"
apply (induct_tac fieldlist)
apply auto
apply (drule_tac x= "(LS \<union> SF a \<sigma> (insert l (L \<union> LS)))" in spec,clarsimp)
apply (rule_tac x="F(a:= LS)" in exI)
apply (auto split: split_if_asm)
done
 
lemma SFI2SG1: "
   (\<And>a b S. l \<notin> L \<Longrightarrow>
                 \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
                 \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a).
                    P (serialization_filter_2 x \<sigma> (L \<union> {l} \<union> S x)) x \<sigma> (L \<union> {l} \<union> S x) \<Longrightarrow>
                 P ({l} \<union>
                    \<Union>((\<lambda>x. serialization_filter_2 x \<sigma> (L \<union> {l} \<union> S x)) `
                       \<Union>(Referenced_locations_Value ` ran a)))
                  l \<sigma> L) \<Longrightarrow>
       P {} l \<sigma> L \<Longrightarrow>
      (\<And>x2 prod x xa.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = Obj prod \<Longrightarrow>
           x \<in> set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
           P (serialization_filter_2 x \<sigma> (L \<union> {l} \<union> xa)) x \<sigma> (L \<union> {l} \<union> xa)) \<Longrightarrow>
        \<sigma> l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (serialization_filter_2 l \<sigma> L) l \<sigma> L"
apply (case_tac prod)
apply clarsimp
apply (subgoal_tac 
  "set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (a)))) = 
    \<Union>(Referenced_locations_Value ` ran (a))")
 apply clarsimp
(*2*)
 apply (drule_tac x=a in meta_spec)
 apply (rotate_tac -1, drule_tac x=b in meta_spec)
 apply simp
 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>(Referenced_locations_Value ` (ran (a)))))")
  apply (drule_tac SF=serialization_filter_2 and \<sigma> = \<sigma> and LS ="{l}" and l=l and L=L in SF_fold_to_Union,simp)
  apply clarsimp
(*3*)
  apply (drule_tac x=F in meta_spec)
  apply (drule_tac x="Obj (a,b)" in meta_spec)
  apply (drule_tac x=a in meta_spec)
  apply (drule_tac x=b in meta_spec)
  apply simp
  apply blast
(*3*)
 apply (subgoal_tac "finite (\<Union>l'\<in>ran a. Referenced_locations_Value l')")
  apply force
 apply (rule finite_ran_obj_Referenced_locations_Value)
 apply force
apply (subgoal_tac "finite (\<Union>l'\<in>ran (a). Referenced_locations_Value l')")
 apply force
apply (rule finite_ran_obj_Referenced_locations_Value)
apply force
done

lemma  SFI2SG2:"(\<And>x2 Value nat.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = StoredVal Value \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> 
           P (serialization_filter_2 nat \<sigma> (L \<union> {l})) nat \<sigma> (L \<union> {l})) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (serialization_filter_2 l' \<sigma> (L \<union> {l})) l' \<sigma> (L \<union> {l}) \<Longrightarrow>
              P ({l} \<union> serialization_filter_2 l' \<sigma> (L \<union> {l})) l \<sigma> L) \<Longrightarrow>
  \<sigma> l = Some a \<Longrightarrow>  P {} l \<sigma> L\<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (serialization_filter_2 l \<sigma> L) l \<sigma> L
  "
apply clarsimp
done

lemma serialization_filter_2_induct_1: "   
(\<And>l \<sigma> L. P {} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L V.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L a b S.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (serialization_filter_2 x \<sigma> (L\<union>{l}\<union>(S x))) x \<sigma> (L\<union>{l}\<union>(S x))) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. serialization_filter_2 x \<sigma> (L \<union> {l}\<union>S x))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L)  \<Longrightarrow>
(\<And>l \<sigma> L l'.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (serialization_filter_2 l' \<sigma> (L\<union>{l})) l' \<sigma>  (L\<union>{l}))\<Longrightarrow>
           (P ({l}\<union>(serialization_filter_2 l' \<sigma> (L\<union>{l}))) l \<sigma> L))         \<Longrightarrow>   
   P (serialization_filter_2 l' \<sigma>' L') l' \<sigma>' L'"
apply (rule serialization_filter_2.induct)
apply (rotate_tac 1,drule_tac x=l in meta_spec)+
apply (rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+
apply (rotate_tac -1,drule_tac x=L in meta_spec)+
apply (case_tac "\<sigma> l")
 apply simp
(*1*)
apply (case_tac a)
 apply (erule SFI2SG1,simp,simp,simp,simp)
apply (case_tac Value)
 apply force

apply (erule SFI2SG2,simp+)
done

lemma equivalence_filters_1:
"\<forall> L'. ((serialization_filter l \<sigma> L)  \<subseteq> (serialization_filter_2 l \<sigma> L') \<union> L \<union> L')"
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. \<forall> L'. (S  \<subseteq> (serialization_filter_2 l'' \<sigma> L') \<union> L \<union> L')" in   serialization_filter_induct_1)
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

