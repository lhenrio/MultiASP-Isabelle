(*  Title:      MultiASP.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       Multi-active object formalisation
                For the moment methods and parameter bindings are done statically, 
                  without inheritance but with interfaces
                  this could be improved
*)
theory Serialization imports StoreDefinition Main AuxiliaryFunctions begin
section{*References, Well-formed store, finite objects*}
(*lemma map_restrict_id: "\<sigma> x = None \<Longrightarrow>(\<sigma>|` L) x = None"
apply (unfold restrict_map_def)
apply auto
  *)       

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
(*Set of locations referenced from a location (non-recursive))*)
where  "Referenced_locations_Location \<sigma> l \<equiv> 
case \<sigma> l of 
None \<Rightarrow>{} |
Some (Obj obj) \<Rightarrow> \<Union>(Referenced_locations_Value`ran(fst(obj))) |
Some (StoredVal (ObjRef l')) \<Rightarrow> {l'} |
_\<Rightarrow>{}
"

lemma  finite_ran_obj_Referenced_locations_Value: "V=Obj(f,C) \<Longrightarrow>finite (\<Union>l'\<in>ran f. Referenced_locations_Value l')"
apply (drule finite_ran_obj)
apply (auto simp: Referenced_locations_Value_def split: Value.splits)
done

definition Well_Formed_Store where
"Well_Formed_Store \<sigma> \<equiv> \<forall> l\<in> dom \<sigma>. Referenced_locations_Location \<sigma> l\<subseteq>dom \<sigma>"


subsection{*generic lemmas on folding (for Mark serialization)*}

lemma SF_fold_to_Union[rule_format]: "\<forall>LS . ((distinct fieldlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) )) ) fieldlist (LS) 
      = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x) ) `(set fieldlist)))))"
apply (induct_tac fieldlist)
apply auto
apply (drule_tac x= "(LS \<union> SF a \<sigma> (insert l (L \<union> LS)) )" in spec,clarsimp)
apply (rule_tac x="F(a:= LS)" in exI)
apply (auto split: split_if_asm)
done

lemma SF_fold_to_Union_what_F[rule_format]: "\<forall>LS . ((distinct fieldlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) )) ) fieldlist (LS) 
      = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x) ) `(set fieldlist)) \<and> 
  (\<forall> n <length fieldlist. \<forall> l'\<in>F (fieldlist!n). l'\<in>LS \<or> (\<exists> n'<n . (l'\<in>SF (fieldlist!n') \<sigma> (L\<union>{l}\<union>F (fieldlist!n')) )) ))))"
apply (induct_tac fieldlist)
 apply auto
apply (drule_tac x= "(LS \<union> SF a \<sigma> (insert l (L \<union> LS)) )" in spec,clarsimp)
apply (rule_tac x="F(a:= LS)" in exI)
apply (auto split: split_if_asm)
apply (case_tac n)
(*2*)
 apply clarsimp+
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
 apply force
apply auto
apply (case_tac x,auto)
done

lemma SF_fold_to_Union_what_F2[rule_format]: "\<forall>LS . ((distinct locationlist)\<longrightarrow>(\<exists> F .
 (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) )) ) locationlist (LS) 
      = LS\<union> \<Union>((\<lambda> n . SF (locationlist!n) \<sigma> (L\<union>{l}\<union>F n) ) `{n'. n'<length locationlist}) \<and> 
(F = (\<lambda>n. if n < length locationlist then 
                  (fold (\<lambda>l' S.  (S\<union>(SF l' \<sigma> (L\<union>{l}\<union>S) )) ) 
                                        (take n locationlist) (LS)) else {})))))"
apply (induct_tac locationlist)
apply auto
apply (case_tac xa)
apply auto
done

subsection{*Properties on locations and stores*}

lemma Referenced_locations_Value_obj[simp]: "Referenced_locations_Value (ObjRef l) = {l}"
apply (auto simp: Referenced_locations_Value_def)
done



lemma Referenced_locations_LocationI_Obj[intro]:
"\<sigma> l = Some (Obj (a, b)) \<Longrightarrow> a x = Some (ObjRef l') \<Longrightarrow> l'\<in> Referenced_locations_Location \<sigma> l"
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


subsection {* serialization and location renaming *}

coinductive serialize :: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
(*serialize v \<sigma> \<sigma>' is true if all the references pointed recursively by v are in sigma' 
(v refers originally to location in sigma and sigma'should be a subset of sigma) 
NB: one should expect that the serialization of value v is a subset of \<sigma>' (using store \<sigma>)
but in practice there is no rule for the non-accessible part of the store*)
  where
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ran(fst(obj)). \<exists>\<sigma>''. (serialize v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
     \<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |

    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (StoredVal v) \<and>  (serialize v \<sigma> \<sigma>')\<Longrightarrow> (serialize (ObjRef l) \<sigma> \<sigma>')" |

     "serialize (null) \<sigma> \<sigma>' " 

(*lemma serialize_composable_inductive_proof:     
"serialize v \<sigma> \<sigma>' \<Longrightarrow> (\<forall> v \<sigma> \<sigma>'. serialize v \<sigma> \<sigma>' \<longrightarrow> Q v \<sigma> \<sigma>') \<Longrightarrow>
    (\<And>\<sigma>' l \<sigma> obj.
        \<sigma>' l = \<sigma> l \<and> \<sigma> l = Some (Obj obj) \<and> 
          (\<forall>v\<in>ran (fst obj). \<exists>\<sigma>''. (serialize v \<sigma> \<sigma>'' \<and> P v \<sigma> \<sigma>''\<and> Q v \<sigma> \<sigma>'') \<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>') 
              \<Longrightarrow> P (ObjRef l) \<sigma> \<sigma>') \<Longrightarrow>
    (\<And>\<sigma>' l \<sigma> v. \<sigma>' l = \<sigma> l \<and> \<sigma> l = Some (StoredVal v) \<and> serialize v \<sigma> \<sigma>' \<and> P v \<sigma> \<sigma>'\<and> Q v \<sigma> \<sigma>' 
              \<Longrightarrow> P (ObjRef l) \<sigma> \<sigma>') \<Longrightarrow>
    (\<And>\<sigma> \<sigma>'. P null \<sigma> \<sigma>'\<and> Q null \<sigma> \<sigma>') \<Longrightarrow> P  v \<sigma> \<sigma>'"
apply (erule serialize.induct,auto)
 apply (subgoal_tac " (\<forall>v\<in>ran a. \<exists>\<sigma>''. serialize v \<sigma> \<sigma>'' \<and> P v \<sigma> \<sigma>'' \<and> Q v \<sigma> \<sigma>'' \<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>' )")
  apply auto
 apply (drule_tac x=v  in bspec,auto)
apply (subgoal_tac " serialize v \<sigma> \<sigma>' \<and> P v \<sigma> \<sigma>' \<and> Q v \<sigma> \<sigma>'")
 apply auto
done
*)



section{* a weaker serialize (for non-WF stores)*}
(* serialize_weak l \<sigma> \<sigma>' does not constraint \<sigma>' if l points to none 
it will be useful to define more easily properties on the serialisation, especially to reason by recurrence *)
coinductive serialize_weak :: "Value \<Rightarrow> Store \<Rightarrow> Store \<Rightarrow> bool"
  where
    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ran(fst(obj)). \<exists>\<sigma>''. (serialize_weak v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
     \<Longrightarrow> (serialize_weak (ObjRef l) \<sigma> \<sigma>')" |

    " \<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (StoredVal v) \<and>  (serialize_weak v \<sigma> \<sigma>')\<Longrightarrow> (serialize_weak (ObjRef l) \<sigma> \<sigma>')" |

     "serialize_weak (null) \<sigma> \<sigma>' " |

(*New : *)
    " \<sigma>(l) =None \<Longrightarrow> (serialize_weak (ObjRef l) \<sigma> \<sigma>')" 

section{*serialize lemmas*}

lemma format_conj: "(P\<and>Q\<longrightarrow>R) \<Longrightarrow> (P\<Longrightarrow>Q\<Longrightarrow>R)"
by simp


lemma serialize_substore_result[THEN format_conj,rule_format]: " serialize v \<sigma> \<sigma>' \<and>\<sigma>'\<subseteq>\<^sub>m  \<sigma>''\<longrightarrow>  serialize v \<sigma> \<sigma>''"
apply (intro impI)
apply (erule serialize.coinduct)
apply clarsimp
apply (erule serialize.cases)
apply auto
(*4*)
   apply (force simp: map_le_def)
  apply (clarsimp simp: map_le_def)
  apply (drule_tac x=v in bspec)
   apply force
  apply force
(*2*)
 apply (rotate_tac -1, erule contrapos_pp,clarsimp)
  apply (drule_tac x=v in bspec)
  apply force
 apply clarsimp
 apply (rule_tac x=\<sigma>'' in exI)
 apply clarsimp
 apply (erule map_le_trans,simp)
apply (force simp: map_le_def)
done

lemma serialize_weak_substore_result[THEN format_conj]: " (serialize_weak v \<sigma> \<sigma>' \<and>\<sigma>'\<subseteq>\<^sub>m  \<sigma>'')\<longrightarrow>  serialize_weak v \<sigma> \<sigma>''"
apply (intro impI)
apply (erule serialize_weak.coinduct)
apply clarsimp
apply (erule serialize_weak.cases)
apply auto
(*4*)
   apply (force simp: map_le_def)
  apply (clarsimp simp: map_le_def)
  apply (drule_tac x=v in bspec)
   apply force
  apply force
(*2*)
 apply (rotate_tac -1, erule contrapos_pp,clarsimp)
  apply (drule_tac x=v in bspec)
  apply force
 apply clarsimp
 apply (rule_tac x=\<sigma>'' in exI)
 apply clarsimp
 apply (erule map_le_trans,simp)
apply (force simp: map_le_def)
done

lemma serialize_value: "serialize (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow> \<sigma>' l = \<sigma> l"
apply (erule serialize.cases)
apply auto
done
lemma serialize_weak_value: "serialize_weak (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow>l\<in>dom \<sigma>\<Longrightarrow> \<sigma>' l = \<sigma> l"
apply (erule serialize_weak.cases)
apply auto
done


lemma serialize_weak_substore[THEN format_conj]: " (serialize_weak v \<sigma> \<sigma>' \<and>\<sigma>''\<subseteq>\<^sub>m  \<sigma> ) \<longrightarrow>  serialize_weak v \<sigma>'' \<sigma>'"
apply (intro impI)
apply (erule serialize_weak.coinduct)
apply (case_tac x)
 apply clarsimp
 apply (case_tac "x2\<in>dom xa")
  apply (subgoal_tac "xb x2 = \<sigma> x2")
  apply (elim conjE)
(*6*)
     apply (erule serialize_weak.cases)
     apply (clarsimp simp: map_le_def)
     apply (auto simp: map_le_def)
(*1*)
apply (rule serialize_weak_value)
 apply (auto simp: map_le_def)
  apply force
done


lemma serialize_weak_weaker_intro_pre:
  " vv=ObjRef l \<and>\<sigma>'(l) = \<sigma>(l) \<and> \<sigma>(l) = Some (Obj obj) \<and> (\<forall> v\<in> ((ran(fst(obj)) - {ObjRef l})). \<exists>\<sigma>''. (serialize_weak v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
    \<Longrightarrow> (serialize_weak vv \<sigma> \<sigma>')"
apply (erule serialize_weak.coinduct) 
apply (case_tac obj,clarsimp)
apply (case_tac "v=ObjRef l")
 apply (rule_tac x= xb in exI,clarsimp+)
done

(*no need to iter on self reference when checking serialize(weak) *)
lemma serialize_weak_weaker_intro:
" \<sigma>(l) = Some (Obj obj) \<Longrightarrow> \<sigma>'(l) = \<sigma>(l) \<Longrightarrow> (\<forall> v\<in> ((ran(fst(obj)) - {ObjRef l})). \<exists>\<sigma>''. (serialize_weak v \<sigma> \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>'))
    \<Longrightarrow> (serialize_weak (ObjRef l) \<sigma> \<sigma>')"
by (rule serialize_weak_weaker_intro_pre,auto)



lemma serialize_weak_remove_1_unreferenced_pre: 
"(l\<in>dom \<sigma>\<and>serialize_weak v (\<sigma>|` (-{l})) \<sigma>' \<and>(\<exists> \<sigma>''. serialize_weak v \<sigma> \<sigma>''\<and> l\<notin>dom \<sigma>''))\<Longrightarrow>  serialize_weak v \<sigma> \<sigma>'"
apply (erule serialize_weak.coinduct)
apply (case_tac x)
apply clarsimp
apply (elim conjE)
apply (case_tac "x2=l")
(*2 easy when l=x2 *)
 apply (elim exE conjE,simp)
 apply (drule serialize_weak_value,assumption)
 apply clarsimp
(*1*)
apply (elim exE conjE,simp)
apply (case_tac "x2\<in>dom xa")
(*2 we eliminate the case x2 in dom xa *)
defer
apply force
apply (case_tac "xa x2")
 apply force
apply (case_tac a)
 apply (case_tac x1)
 apply simp
 apply (frule serialize_weak_value)
  apply clarsimp
 apply (intro conjI)
  apply force
(*2*)
 apply (intro ballI)
 apply (erule serialize_weak.cases,simp+)
    apply (erule serialize_weak.cases,simp+)
(*8*)
       apply (elim conjE exE)
       apply (drule_tac x=v in bspec, assumption)
       apply (drule_tac x=v in bspec, force)
       apply (elim conjE exE)
       apply (rule_tac x=\<sigma>'''''' in exI)
       apply simp
       apply (intro disjI1)
       apply (rule_tac x=\<sigma>''' in exI)
       apply simp
       apply (rule serialize_weak_substore_result)
(*10*)
         apply force
        apply simp+
(*4*)
   apply force
  apply force
 apply force
apply simp
apply (erule serialize_weak.cases)
   apply auto
apply (erule serialize_weak.cases)
   apply auto
done

lemma serialize_weak_remove_1_unreferenced: 
"serialize_weak v (\<sigma>|` (-{l})) \<sigma>' \<Longrightarrow>(\<exists> \<sigma>''. serialize_weak v \<sigma> \<sigma>''\<and> l\<notin>dom \<sigma>'')\<Longrightarrow>  serialize_weak v \<sigma> \<sigma>'"
apply (case_tac "l\<in>dom \<sigma>")
apply (rule serialize_weak_remove_1_unreferenced_pre)
apply auto
apply (subgoal_tac "(\<sigma> |` (- {l})) = \<sigma>")
apply (auto simp: restrict_map_def)
done

lemma serialize_weak_remove_1_referenced_pre: 
"l\<in>dom \<sigma>\<and>serialize_weak v (\<sigma>|` (-{l})) \<sigma>' \<and> serialize_weak (ObjRef l) \<sigma> \<sigma>''\<and>\<sigma>'\<subseteq>\<^sub>m  \<sigma>1\<and>\<sigma>''\<subseteq>\<^sub>m  \<sigma>1
        \<Longrightarrow>  serialize_weak v \<sigma> \<sigma>1"
apply (erule serialize_weak.coinduct)
apply (case_tac x)
apply clarsimp
apply (elim conjE)
apply (case_tac "x2=l")
(*2 when l=x2 *)
 apply (frule serialize_weak_value,assumption)
 apply (simp add: map_le_def)
 apply (frule_tac x=l in bspec)
 back
  apply force
 apply simp
 apply (case_tac "xa l")
  apply (erule serialize_weak.cases,simp+)
 apply (case_tac a)
  apply (erule serialize_weak.cases,simp+)
(*6*)
     apply force
    apply force
   apply force
  apply (erule serialize_weak.cases,simp+)
(*6*)
     apply clarsimp
     apply (drule_tac x=v in bspec, assumption)
     apply clarsimp
     apply (rule_tac x=\<sigma>'''' in exI)
     apply (force simp: map_le_def)
    apply force
   apply force
  apply force
 apply (erule serialize_weak.cases,simp+)
(*5*)
    apply clarsimp
   apply force
  apply force
 apply (rule disjI2)
 apply simp
 apply (erule serialize_weak.cases,simp+)
(*4*)
   apply (rule disjI2)
   apply (rule serialize_weak_substore_result,simp+)
    apply force
   apply (force simp: map_le_def)
  apply force
 apply force

(*1*)
apply (case_tac "x2\<in>dom xa")
(*2 we eliminate the case x2 in dom xa *)
defer
apply force
(*1 else*)
apply (case_tac "xa x2")
 apply force
apply (case_tac a)
 apply (case_tac x1)
 apply simp
 apply (frule serialize_weak_value)
  apply clarsimp
 apply (intro conjI)
  apply (force simp: map_le_def)
(*2*)
 apply (intro ballI)
 apply (erule serialize_weak.cases,simp+)
    apply (erule serialize_weak.cases,simp+)
(*8*)
       apply (elim conjE exE)
       apply (drule_tac x=v in bspec, force)
       apply (elim conjE exE)
       apply (rule_tac x=xb in exI)
       apply (intro conjI)       
        apply (intro disjI1)
        apply (intro conjI)       
(*11*)
          apply (rule serialize_weak_substore_result,force,assumption)
          apply force
         apply (force simp: map_le_def)
        apply (force simp: map_le_def)
       apply simp+
      apply clarsimp
      apply (drule_tac x=v in bspec, assumption)
      apply clarsimp
      apply (rule_tac x=xb in exI)
      apply (intro conjI)       
       apply (intro disjI1)
       apply (intro conjI)       
(*10*)
         apply (rule serialize_weak_substore_result,force,assumption,simp)
         apply clarsimp+

(*1*)
apply (erule serialize_weak.cases)
   apply auto
apply (erule serialize_weak.cases)
   apply (auto)
 apply (force  simp: map_le_def)
apply (force  simp: map_le_def)
done

lemma serialize_weak_remove_1_referenced: 
"serialize_weak v (\<sigma>|` (-{l})) \<sigma>' \<Longrightarrow> serialize_weak (ObjRef l) \<sigma> \<sigma>''\<Longrightarrow>\<sigma>'\<subseteq>\<^sub>m  \<sigma>'''\<Longrightarrow>\<sigma>''\<subseteq>\<^sub>m  \<sigma>'''
        \<Longrightarrow>  serialize_weak v \<sigma> \<sigma>'''"
apply (case_tac "l\<in>dom \<sigma>")
apply (rule serialize_weak_remove_1_referenced_pre,simp)
apply (subgoal_tac "(\<sigma> |` (- {l})) = \<sigma>",simp)
apply (rule serialize_weak_substore_result)
apply (auto simp: restrict_map_def)
done

lemma serialize_weak_remove_one_obj_pre: 
"\<sigma> l = Some (Obj obj)\<and>serialize_weak v (\<sigma>|` (-{l})) \<sigma>' \<and> \<sigma>l\<subseteq>\<^sub>m  \<sigma>' \<and>
(\<forall> v\<in> ((ran(fst(obj)) - {ObjRef l})). \<exists>\<sigma>''. (serialize_weak v (\<sigma>|` (-{l})) \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>l)) \<and>\<sigma>l l = Some (Obj obj)
        \<Longrightarrow>  serialize_weak v \<sigma> \<sigma>'"
apply (erule serialize_weak.coinduct)
apply (case_tac x)
 apply clarsimp
apply (elim conjE)
apply (case_tac "x2=l")
(*2 when l=x2 *)
 apply (clarsimp simp: map_le_def)
 apply (intro conjI,force)
 apply (case_tac obj,clarsimp)
 apply (case_tac "v=ObjRef l")
  apply clarsimp
  apply (rule_tac x=xb in exI)
  apply force
 apply (frule_tac x=v in bspec)
  apply force
 apply (elim exE conjE)
 apply (rule_tac x=\<sigma>l in exI)
 apply (intro conjI disjI1)
   apply (rule serialize_weak_substore_result,simp+)
   apply (clarsimp simp: map_le_def)
   apply (clarsimp simp: map_le_def)
   apply (clarsimp simp: map_le_def)

(*1*)
apply (case_tac "x2\<in>dom xa")
(*2 we eliminate the case x2 in dom xa *)
defer
apply force
(*1 else*)
apply (case_tac "xa x2")
 apply force
apply (case_tac a)
 apply (case_tac x1)
 apply simp
 apply (frule serialize_weak_value)
  apply clarsimp
 apply (intro conjI)
  apply (clarsimp simp: map_le_def)
(*2*)
 apply (intro ballI)
 apply (erule serialize_weak.cases,simp+)
(*5*)
    apply (elim conjE exE)
    apply (drule_tac x=v in bspec, force)
    apply (elim conjE exE)
    apply (rule_tac x=xb in exI)
    apply (intro conjI)       
     apply (intro disjI1)
     apply (intro conjI)
(*7*)
      apply (rule serialize_weak_substore_result,force,force)
     apply clarsimp+

(*1*)
apply (erule serialize_weak.cases)
   apply auto
done

lemma serialize_weak_remove_one_obj:
" \<sigma>l l = Some (Obj obj)
        \<Longrightarrow>\<sigma> l = Some (Obj obj) 
        \<Longrightarrow>  serialize_weak v (\<sigma>|` (-{l})) \<sigma>'' 
        \<Longrightarrow> \<sigma>''\<subseteq>\<^sub>m\<sigma>' 
        \<Longrightarrow> \<sigma>l\<subseteq>\<^sub>m  \<sigma>' 
        \<Longrightarrow> (\<forall> v\<in> ((ran(fst(obj)) - {ObjRef l})). \<exists>\<sigma>''. (serialize_weak v (\<sigma>|` (-{l})) \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>l)) 
            \<Longrightarrow> serialize_weak v \<sigma> \<sigma>'"
apply (rule_tac \<sigma>l=\<sigma>l in serialize_weak_remove_one_obj_pre,(intro conjI,simp)+)
apply (rule serialize_weak_substore_result)
by auto

lemma serialize_weak_serialize_one_obj:
" \<sigma>l l = Some (Obj obj)
  \<Longrightarrow>\<sigma> l = Some (Obj obj) 
  \<Longrightarrow> (\<forall> v\<in> ((ran(fst(obj)) - {ObjRef l})). \<exists>\<sigma>''. (serialize_weak v (\<sigma>|` (-{l})) \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>l)) 
      \<Longrightarrow> serialize_weak (ObjRef l) \<sigma> \<sigma>l"
apply (rule_tac obj=obj in serialize_weak_weaker_intro,simp+)
apply (intro ballI conjI)
apply (rule_tac x=\<sigma>l in exI)
apply clarsimp
apply (frule_tac x=v in bspec,force)
apply (elim exE conjE)
apply (rule_tac \<sigma>l=\<sigma>l in serialize_weak_remove_one_obj,simp+)
done

lemma serialize_weak_serialize_one_self_ref_pre:
" v= ObjRef l \<and>\<sigma> l = Some (StoredVal (ObjRef l)) \<and> \<sigma>' l = \<sigma> l \<and> \<sigma> l = Some (StoredVal (ObjRef l)) \<Longrightarrow>  serialize_weak v \<sigma>  \<sigma>'"
by (erule serialize_weak.coinduct, auto)

lemma serialize_weak_serialize_one_self_ref:
"\<sigma> l = Some (StoredVal (ObjRef l)) 
  \<Longrightarrow> \<sigma>' l = \<sigma> l 
  \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l)) 
        \<Longrightarrow>  serialize_weak (ObjRef l) \<sigma>  \<sigma>'"
by (rule serialize_weak_serialize_one_self_ref_pre, auto)


lemma serialize_weak_remove_one_ref_pre: 
"\<sigma> l = Some (StoredVal (ObjRef l'))\<and>serialize_weak v (\<sigma>|` (-{l})) \<sigma>' \<and> \<sigma>l\<subseteq>\<^sub>m  \<sigma>' \<and>
 serialize_weak (ObjRef l') (\<sigma>|` (-{l})) \<sigma>''\<and> \<sigma>'' \<subseteq>\<^sub>m \<sigma>l \<and>\<sigma>l l = Some (StoredVal (ObjRef l'))
        \<Longrightarrow>  serialize_weak v \<sigma> \<sigma>'"
apply (erule serialize_weak.coinduct)
apply (case_tac x)
 apply clarsimp
apply (elim conjE)
apply (case_tac "x2=l")
(*2 when l=x2 *)
 apply (clarsimp simp: map_le_def)
 apply (intro conjI,force)
 apply (intro conjI disjI1)
   apply (rule_tac \<sigma>'1=\<sigma>'' in serialize_weak_substore_result)
    apply assumption
   apply (force simp: map_le_def)

(*1 the rest is similar to the obj case*)
apply (case_tac "x2\<in>dom xa")
(*2 we eliminate the case x2 in dom xa *)
defer
apply force
(*1 else*)
apply (case_tac "xa x2")
 apply force
apply (case_tac a)
 apply (case_tac x1)
 apply simp
 apply (frule serialize_weak_value)
  apply clarsimp
 apply (intro conjI)
  apply (clarsimp simp: map_le_def)
(*2*)
 apply (intro ballI)
 apply (erule serialize_weak.cases,simp+)
(*5*)
    apply (elim conjE exE)
    apply (drule_tac x=v in bspec, force)
    apply (elim conjE exE)
    apply (rule_tac x=xb in exI)
    apply (intro conjI)       
     apply (intro disjI1)
     apply (intro conjI)
(*7*)
      apply (rule serialize_weak_substore_result,force,force)
     apply clarsimp+

(*1*)
apply (erule serialize_weak.cases)
   apply auto
done

lemma serialize_weak_remove_one_ref:
" \<sigma>l l = Some (StoredVal (ObjRef l'))
      \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) 
      \<Longrightarrow> serialize_weak v (\<sigma>|` (-{l})) \<sigma>'' 
      \<Longrightarrow> \<sigma>''\<subseteq>\<^sub>m\<sigma>' \<Longrightarrow> \<sigma>l\<subseteq>\<^sub>m  \<sigma>' 
      \<Longrightarrow>serialize_weak (ObjRef l') (\<sigma> |` (- {l})) \<sigma>l 
            \<Longrightarrow> serialize_weak v \<sigma> \<sigma>'"
apply (rule_tac \<sigma>l=\<sigma>l in serialize_weak_remove_one_ref_pre,(intro conjI,simp)+)
apply (rule serialize_weak_substore_result)
by auto


lemma serialize_weak_serialize_one_ref:
" \<sigma>l l = Some (StoredVal (ObjRef l'))  \<Longrightarrow> 
  \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
 serialize_weak (ObjRef l') (\<sigma>|` (-{l}))  \<sigma>l \<Longrightarrow>
 serialize_weak (ObjRef l) \<sigma> \<sigma>l"
apply (rule_tac v="ObjRef l'" in serialize_weak.intros(2),auto)
apply (rule_tac \<sigma>l=\<sigma>l and \<sigma>''=\<sigma>l in serialize_weak_remove_one_ref,simp+)
done

lemma serialize_weak_serialize_pre: 
"Well_Formed_Store \<sigma> \<and>(Referenced_locations_Value v) \<subseteq> (dom \<sigma>)\<and> serialize_weak v \<sigma> \<sigma>'
 \<Longrightarrow> serialize v \<sigma> \<sigma>' "
apply (erule serialize.coinduct)
apply (case_tac x)
apply force

apply (simp add: Referenced_locations_Value_def)
apply (elim conjE)
apply (case_tac "xa x2")
apply force
apply (case_tac a)
apply (case_tac x1)
 apply (erule serialize_weak.cases,simp+)
 apply clarsimp
 apply (case_tac v,force)
 apply (drule_tac x=v in bspec,force,clarsimp)
 apply (rule_tac x=\<sigma>'' in exI)
 apply (intro conjI disjI1)
 apply (simp add: ran_def)
 apply (elim exE)
 apply (erule Well_Formed_StoreD_obj,simp+)

 apply (erule serialize_weak.cases,simp+)
 apply (case_tac x2a,force,simp)
 apply (rule disjI1)
 apply (rule Well_Formed_StoreD_ref)
 apply auto
done

theorem serialize_weak_serialize: 
"Well_Formed_Store \<sigma> 
  \<Longrightarrow>(Referenced_locations_Value v) \<subseteq> (dom \<sigma>) 
  \<Longrightarrow> serialize_weak v \<sigma> \<sigma>'
 \<Longrightarrow> serialize v \<sigma> \<sigma>' "
by (rule serialize_weak_serialize_pre,auto)

section {* serialization filter*}

function (sequential) serialization_filter :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialization_filter v \<sigma> L  is the set of locations that are recursively referenced by the value v
  locations in L are EXCLUDED from the set (to prevent non-termination in case of reference loop) *)
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

abbreviation serialize_filter:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
(* a second definition of serialisation based on the serialisation filter: 
sigma' is exactly the store captured by the algorithm (the smallest necessary sub-store *)
where
"serialize_filter l \<sigma> \<equiv>  \<sigma> |` serialization_filter l \<sigma> {}" 

(* intermediary lemma for serialization_filter1*)
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
(* intermediary lemma for serialization_filter1 and 1B*)
lemma  SFI1SG2:"(\<And>x2 v nat.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = StoredVal v \<Longrightarrow> v = ObjRef nat \<Longrightarrow> P (serialization_filter nat \<sigma> (L \<union> {l})) nat \<sigma> (L \<union> {l})) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (serialization_filter l' \<sigma> (L \<union> {l})) l' \<sigma> (L \<union> {l}) \<Longrightarrow> P ({l} \<union> serialization_filter l' \<sigma> (L \<union> {l})) l \<sigma> L) \<Longrightarrow>
  \<sigma> l = Some a \<Longrightarrow>  ((\<sigma> l=None \<or>l\<in>L)\<longrightarrow>P {} l \<sigma> L)\<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (serialization_filter l \<sigma> L) l \<sigma> L
  "
apply clarsimp
done

(* INDUCTION PRINCIPLES on Filtering 
1 - is with an additional variable for the induction set (often useful)
1B - the same as 1 but weaker on the recurrence hypothesis taking into acccount that the current loc l is filtered
2 - is the most natural one
*)
lemma serialization_filter1: "   
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

(* intermediary lemma for serialization_filter1B*)
lemma SFI1SG1B: "(\<And>a b. l \<notin> L \<Longrightarrow>
               \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
               \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a)-{l}. P (serialization_filter x \<sigma> (L \<union> {l})) x \<sigma> (L \<union> {l}) \<Longrightarrow>
               P ({l} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (L \<union> {l})) ` (\<Union>(Referenced_locations_Value ` ran a)-{l}))) l \<sigma> L) \<Longrightarrow>
       (\<And>l \<sigma> L.(\<sigma> l=None \<or>l\<in>L)\<longrightarrow>P {} l \<sigma> L) \<Longrightarrow>
        (\<And>x2 prod x.
           l \<notin> L \<Longrightarrow>
           \<sigma> l = Some x2 \<Longrightarrow>
           x2 = Obj prod \<Longrightarrow>
           x \<in> \<Union>(Referenced_locations_Value ` ran (fst prod))-{l} \<Longrightarrow> P (serialization_filter x \<sigma> (L \<union> {l})) x \<sigma> (L \<union> {l})) \<Longrightarrow>
        \<sigma> l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (serialization_filter l \<sigma> L) l \<sigma> L"
apply (case_tac prod)
apply clarsimp
apply (subgoal_tac "(insert l (\<Union>x\<in>((\<Union>x\<in>ran aa. Referenced_locations_Value x) - {l}) \<inter> {x. x \<noteq> l \<and> x \<notin> L}.
                                     case \<sigma> x of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {x} \<union> \<Union>((\<lambda>xa. serialization_filter xa \<sigma> (insert l L \<union> {x})) ` \<Union>(Referenced_locations_Value ` ran (fst obj))) | Some (StoredVal null) \<Rightarrow> {x}
                                     | Some (StoredVal (ObjRef l')) \<Rightarrow> {x} \<union> serialization_filter l' \<sigma> (insert l L \<union> {x})))
 =
(insert l (\<Union>x\<in>(\<Union>x\<in>ran aa. Referenced_locations_Value x) \<inter> {x. x \<noteq> l \<and> x \<notin> L}.
                                       case \<sigma> x of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {x} \<union> \<Union>((\<lambda>xa. serialization_filter xa \<sigma> (insert l L \<union> {x})) ` \<Union>(Referenced_locations_Value ` ran (fst obj))) | Some (StoredVal null) \<Rightarrow> {x}
                                       | Some (StoredVal (ObjRef l')) \<Rightarrow> {x} \<union> serialization_filter l' \<sigma> (insert l L \<union> {x})))")
defer
apply blast
apply (subgoal_tac 
    "\<And>A. ((A - {l}) \<inter> {x. x \<noteq> l \<and> x \<notin> L}) = (A \<inter> {x. x \<noteq> l \<and> x \<notin> L})")
apply auto
done

lemma serialization_filter1B: "   
(\<And>l \<sigma> L. (\<sigma> l=None\<or>l\<in>L) \<longrightarrow> P {} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L V. l\<notin>L \<Longrightarrow>  \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L) \<Longrightarrow> 
(\<And>l \<sigma> L f C.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (f,C)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran f))-{l}. 
                          P (serialization_filter x \<sigma> (L\<union>{l})) x \<sigma> (L\<union>{l})) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. serialization_filter x \<sigma> (L \<union> {l}))` (\<Union>(Referenced_locations_Value`ran(f))-{l})))) l \<sigma> L)  \<Longrightarrow>
(\<And>l \<sigma> L l'.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (serialization_filter l' \<sigma> (L\<union>{l})) l' \<sigma>  (L\<union>{l}))\<Longrightarrow>
           (P ({l}\<union>(serialization_filter l' \<sigma> (L\<union>{l}))) l \<sigma> L))         \<Longrightarrow>   
   P (serialization_filter l' \<sigma>' L') l' \<sigma>' L'"
apply (rule serialization_filter.induct)
apply (case_tac "\<sigma> l")
(*2 CASE None*)
 apply force
apply (case_tac a)
(*2 case obj *)
 apply (rule SFI1SG1B,clarsimp,simp)
(*4*)
   apply ((rotate_tac 1,drule_tac x=l in meta_spec)+,(rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+,(rotate_tac -1,drule_tac x=L in meta_spec)+)
   apply blast
  apply ((rotate_tac 1,drule_tac x=l in meta_spec)+,(rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+,(rotate_tac -1,drule_tac x=L in meta_spec)+)
  apply blast
 apply ((rotate_tac 1,drule_tac x=l in meta_spec)+,(rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+,(rotate_tac -1,drule_tac x=L in meta_spec)+)
 apply blast
apply ((rotate_tac 1,drule_tac x=l in meta_spec)+,(rotate_tac -1,drule_tac x=\<sigma> in meta_spec)+,(rotate_tac -1,drule_tac x=L in meta_spec)+)
(* CASE StoredVal*)
apply (case_tac x2)
 apply simp
apply (erule SFI1SG2,simp+)
done

lemma serialization_filter2: "   (\<And>l \<sigma> L. P {} ) \<Longrightarrow> (* NOT USED FOR THE MOMENT *)
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
apply (insert  serialization_filter1 [of "(\<lambda> S l \<sigma> L. (P S))" ])
apply auto
done

section{* Serialization filter lemmas*}
lemma serialization_filter_subset: "serialization_filter l \<sigma> L \<subseteq> dom \<sigma>"
apply (rule_tac P= "\<lambda> S l \<sigma> L. (S \<subseteq> dom \<sigma>)" in   serialization_filter1)
   apply auto
apply (drule_tac x=xb in bspec)
 apply auto
apply (drule_tac x=xa in bspec)
 apply (auto split: option.splits )
done

lemma serialize_filter_subset: "dom (serialize_filter l \<sigma>) \<subseteq> dom \<sigma>"
apply (insert serialization_filter_subset, auto)
done

lemma serialize_filter_value: "(serialize_filter l \<sigma>) l' = Some x \<Longrightarrow> \<sigma> l' = Some x"
apply (subgoal_tac "l'\<in>(serialization_filter l \<sigma> {})")
 apply (drule_tac m=\<sigma> in Map.restrict_in)
 apply force
apply (rule Map_restrict_Some,blast)
done

lemma Serialization_excluded_set_subset[rule_format]: 
"\<forall> L . L\<subseteq>L' \<longrightarrow> serialization_filter l \<sigma> L' \<subseteq> serialization_filter l \<sigma> L"
apply (rule_tac P= "\<lambda> S l \<sigma> L'. (\<forall>L. L\<subseteq>L' \<longrightarrow> S \<subseteq> serialization_filter l \<sigma> L)" in   serialization_filter1)
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

lemma serialization_filter_dom_subset_pre[rule_format]: 
          "\<forall> \<sigma>' v. (serialize v \<sigma> \<sigma>' \<longrightarrow> (v=ObjRef l \<longrightarrow> serialization_filter l \<sigma> L \<subseteq> dom \<sigma>'))"
apply (rule_tac P= "\<lambda> S l \<sigma> L. \<forall> \<sigma>' v. (serialize v \<sigma> \<sigma>' \<longrightarrow> (v=ObjRef l \<longrightarrow> S \<subseteq> dom \<sigma>'))" in   serialization_filter1)
(*4*)
   apply force
  apply clarsimp
  apply (erule serialize.cases,simp,simp,simp)
 apply clarsimp
 apply (intro conjI)
  apply (drule serialize_value)
  apply force
 apply clarsimp
 apply (drule_tac x=xb in bspec,assumption)
 apply (drule_tac x=xa in bspec,assumption)
 apply (drule_tac x=\<sigma>' in spec)
 apply clarsimp
 apply (case_tac xb)
(*3 null*)
  apply (clarsimp simp: Referenced_locations_Value_def)
(*2 objref*)
 apply clarsimp
 apply (erule impE)
  apply (erule serialize.cases,clarsimp)
    apply (drule_tac x="ObjRef x2" in bspec,assumption)
    apply clarsimp+
    apply (rule serialize_substore_result)
  apply simp+
(*2*)
 apply force
apply clarsimp
apply (intro conjI)
(*3*)  
  apply clarsimp
  apply (drule serialize_value,force)
 apply clarsimp
 apply (drule serialize_value,force)
(*1*)
apply clarsimp
apply (intro conjI) 
 apply (drule serialize_value,force)
apply clarsimp
apply (drule_tac x=\<sigma>' in spec)
apply (erule impE)
 apply (erule serialize.cases)
apply auto
done

lemma serialization_filter_dom_subset: 
  "serialize (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow>  serialization_filter l \<sigma> L \<subseteq> dom \<sigma>' "
by (drule serialization_filter_dom_subset_pre[of "ObjRef l" \<sigma> \<sigma>'],auto)

lemma serialization_filter_coincide_val_pre[rule_format,elim]: (* VERY SIMILAR TO LEMMA dom_subset_pre*)
"\<forall> \<sigma>' v l'.(serialize v \<sigma> \<sigma>' \<longrightarrow> (v=ObjRef x2 \<longrightarrow> l'\<in>serialization_filter x2 \<sigma> L \<longrightarrow> \<sigma> l' = \<sigma>' l'))"
apply (rule_tac P= "\<lambda> S l \<sigma> L. \<forall> \<sigma>' v l'. (serialize v \<sigma> \<sigma>' \<longrightarrow> (v=ObjRef l \<longrightarrow> l'\<in>S \<longrightarrow> \<sigma> l' = \<sigma>' l'))" in   serialization_filter1)
 apply clarsimp
  apply clarsimp
  apply (erule serialize.cases,simp,simp,simp)
 apply clarsimp
 apply (intro conjI)
  apply (drule serialize_value)
 apply clarsimp

 apply clarsimp
 apply (drule_tac x=xa in bspec,assumption)
 apply (drule_tac x=x in bspec,assumption)
 apply (drule_tac x=\<sigma>' in spec)
 apply clarsimp
 apply (case_tac xa)
(*3 null*)
  apply (clarsimp simp: Referenced_locations_Value_def)
(*2 objref*)
 apply clarsimp
 apply (erule impE)
  apply (erule serialize.cases,clarsimp)
    apply (drule_tac x="ObjRef x2" in bspec,assumption)
    apply clarsimp
    apply (rule serialize_substore_result)
     apply simp+
 apply (intro conjI)
(*3*)  
  apply clarsimp
  apply (drule serialize_value,force)
 apply clarsimp
 apply (drule serialize_value,force)
(*1*)
apply clarsimp
apply (intro conjI) 
 apply (drule serialize_value,force)
apply clarsimp
apply (drule_tac x=\<sigma>' in spec)
apply (erule impE)
 apply (erule serialize.cases)
   apply auto
done

lemma serialization_filter_coincide_val: 
  "serialize v \<sigma> \<sigma>' \<Longrightarrow> (\<forall> L. case v of ObjRef l \<Rightarrow> l'\<in>serialization_filter l \<sigma> L \<longrightarrow> \<sigma>' l' = \<sigma> l' | null \<Rightarrow> True) "
by( auto split: Value.splits,drule serialization_filter_coincide_val_pre,auto)

lemma serialization_filter_origin: "\<sigma> l = Some y\<Longrightarrow>l\<in> serialization_filter l \<sigma> {}"
by (auto split: Storable.splits Value.splits option.splits)




section{*serialization filter well formed*}
lemma serialization_filter_WF_1step_obj[rule_format]: 
  "l\<in>serialization_filter l'' \<sigma> L \<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some (ObjRef l') 
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  l'\<in>L\<or>l'\<in>serialization_filter l'' \<sigma> L "
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. l\<in>S \<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some ( ObjRef l')   \<longrightarrow>Well_Formed_Store \<sigma>
\<longrightarrow>   l'\<in>L\<or>l'\<in>S" in   serialization_filter1)
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
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  l'\<in>L\<or>l'\<in>S" in   serialization_filter1)
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

lemma Serialization_WF: "Well_Formed_Store \<sigma> \<Longrightarrow> Well_Formed_Store (serialize_filter l \<sigma>)"
apply (unfold Well_Formed_Store_def)
apply (intro ballI)
apply (fold Well_Formed_Store_def)
apply (subgoal_tac " la \<in> dom \<sigma>")
 apply (case_tac "\<sigma> la")
  apply blast
 apply rule
 apply (unfold Referenced_locations_Location_def)
(*2*)
 apply (case_tac  "serialize_filter l \<sigma> la")
  apply blast
 apply (drule serialize_filter_value)
 apply (subgoal_tac "a=aa")
  apply clarify
  apply (case_tac aa,rename_tac obj')
  apply (case_tac obj')
   apply (frule serialize_filter_value)
   apply  clarsimp
   apply (subgoal_tac "serialize_filter l \<sigma> la = Some (Obj (ab, ba))")
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
  apply (frule serialize_filter_value)
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
apply (insert serialize_filter_subset[of \<sigma> l])
apply blast
done

section{*serialization filter VS serialize*}

theorem serializationfilter_smallest_serialize: "serialize (ObjRef l) \<sigma> \<sigma>' \<Longrightarrow> (serialize_filter l \<sigma>) \<subseteq>\<^sub>m \<sigma>'"
apply (rule map_le_eq)
 apply (frule serialization_filter_dom_subset[of l \<sigma> \<sigma>' "{}"])
 apply force
apply rule
apply (frule_tac l'=x in serialization_filter_coincide_val)
apply (drule_tac x="{}" in spec)
apply (auto simp: restrict_map_def)
done



lemma serialization_filter_verifies_serialize_weak_axiomatic_def: 
   "serialize_weak (ObjRef l) (\<sigma>|` (-L)) (\<sigma> |` serialization_filter l \<sigma> L)"
apply (rule_tac P="\<lambda> S l \<sigma> L. serialize_weak  (ObjRef l) (\<sigma>|` (-L)) (\<sigma> |` serialization_filter l \<sigma> L)"
            in serialization_filter1B)
(*4 None*)
   apply clarify
   apply (rule serialize_weak.intros(4))
   apply (force simp: restrict_map_def)
(*3 notobjref*)
  apply (case_tac V)
   apply (rule_tac v="null" in serialize_weak.intros(2),clarsimp)  
   apply (rule serialize_weak.intros(3))
  apply (force)

(*2 obj*)
 apply (rule serialize_weak_serialize_one_obj,simp,simp)
 apply (intro ballI)
 apply (case_tac v)
  apply (rule_tac x=empty in exI)
  apply clarsimp
  apply (rule serialize_weak.intros)
 apply (drule_tac x=x2 in bspec)
  apply force
 apply (rule_tac x="(\<sigma> |` (if x2 \<in> L then {}
                          else case \<sigma> x2 of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow> {x2} \<union> \<Union>((\<lambda>x. serialization_filter x \<sigma> (insert l L \<union> {x2})) ` \<Union>(Referenced_locations_Value ` ran (fst obj))) | Some (StoredVal null) \<Rightarrow> {x2}
                               | Some (StoredVal (ObjRef l')) \<Rightarrow> {x2} \<union> serialization_filter l' \<sigma> (insert l L \<union> {x2})))" in exI)
 apply clarsimp
  apply (subgoal_tac " (\<sigma> |` (- insert l L)) = (\<sigma> |` (- L \<inter> - {l}))")
  apply (intro conjI impI)
(*5*)
    apply (rule serialize_weak.intros(4),force)
   apply clarsimp
  apply (force simp: map_le_def Map.restrict_map_def)
 apply (force simp: Map.restrict_map_def)

(*1 ref*)
apply (rule serialize_weak_serialize_one_ref,simp+)
apply (intro conjI)
  apply clarsimp
  apply (rule serialize_weak.intros(4),force)
 apply clarsimp
 apply (rule serialize_weak.intros(4),force)
apply clarsimp
apply (subgoal_tac " (\<sigma> |` (- insert l L)) = (\<sigma> |` (- L \<inter> - {l}))")
 apply clarsimp
 apply (rule serialize_weak_substore_result,simp)
 apply (force simp: map_le_def )
apply (force simp: Map.restrict_map_def)
done

theorem serialization_filter_verifies_serialize_axiomatic_def: 
"Well_Formed_Store \<sigma> \<Longrightarrow> l\<in>dom \<sigma> 
    \<Longrightarrow> serialize (ObjRef l) \<sigma> (serialize_filter l \<sigma>)"
apply (subgoal_tac "serialize_weak (ObjRef l) (\<sigma>|`(-{})) (\<sigma>|` (serialization_filter l \<sigma> {}))")
 apply (erule serialize_weak_serialize,simp,simp add: Map.restrict_map_def)
apply (rule serialization_filter_verifies_serialize_weak_axiomatic_def)
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

lemma subst_WF: " Well_Formed_Store \<sigma> \<Longrightarrow> check_subst \<sigma> \<psi> \<sigma>' \<Longrightarrow> Well_Formed_Store \<sigma>'"
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
 apply auto
apply blast
done


section{*Mark filtering*}

function (sequential) Serialization_filter_eff :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (Serialization_filter_eff l \<sigma> L ) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      None => {} |
      Some (Obj obj) \<Rightarrow> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S)   )) ) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) ({l}))  |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (Serialization_filter_eff l' \<sigma> (L\<union>{l}) )|
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

abbreviation serialize_filter_eff:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
where
"serialize_filter_eff l \<sigma> \<equiv>  \<sigma> |` Serialization_filter_eff l \<sigma> {} " 

lemma SFI2SG1: "
       (\<And>l \<sigma> L a b S.
           l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
                     \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a). P (Serialization_filter_eff x \<sigma> (L \<union> {l} \<union> S x) ) x \<sigma> (L \<union> {l} \<union> S x)  \<Longrightarrow>
                     P ({l} \<union> \<Union>((\<lambda>x. Serialization_filter_eff x \<sigma> (L \<union> {l} \<union> S x) ) ` \<Union>(Referenced_locations_Value ` ran a))) l \<sigma> L ) \<Longrightarrow>
       (\<And>l \<sigma> L l' . l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> P (Serialization_filter_eff l' \<sigma> (L \<union> {l}) ) l' \<sigma> (L \<union> {l})  \<Longrightarrow> P ({l} \<union> Serialization_filter_eff l' \<sigma> (L \<union> {l}) ) l \<sigma> L ) \<Longrightarrow>
       (\<And>x2 prod x xa.
           l \<notin> L \<Longrightarrow> \<sigma> l = Some x2 \<Longrightarrow>
                     x2 = Obj prod \<Longrightarrow>
                     x \<in> set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
                     P (Serialization_filter_eff x \<sigma> (L \<union> {l} \<union> xa) ) x \<sigma> (L \<union> {l} \<union> xa) ) \<Longrightarrow>
       (\<And>l \<sigma> L  . P {} l \<sigma> L ) \<Longrightarrow> \<sigma> l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (Serialization_filter_eff l \<sigma> L ) l \<sigma> L 
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
  apply (drule_tac SF=Serialization_filter_eff and \<sigma> = \<sigma> and LS ="{l}" and l=l and L=L  in SF_fold_to_Union,simp)
(*SF_fold_to_Union[rule_format]: "((distinct fieldlist)\<longrightarrow>(\<exists> F . (fold (\<lambda>x S.  (S\<union>(SF x \<sigma> (L\<union>{l}\<union>S) T)) ) fieldlist (LS)  = LS\<union> \<Union>((\<lambda> x . SF x \<sigma> (L\<union>{l}\<union>F x) T) `(set fieldlist)))))"*)
  apply clarsimp
(*3*)
  apply (drule_tac x=F in meta_spec)
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
           P (Serialization_filter_eff nat \<sigma> (L \<union> {l}) ) nat \<sigma> (L \<union> {l}) ) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (Serialization_filter_eff l' \<sigma> (L \<union> {l}) ) l' \<sigma> (L \<union> {l})  \<Longrightarrow>
              P ({l} \<union> Serialization_filter_eff l' \<sigma> (L \<union> {l}) ) l \<sigma> L ) \<Longrightarrow>
  \<sigma> l = Some a \<Longrightarrow>  P {} l \<sigma> L \<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (Serialization_filter_eff l \<sigma> L ) l \<sigma> L 
  "
apply clarsimp
done

lemma Serialization_filter_eff_induct_1: "   
(\<And>l \<sigma> L . P {} l \<sigma> L ) \<Longrightarrow> 
(\<And>l \<sigma> L V .  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L ) \<Longrightarrow> 
(\<And>l \<sigma> L a b S .
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (Serialization_filter_eff x \<sigma> (L\<union>{l}\<union>(S x)) ) x \<sigma> (L\<union>{l}\<union>(S x)) 
                                     ) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. Serialization_filter_eff x \<sigma> (L \<union> {l}\<union>S x))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L )  \<Longrightarrow>
(\<And>l \<sigma> L l' .
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (Serialization_filter_eff l' \<sigma> (L\<union>{l}) ) l' \<sigma>  (L\<union>{l}) )\<Longrightarrow>
           (P ({l}\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}) )) l \<sigma> L ))         \<Longrightarrow>   
   P (Serialization_filter_eff l' \<sigma>' L' ) l' \<sigma>' L' "
apply (rule Serialization_filter_eff.induct)
apply (case_tac "\<sigma> l")
 apply (simp)
(*1*)
apply (case_tac a)
 apply (erule SFI2SG1,simp,simp,simp,simp,simp)
apply (rename_tac val,case_tac val)
 apply force
apply (erule SFI2SG2,simp+)
done



lemma Serialization_filter_effD_L:"x\<in>Serialization_filter_eff l \<sigma> L \<Longrightarrow> l\<notin>L"
apply force
done

lemma Serialization_filter_effD_L_contrapos:"l\<notin>Serialization_filter_eff l \<sigma> L  \<Longrightarrow> l\<in>L \<or> \<sigma> l = None"
apply (simp split: option.splits Storable.splits split_if_asm )
apply (clarsimp,rename_tac f C)
apply (subgoal_tac "l\<in>{l}",drule_tac F="\<lambda> l' S . (if l' = l \<or> l' \<in> L \<or> l' \<in> S then {}
                                  else case \<sigma> l' of None \<Rightarrow> {}
                                                 | Some (Obj obj) \<Rightarrow>
                                                     fold (\<lambda>l'a Sa. Sa \<union> Serialization_filter_eff l'a \<sigma> (insert l (L \<union> S) \<union> {l'} \<union> Sa))
                                                      (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {l'}
                                                 | Some (StoredVal null) \<Rightarrow> {l'} | Some (StoredVal (ObjRef l'a)) \<Rightarrow> {l'} \<union> Serialization_filter_eff l'a \<sigma> (insert l (L \<union> S) \<union> {l'}) )" in AuxiliaryFunctions.foldr_Un_init
       ,blast)
apply blast
apply (simp split: Value.splits Storable.splits split_if_asm )
done

lemma Serialization_filter_eff_no_l[simp]:"l\<notin>Serialization_filter_eff l \<sigma> L = (l\<in>L \<or> \<sigma> l = None)"
apply rule
apply (rule Serialization_filter_effD_L_contrapos,simp)
apply auto
done

lemma Serialization_filter_effD: "x\<in>Serialization_filter_eff l \<sigma> L \<Longrightarrow> 
                                   ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S)))) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>Serialization_filter_eff l' \<sigma> (L\<union>{l}) )))"
apply (case_tac "\<sigma> l")
apply (simp split: option.splits Storable.splits split_if_asm )
apply (case_tac "x=l",force)
apply (case_tac a)
apply (force split: option.splits Storable.splits split_if_asm Value.splits)
apply (force split: Value.splits split_if_asm)
done

lemma Serialization_filter_effI: "l\<notin>L\<Longrightarrow> ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S))) ) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>Serialization_filter_eff l' \<sigma> (L\<union>{l}) )) ) 
                                   \<Longrightarrow> x\<in>Serialization_filter_eff l \<sigma> L "
apply (elim disjE)
apply (clarsimp split: Storable.splits split_if_asm)
apply (clarsimp split: Storable.splits split_if_asm )
(*3*)
apply (case_tac y,rename_tac obj',case_tac obj')
apply (subgoal_tac "l\<in>{l}",drule AuxiliaryFunctions.foldr_Un_init,simp,blast)
apply (simp split: Value.splits)
apply force
done

lemma Serialization_filter_eff_def2: 
"x\<in>Serialization_filter_eff l \<sigma> L  = (l\<notin>L \<and> ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                  x \<in> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S))) ) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>Serialization_filter_eff l' \<sigma> (L\<union>{l}) )) )) 
                       "
apply rule 
apply (frule Serialization_filter_effD, drule Serialization_filter_effD_L,blast)
apply (rule Serialization_filter_effI,blast,blast)
done

declare Serialization_filter_eff.simps[simp del]

lemma Serialization_filter_eff_empty[simp]: "(Serialization_filter_eff l \<sigma> L  ={}) = (l\<in>L\<or> \<sigma> l = None)"
apply rule
apply (case_tac "l\<in>(Serialization_filter_eff l \<sigma> L )")
apply force
apply (drule Serialization_filter_effD_L_contrapos)
apply simp
apply (clarsimp simp: Serialization_filter_eff.simps)
done

lemma serialize_value_Mark: "(serialize_filter_eff l \<sigma>) l' = Some x \<Longrightarrow> \<sigma> l' = Some x"
apply (subgoal_tac "l'\<in>(Serialization_filter_eff l \<sigma> {} )")
 apply (drule_tac m=\<sigma> in Map.restrict_in)
 apply force
apply (rule Map_restrict_Some,blast)
done

lemma Serialization_filter_eff_serialization_filter:
" \<forall> L'. (L'\<subseteq>L \<longrightarrow>Serialization_filter_eff l \<sigma> L \<subseteq> serialization_filter l \<sigma> L')"
apply (rule_tac P= "\<lambda> S l \<sigma> L. (\<forall> L'. (L'\<subseteq>L \<longrightarrow>S \<subseteq> serialization_filter l \<sigma> L'))" in   Serialization_filter_eff_induct_1)
apply clarsimp
apply clarify
apply (subgoal_tac "serialization_filter l \<sigma> L'={l}")
apply force
apply (case_tac V,simp)
apply force
apply force

apply clarify

apply (subgoal_tac "l\<notin>L'")
prefer 2
apply force

apply simp
apply (case_tac "x=l",force)
apply clarsimp
apply (drule_tac x=xa in bspec)
apply simp

apply (drule_tac x=xb in bspec)
apply simp
apply (drule_tac x="insert l L" in spec)
apply simp
apply (erule impE)
apply force
apply (case_tac "xb = l\<or> \<sigma> xb=None \<or>xb\<in>L")
apply (subgoal_tac "Serialization_filter_eff xb \<sigma> (insert l (L \<union> S xb)) = {}")
apply force
apply force

apply clarsimp
apply (rule_tac x=xb in bexI)
apply simp
apply (subgoal_tac "serialization_filter xb \<sigma>  (insert l L ) \<subseteq> serialization_filter xb \<sigma>  (insert l L' ) ")
prefer 2
apply (rule Serialization_excluded_set_subset,force)

apply simp
apply (rotate_tac 3, drule_tac c=x in subsetD,assumption)
apply (subgoal_tac "xb\<notin>L'",force)
apply force

apply force

apply clarify
apply (subgoal_tac "l\<notin>L'")
prefer 2
apply blast

apply (drule_tac x="insert l L'" in spec)
apply (erule impE,blast)
apply (erule UnE)
apply (force split: Storable.splits Value.splits option.splits)
apply clarsimp
apply rule
apply clarify
apply (subgoal_tac "Serialization_filter_eff l \<sigma> (insert l L) ={}",blast)
apply force
apply rule
apply clarsimp
apply (subgoal_tac "Serialization_filter_eff l' \<sigma> (insert l L) ={}",blast)
apply force
apply force
done
lemma Serialization_filter_eff_origin: "l \<notin> L \<Longrightarrow> \<sigma> l \<noteq>None\<Longrightarrow> l \<in> Serialization_filter_eff l \<sigma> L"
 apply (simp add: Serialization_filter_eff.simps)
 apply (auto split: Storable.splits Value.splits option.splits)
 apply (subgoal_tac "distinct (sorted_list_of_set (\<Union>x\<in>ran a. Referenced_locations_Value x))")
apply (drule SF_fold_to_Union,force)
 apply (rule distinct_sorted_list_of_set)
done

lemma Serialization_filter_eff_excluded_set_subset[rule_format]: 
"\<forall> L . L\<subseteq>L' \<longrightarrow> Serialization_filter_eff l \<sigma> L' \<subseteq> Serialization_filter_eff l \<sigma> L"
apply (rule_tac P= "\<lambda> S l \<sigma> L'. (\<forall>L. L\<subseteq>L' \<longrightarrow> S \<subseteq> Serialization_filter_eff l \<sigma> L)" in   Serialization_filter_eff_induct_1)
(*4*)
   apply clarsimp
  apply (clarsimp split: Value.splits)
  apply (subgoal_tac "l\<notin> La")
  apply (rule Serialization_filter_eff_origin,simp+)
  apply blast
  apply clarsimp
  apply rule
   apply (rule Serialization_filter_eff_origin)
  apply blast
  apply simp
  apply clarsimp

  apply (drule_tac x=xa in bspec,assumption)
  apply (drule_tac x=xb in bspec,assumption)
   apply (drule_tac x="insert l (La \<union> S xb)" in spec)
 apply (erule impE,blast)
apply (drule_tac c=x in subsetD,assumption)
 apply (simp(no_asm) add: Serialization_filter_eff.simps)
  apply (subgoal_tac "l\<notin> La")
 apply clarsimp
 apply (subgoal_tac "distinct (sorted_list_of_set (\<Union>x\<in>ran a. Referenced_locations_Value x)) ")
apply (drule_tac SF=Serialization_filter_eff and \<sigma>=\<sigma> and l=l and L=La and LS="{l}" in SF_fold_to_Union_what_F2,simp)
apply (case_tac "x=l")
apply force
apply clarsimp
apply (subgoal_tac "finite (\<Union>x\<in>ran a. Referenced_locations_Value x)")
apply (frule_tac x=xb in AuxiliaryFunctions.sorted_list_of_set_nthI)
apply force
apply clarsimp
apply (rule_tac x=n in exI)
apply (drule sorted_list_of_set_card_length)
apply clarsimp
STOPPED HERE :
induction is not powerful enough because we loose the relation between the S in one exploration of an object and the S in another exploration of the same object
 (insert l (La \<union> S (sorted_list_of_set (\<Union>x\<in>ran a. Referenced_locations_Value x) ! n)))
 (insert l (La \<union> fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (insert l (La \<union> S))) (take n (sorted_list_of_set (\<Union>x\<in>ran a. Referenced_locations_Value x))) {l}))
 apply (clarsimp split: Storable.splits Value.splits option.splits)
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

section
(* mark filtering with additional param useful?
section{*Mark filtering*}


function (sequential) Serialization_filter_eff :: "Location \<Rightarrow> Store \<Rightarrow> Location set \<Rightarrow> Location set\<Rightarrow> Location set"
(*serialize v \<sigma> \<sigma>' is true if the serialization of value v is a subset of \<sigma>' (using store \<sigma>)*)
  where
    "
    (Serialization_filter_eff l \<sigma> L T) = (if l\<in>L then {} else
      (case \<sigma>(l) of
      None => {} |
      Some (Obj obj) \<Rightarrow> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S)   (T\<union>(\<Union>(Referenced_locations_Value`ran(fst(obj))))))) ) 
                (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fst(obj))))) ({l}))  |
      Some (StoredVal (ObjRef l')) \<Rightarrow>{l}\<union> (Serialization_filter_eff l' \<sigma> (L\<union>{l}) T)|
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

abbreviation serialize_filter_eff:: "Location \<Rightarrow> Store \<Rightarrow> Store" 
where
"serialize_filter_eff l \<sigma> \<equiv>  \<sigma> |` Serialization_filter_eff l \<sigma> {} {}" 

lemma SFI2SG1: "
       (\<And>l \<sigma> L a b S T.
           l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a, b)) \<Longrightarrow>
                     \<forall>x\<in>\<Union>(Referenced_locations_Value ` ran a). P (Serialization_filter_eff x \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a))) x \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a)) \<Longrightarrow>
                     P ({l} \<union> \<Union>((\<lambda>x. Serialization_filter_eff x \<sigma> (L \<union> {l} \<union> S x) (T \<union> \<Union>(Referenced_locations_Value ` ran a))) ` \<Union>(Referenced_locations_Value ` ran a))) l \<sigma> L T) \<Longrightarrow>
       (\<And>l \<sigma> L l' T. l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> P (Serialization_filter_eff l' \<sigma> (L \<union> {l}) T) l' \<sigma> (L \<union> {l}) T \<Longrightarrow> P ({l} \<union> Serialization_filter_eff l' \<sigma> (L \<union> {l}) T) l \<sigma> L T) \<Longrightarrow>
       (\<And>x2 prod x xa.
           l \<notin> L \<Longrightarrow> \<sigma> l = Some x2 \<Longrightarrow>
                     x2 = Obj prod \<Longrightarrow>
                     x \<in> set (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
                     P (Serialization_filter_eff x \<sigma> (L \<union> {l} \<union> xa) (T \<union> \<Union>(Referenced_locations_Value ` ran (fst prod)))) x \<sigma> (L \<union> {l} \<union> xa) (T \<union> \<Union>(Referenced_locations_Value ` ran (fst prod)))) \<Longrightarrow>
       (\<And>l \<sigma> L  T. P {} l \<sigma> L T) \<Longrightarrow> \<sigma> l = Some a \<Longrightarrow> a = Obj prod \<Longrightarrow> P (Serialization_filter_eff l \<sigma> L T) l \<sigma> L T
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
  apply (drule_tac SF=Serialization_filter_eff and \<sigma> = \<sigma> and LS ="{l}" and l=l and L=L and T="T\<union>UNION (ran f) Referenced_locations_Value" in SF_fold_to_Union,simp)
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
           P (Serialization_filter_eff nat \<sigma> (L \<union> {l}) T) nat \<sigma> (L \<union> {l}) T) \<Longrightarrow>
     (\<And>l'. l \<notin> L \<Longrightarrow>
              \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
              P (Serialization_filter_eff l' \<sigma> (L \<union> {l}) T) l' \<sigma> (L \<union> {l}) T \<Longrightarrow>
              P ({l} \<union> Serialization_filter_eff l' \<sigma> (L \<union> {l}) T) l \<sigma> L T) \<Longrightarrow>
  \<sigma> l = Some a \<Longrightarrow>  P {} l \<sigma> L T\<Longrightarrow>a = StoredVal (ObjRef l') \<Longrightarrow> P (Serialization_filter_eff l \<sigma> L T) l \<sigma> L T
  "
apply clarsimp
done

lemma Serialization_filter_eff1: "   
(\<And>l \<sigma> L T. P {} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L V T.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L a b S T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (Serialization_filter_eff x \<sigma> (L\<union>{l}\<union>(S x)) (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) x \<sigma> (L\<union>{l}\<union>(S x)) 
                                     (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. Serialization_filter_eff x \<sigma> (L \<union> {l}\<union>S x) (T\<union>\<Union>(Referenced_locations_Value`(ran a))))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L T)  \<Longrightarrow>
(\<And>l \<sigma> L l' T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (Serialization_filter_eff l' \<sigma> (L\<union>{l}) T) l' \<sigma>  (L\<union>{l}) T)\<Longrightarrow>
           (P ({l}\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}) T)) l \<sigma> L T))         \<Longrightarrow>   
   P (Serialization_filter_eff l' \<sigma>' L' T) l' \<sigma>' L' T"
apply (rule Serialization_filter_eff.induct)
apply (case_tac "\<sigma> l")
 apply (simp)
(*1*)
apply (case_tac a)
 apply (erule SFI2SG1,simp,simp,simp,simp,simp)
apply (rename_tac val,case_tac val)
 apply force
apply (erule SFI2SG2,simp+)
done



lemma Serialization_filter_effD_L:"x\<in>Serialization_filter_eff l \<sigma> L T\<Longrightarrow> l\<notin>L"
apply force
done

lemma Serialization_filter_effD_L_contrapos:"l\<notin>Serialization_filter_eff l \<sigma> L T \<Longrightarrow> l\<in>L \<or> \<sigma> l = None"
apply (simp split: option.splits Storable.splits split_if_asm )
apply (clarsimp,rename_tac f C)
apply (subgoal_tac "l\<in>{l}",drule_tac F="\<lambda> l' S . (if l' = l \<or> l' \<in> L \<or> l' \<in> S then {}
                                  else case \<sigma> l' of None \<Rightarrow> {}
                                                 | Some (Obj obj) \<Rightarrow>
                                                     fold (\<lambda>l'a Sa. Sa \<union> Serialization_filter_eff l'a \<sigma> (insert l (L \<union> S) \<union> {l'} \<union> Sa) (T \<union> UNION (ran (fst (f, C))) Referenced_locations_Value \<union> \<Union>(Referenced_locations_Value ` ran (fst obj))))
                                                      (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {l'}
                                                 | Some (StoredVal null) \<Rightarrow> {l'} | Some (StoredVal (ObjRef l'a)) \<Rightarrow> {l'} \<union> Serialization_filter_eff l'a \<sigma> (insert l (L \<union> S) \<union> {l'}) (T \<union> UNION (ran (fst (f, C))) Referenced_locations_Value))" in AuxiliaryFunctions.foldr_Un_init
       ,blast)
apply blast
apply (simp split: Value.splits Storable.splits split_if_asm )
done

lemma Serialization_filter_eff_no_l[simp]:"l\<notin>Serialization_filter_eff l \<sigma> L T= (l\<in>L \<or> \<sigma> l = None)"
apply rule
apply (rule Serialization_filter_effD_L_contrapos,simp)
apply auto
done

lemma Serialization_filter_effD_: "x\<in>Serialization_filter_eff l \<sigma> L T\<Longrightarrow> 
                                   ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(fields)))))) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>Serialization_filter_eff l' \<sigma> (L\<union>{l}) T)))"
apply (case_tac "\<sigma> l")
apply (simp split: option.splits Storable.splits split_if_asm )
apply (case_tac "x=l",force)
apply (case_tac a)
apply (force split: option.splits Storable.splits split_if_asm Value.splits)
apply (force split: Value.splits split_if_asm)
done

lemma Serialization_filter_effI: "l\<notin>L\<Longrightarrow> ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                        x \<in> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(fields))))) ) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>Serialization_filter_eff l' \<sigma> (L\<union>{l}) T)) ) 
                                   \<Longrightarrow> x\<in>Serialization_filter_eff l \<sigma> L T"
apply (elim disjE)
apply (clarsimp split: Storable.splits split_if_asm)
apply (clarsimp split: Storable.splits split_if_asm )
(*3*)
apply (case_tac y,rename_tac obj',case_tac obj')
apply (subgoal_tac "l\<in>{l}",drule AuxiliaryFunctions.foldr_Un_init,simp,blast)
apply (simp split: Value.splits)
apply force
done

lemma Serialization_filter_eff_def2: 
"x\<in>Serialization_filter_eff l \<sigma> L T = (l\<notin>L \<and> ((\<exists> fields C . (\<sigma> l = Some (Obj (fields,C))\<and> 
                                  x \<in> (fold (\<lambda>l' S.  (S\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}\<union>S) (T\<union>\<Union>(Referenced_locations_Value`ran(fields))))) ) 
                                        (sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(fields)))) ({l})))) \<or>  
                                   (x=l \<and>\<sigma> l \<noteq>None) \<or>
                                   (\<exists> l' . (\<sigma> l = Some (StoredVal (ObjRef l'))\<and> x\<in>Serialization_filter_eff l' \<sigma> (L\<union>{l}) T)) )) 
                       "
apply rule 
apply (frule Serialization_filter_effD_, drule Serialization_filter_effD_L,blast)
apply (rule Serialization_filter_effI,blast,blast)
done

declare Serialization_filter_eff.simps[simp del]

lemma Serialization_filter_eff_empty[simp]: "(Serialization_filter_eff l \<sigma> L T ={}) = (l\<in>L\<or> \<sigma> l = None)"
apply rule
apply (case_tac "l\<in>(Serialization_filter_eff l \<sigma> L T)")
apply force
apply (drule Serialization_filter_effD_L_contrapos)
apply simp
apply (clarsimp simp: Serialization_filter_eff.simps)
done

lemma serialize_value_Mark: "(serialize_filter_eff l \<sigma>) l' = Some x \<Longrightarrow> \<sigma> l' = Some x"
apply (subgoal_tac "l'\<in>(Serialization_filter_eff l \<sigma> {} {})")
 apply (drule_tac m=\<sigma> in Map.restrict_in)
 apply force
apply (rule Map_restrict_Some,blast)
done

lemma Serialization_filter_eff_serialization_filter:
"Serialization_filter_eff l \<sigma> L {}= serialization_filter l \<sigma> L"
apply (rule serialization_filter1B)
apply auto

lemma Serialization_filter_eff2: "   
(\<And>l \<sigma> L T. P {} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L V T.  l\<notin>L \<Longrightarrow> \<sigma> l = Some (StoredVal V) \<Longrightarrow>isnotObjRef V \<Longrightarrow>P {l} l \<sigma> L T) \<Longrightarrow> 
(\<And>l \<sigma> L a b S T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
        let locationlist = sorted_list_of_set (\<Union>(Referenced_locations_Value`ran(a))) in
           S = (\<lambda> n . (if (n< length locationlist) then (L\<union>{l}\<union> (\<Union>k\<in>{n'. n'<n}. (Serialization_filter_eff ((locationlist)!k) \<sigma> (L\<union>{l}\<union>S k) T))) else {})) \<Longrightarrow>
           (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). 
                          P (Serialization_filter_eff x \<sigma> (L\<union>{l}\<union>(S x)) (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) x \<sigma> (L\<union>{l}\<union>(S x)) 
                                     (T\<union>\<Union>(Referenced_locations_Value`(ran a)))) \<Longrightarrow>
            P ({l}\<union>(\<Union> ((\<lambda> x. Serialization_filter_eff x \<sigma> (L \<union> {l}\<union>S x) (T\<union>\<Union>(Referenced_locations_Value`(ran a))))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) l \<sigma> L T)  \<Longrightarrow>
(\<And>l \<sigma> L l' T.
        l \<notin> L \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow> 
           (P (Serialization_filter_eff l' \<sigma> (L\<union>{l}) T) l' \<sigma>  (L\<union>{l}) T)\<Longrightarrow>
           (P ({l}\<union>(Serialization_filter_eff l' \<sigma> (L\<union>{l}) T)) l \<sigma> L T))         \<Longrightarrow>   
   P (Serialization_filter_eff l' \<sigma>' L' T) l' \<sigma>' L' T"
apply (rule Serialization_filter_eff.induct)
apply (case_tac "\<sigma> l")
 apply (simp add: Serialization_filter_eff.simps)
(*1*)
apply (case_tac a)

 apply (erule SFI2SG1,simp,simp,simp,simp,simp)
apply (case_tac Value)
(* apply force
apply (erule SFI2SG2,simp+)
done



lemma T_is_accessory_pre: "x\<in>Serialization_filter_eff l \<sigma> L T \<longrightarrow> x\<in>Serialization_filter_eff l \<sigma> L (T\<union>T')"
apply (rule_tac P="\<lambda> S l \<sigma> L T. x\<in>S \<longrightarrow>x\<in> Serialization_filter_eff l \<sigma> L (T\<union>T')" in Serialization_filter_eff1)
apply auto
apply (erule Serialization_filter_effI_,force)
apply (erule Serialization_filter_effI_,force)
apply (erule Serialization_filter_effI_,simp)
apply (drule_tac x=xa in bspec,simp)
apply (drule_tac x=xaa in bspec,simp)
apply clarsimp
S too imprecise

lemma serialization_filter_WF_1step_obj[rule_format]: 
  "l\<in>Serialization_filter_eff l'' \<sigma> L T\<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some (ObjRef l') 
        \<longrightarrow>Well_Formed_Store \<sigma>\<longrightarrow>  \<exists> t\<in>T. l'\<in>serialization_filter l'' \<sigma> L {} \<or>l'\<in>L\<or>l'\<in>serialization_filter l'' \<sigma> L T"
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. l\<in>S \<longrightarrow> \<sigma> l = Some (Obj (a,b)) \<longrightarrow>  a x = Some ( ObjRef l')   \<longrightarrow>Well_Formed_Store \<sigma>
\<longrightarrow>   l'\<in>L\<or>l'\<in>S" in   serialization_filter1)
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


lemma Serialization_WF: "Well_Formed_Store \<sigma> \<Longrightarrow> Well_Formed_Store (serialize_filter_eff l \<sigma>)"
apply (unfold Well_Formed_Store_def)
apply (intro ballI)
apply (fold Well_Formed_Store_def)
apply (subgoal_tac " la \<in> dom \<sigma>")
 apply (case_tac "\<sigma> la")
  apply blast
 apply rule
 apply (unfold Referenced_locations_Location_def)
(*2*)
 apply (case_tac  "serialize_filter_eff l \<sigma> la")
  apply blast
 apply (drule serialize_value)
 apply (subgoal_tac "a=aa")
  apply clarify
  apply (case_tac aa,case_tac prod)
   apply (frule serialize_value)
   apply  clarsimp
   apply (subgoal_tac "serialize_filter l \<sigma> la = Some (Obj (ab, ba))")
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
apply (insert serialize_filter_subset[of \<sigma> l])
apply blast
done


lemma Serialization_filter_eff_union: (Serialization_filter_eff l' \<sigma> L\<union>L')\<union>L' = (Serialization_filter_eff l' \<sigma> L\<union>L')

lemma fold_union_init[rule_format]: "\<forall> L'' . fold (\<lambda>l' S. S \<union> (Serialization_filter_eff l' \<sigma> S)) list (L \<union> L'') = (fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> S) list L) \<union> L''"
apply (induct_tac list)
apply force
apply clarsimp
apply (drule_tac x="L''\<union>L'' \<union> Serialization_filter_eff a \<sigma> (L \<union> L'')" in spec) 
apply simp
apply (subgoal_tac "(L'' \<union> F a (L \<union> L'')) =   (L'' \<union> (F a (L \<union> L'')))")
apply simp
apply blast
apply blast
done
lemma "\<forall> L' . l \<in> fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (L' \<union> S)) list L = (l\<in>L\<or> 
            ( \<exists> i<length list . let S =  fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (L' \<union> S)) (take i list) L  in  (l\<in>Serialization_filter_eff (list!i) \<sigma> (L' \<union> S) \<and> l\<notin>S)))"
apply (induct_tac list)
apply force
apply (clarsimp)
apply (subgoal_tac "fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (L' \<union> S)) list (L \<union> Serialization_filter_eff a \<sigma> (L' \<union> L)) = fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (L' \<union> S)) list L \<union> Serialization_filter_eff a \<sigma> (L' \<union> L)")
defer
apply (rule_tac list=list and L''="Serialization_filter_eff a \<sigma> (L' \<union> L)"  in fold_union_init)
apply clarsimp
apply (case_tac "l\<in>L")
apply force
apply clarsimp
apply rule
apply (case_tac "l \<in> Serialization_filter_eff a \<sigma> (L' \<union> L)")
apply clarsimp
apply (rule_tac x=0 in exI)
apply clarsimp
apply (clarsimp simp: Let_def)

apply (rule_tac x="Suc i" in exI)
apply (clarsimp simp: Let_def)

lemma " \<forall> x . l \<in> Serialization_filter_eff l' \<sigma> L \<longrightarrow>
                    x \<in> Serialization_filter_eff l \<sigma> L \<longrightarrow>x \<in> Serialization_filter_eff l' \<sigma> L"
apply (rule_tac P = " \<lambda> l' \<sigma> L .\<forall> x .l \<in> Serialization_filter_eff l' \<sigma> L \<longrightarrow>
                    x \<in> Serialization_filter_eff l \<sigma> L \<longrightarrow>x \<in> Serialization_filter_eff l' \<sigma> L" in Serialization_filter_eff.induct)
apply (case_tac "l=la")
apply clarsimp
apply clarsimp
apply (frule Serialization_filter_effD_L)
apply (frule Serialization_filter_effD_L)
apply (drule Serialization_filter_effD_,clarsimp)
apply (elim disjE)
apply clarsimp
apply(thin_tac "(\<And>x2 Value nat. False \<Longrightarrow> x2 = StoredVal (ObjRef nat) \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> l \<in> Serialization_filter_eff nat \<sigma> (insert la L) \<longrightarrow> (\<forall>x. x \<in> Serialization_filter_eff l \<sigma> (insert la L) \<longrightarrow> x \<in> Serialization_filter_eff nat \<sigma> (insert la L))) ")
apply (drule_tac x= "Obj(fields,C)" in meta_spec)
apply (drule_tac x= "fields" in meta_spec)
apply (drule_tac x= C in meta_spec)
apply (rule Serialization_filter_effI_)
apply clarsimp
apply clarsimp

(*
DO NOT DO FOLD TO UNION FIND BETTER
*)

 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>x\<in>ran fields. Referenced_locations_Value x))")
apply (drule_tac SF=Serialization_filter_eff and \<sigma> = \<sigma> and LS ="{la}" and l=la and L="L" in SF_fold_to_Union)
apply clarsimp
apply (drule_tac x= xa in meta_spec)
apply (drule_tac x= "F xa" in meta_spec)
apply clarsimp
apply (rule_tac x=xa in bexI)
apply (drule_tac x=x in spec)
apply clarsimp
apply (erule disjE,simp)

lemma Serialization_filter_effdouble_union[rule_format]: "   
   \<forall>  l'. ( Serialization_filter_eff l \<sigma> L \<subseteq> Serialization_filter_eff l' \<sigma> L \<union> Serialization_filter_eff l \<sigma> (L\<union>Serialization_filter_eff l' \<sigma> L))"
apply (rule_tac P = " \<lambda> l \<sigma> L . \<forall>  l'. ( Serialization_filter_eff l \<sigma> L \<subseteq> Serialization_filter_eff l' \<sigma> L \<union> Serialization_filter_eff l \<sigma> (L\<union>Serialization_filter_eff l' \<sigma> L))" in Serialization_filter_eff.induct)
apply clarsimp
apply (erule contrapos_np)
apply (frule Serialization_filter_effD_L)
apply (frule Serialization_filter_effD_,simp)
apply (elim disjE)
apply clarsimp
apply(thin_tac "       (\<And>x2 Value nat. False \<Longrightarrow> x2 = StoredVal (ObjRef nat) \<Longrightarrow> Value = ObjRef nat \<Longrightarrow> \<forall>l'. Serialization_filter_eff nat \<sigma> (insert l L) \<subseteq> Serialization_filter_eff l' \<sigma> (insert l L) \<union> Serialization_filter_eff nat \<sigma> (insert l (L \<union> Serialization_filter_eff l' \<sigma> (insert l L)))) ")
apply (drule_tac x= "Obj(fields,C)" in meta_spec)
apply (drule_tac x= "fields" in meta_spec)
apply (drule_tac x= C in meta_spec)
apply clarsimp
apply (rule Serialization_filter_effI_)
apply clarsimp


apply (subgoal_tac "\<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I}\<subseteq> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I} \<union> Serialization_filter_eff l \<sigma> (L \<union> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I})")
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


lemma Serialization_filter_effdouble[rule_format]: "   
   \<forall> L' S S' I ll LL. ((S\<subseteq>S'\<and>S'=\<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) | i . i\<in> I})\<longrightarrow>(S\<union>(Serialization_filter_eff l \<sigma> (L\<union>L'\<union>S))\<subseteq> S'\<union>(Serialization_filter_eff l \<sigma> (L\<union>S'))))"
apply (rule_tac P = " \<lambda> l \<sigma> L . \<forall> L' S S' I ll LL. ((S\<subseteq>S'\<and>S'=\<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) | i . i\<in> I})\<longrightarrow>(S\<union>(Serialization_filter_eff l \<sigma> (L\<union>L'\<union>S))\<subseteq> S'\<union>(Serialization_filter_eff l \<sigma> (L\<union>S'))))" in  Serialization_filter_eff.induct)
apply clarsimp
apply rule
apply (subgoal_tac "\<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I}\<subseteq> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I} \<union> Serialization_filter_eff l \<sigma> (L \<union> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I})")
apply (erule Set.subset_trans,simp)
apply blast
(*1*)
apply rule
apply (frule Serialization_filter_effD_L)
apply (frule Serialization_filter_effD_,simp)
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
apply (subgoal_tac "x\<in>\<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I}\<or>x\<in>Serialization_filter_eff l' \<sigma> (insert l (L \<union> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I}))")
apply(case_tac "x \<in> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I}")
apply (blast)
apply clarsimp
apply (subgoal_tac "x \<in> Serialization_filter_eff l \<sigma> (L \<union> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) |i. i \<in> I})")
apply simp
apply (rule Serialization_filter_effI_)
apply clarsimp
apply(subgoal_tac "Serialization_filter_eff l \<sigma> (L \<union> L' \<union> S) ={}")
apply blast
apply(subgoal_tac "l\<in>(L \<union> L' \<union> S)")
apply(thin_tac "x \<in> Serialization_filter_eff l \<sigma> (L \<union> L' \<union> S)")
apply clarsimp
apply(subgoal_tac "l\<in>S")
apply blast
apply (drule_tac c=l in Set.subsetD,simp)
apply (rule Serialization_filter_effI_) 
 apply (simp (no_asm) add: Serialization_filter_eff.simps)
(*1*)
apply (case_tac a, case_tac prod)
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply (rule)
apply (drule Set.Un_mono ,blast,simp)
apply (thin_tac "(\<And>x2 Value nat. ?P x2 Value nat\<Longrightarrow>?Q x2 Value nat \<Longrightarrow>?R x2 Value nat\<Longrightarrow>?U x2 Value nat\<Longrightarrow>?T x2 Value nat)")
apply (drule_tac x="Obj (aaa, ba)" in meta_spec)
apply (drule_tac x=aaa in meta_spec)
apply (drule_tac x=ba in meta_spec)
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply (clarsimp)
apply (case_tac "l\<in>L",simp)
apply (case_tac "l\<in>L'",simp)
apply (case_tac "l\<in>S",simp)
apply (clarsimp simp del: Serialization_filter_eff.simps split: split_if_asm)
apply simp
 apply (subgoal_tac "distinct (sorted_list_of_set
                                              (\<Union>x\<in>ran aaa. Referenced_locations_Value x))")
  apply (drule_tac SF=Serialization_filter_eff and \<sigma> = \<sigma> and LS ="{l}" and l=l and L="L\<union>L'\<union>S" in SF_fold_to_Union,simp)
apply (clarsimp)
apply (case_tac "x=l",simp)
apply (rule_tac x="(case \<sigma> (ll i) of None \<Rightarrow> {} | Some (Obj obj) \<Rightarrow>  fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (LL i \<union> {ll i} \<union> S)) (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {ll i}
                                                                           | Some (StoredVal null) \<Rightarrow> {ll i} | Some (StoredVal (ObjRef l')) \<Rightarrow> {ll i} \<union> Serialization_filter_eff l' \<sigma> (LL i \<union> {ll i}))" in exI)
apply simp
apply (rule_tac x=i in exI)
apply simp
apply (clarsimp simp del: Serialization_filter_eff.simps )
apply (subgoal_tac "l'\<in>LL i \<or>l'\<in>Serialization_filter_eff (ll i) \<sigma> (LL i)") (* IF WELL FORMEDNESS IS PROVEN*)
apply (elim disjE)
apply (subgoal_tac "l'\<in>Serialization_filter_eff l \<sigma> (L\<union> \<Union>{Serialization_filter_eff (ll i) \<sigma> (LL i) | i . i\<in> I})")
apply (clarsimp  split: split_if_asm)
apply (drule_tac x="(case \<sigma> (ll i) of None \<Rightarrow> {}        
| Some (Obj obj) \<Rightarrow>fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (LL i \<union> {ll i} \<union> S)) (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {ll i}                                                
| Some (StoredVal null) \<Rightarrow> {ll i} | Some (StoredVal (ObjRef l')) \<Rightarrow> {ll i} \<union> Serialization_filter_eff l' \<sigma> (LL i \<union> {ll i}))" in spec)
apply simp
apply (drule_tac x= i in spec)
apply simp
apply (simp (no_asm))
apply (clarsimp simp del: Serialization_filter_eff.simps)
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
  fold (\<lambda>l' S. S \<union> Serialization_filter_eff l' \<sigma> (LL i \<union> {ll i} \<union> S)) (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran (fst obj)))) {ll i}
                                                                                                                 | Some (StoredVal null) \<Rightarrow> {ll i} | Some (StoredVal (ObjRef l')) \<Rightarrow> {ll i} \<union> Serialization_filter_eff l' \<sigma> (LL i \<union> {ll i}))" in exI)
apply (clarsimp simp del: Serialization_filter_eff.simps )
apply (rule_tac x=i in exI)
apply simp

apply clarsimp
apply (drule_tac x="{}" in meta_pec) (*? ? ?*)
apply (case_tac "l\<in>L")
apply simp
apply (clarsimp simp del: Serialization_filter_eff.simps)
 apply (clarsimp split: option.splits Storable.splits)
apply (clarsimp split: Value.splits)
apply bast
sorry


(*induction useful\<Or>? (\<And>l \<sigma> L a b S L'.
        l \<notin> L \<Longrightarrow> l \<notin> L' \<Longrightarrow> \<sigma> l = Some (Obj (a,b)) \<Longrightarrow> 
          (\<forall> x\<in>\<Union>(Referenced_locations_Value`(ran a)). (\<forall> L'. 
                          (Serialization_filter_eff x \<sigma> (L\<union>L'\<union>{l}\<union>(S x))) \<subseteq>(Serialization_filter_eff x \<sigma> (L\<union>{l}\<union>(S x))))) \<Longrightarrow>
            ({l}\<union>(\<Union> ((\<lambda> x. Serialization_filter_eff x \<sigma> (L\<union>L' \<union> {l}\<union>S x))` 
                                             \<Union>(Referenced_locations_Value`ran(a)))))\<subseteq> ({l}\<union>(\<Union> ((\<lambda> x. Serialization_filter_eff x \<sigma> ((L) \<union> {l}\<union>S x))` 
                                             \<Union>(Referenced_locations_Value`ran(a))))) )  \<Longrightarrow>
(\<And>l \<sigma> L l' L'.
        l \<notin> L\<Longrightarrow> l\<notin> L' \<Longrightarrow> \<sigma> l = Some (StoredVal (ObjRef l')) \<Longrightarrow>
           \<forall> L'. (Serialization_filter_eff l' \<sigma> (L\<union>L'\<union>{l}))\<subseteq> ( (Serialization_filter_eff l' \<sigma> (L\<union>{l})) )\<Longrightarrow>
           (({l}\<union>(Serialization_filter_eff l' \<sigma> (L\<union>L'\<union>{l})))\<subseteq>  ({l}\<union>(Serialization_filter_eff l' \<sigma> ((L)\<union>{l}))) ))         \<Longrightarrow>   
*)
lemma " S \<subseteq> S' \<Longrightarrow> \<sigma> l = Some (Obj (aaa, ba)) \<Longrightarrow>
                   (\<And>x xa. l \<notin> L \<Longrightarrow> x \<in> set (sorted_list_of_set (\<Union>x\<in>ran aaa. Referenced_locations_Value x)) \<Longrightarrow>
                                      \<forall>L' S S'. S \<subseteq> S' \<longrightarrow> S \<subseteq> S' \<union> Serialization_filter_eff x \<sigma> (insert l (L \<union> xa \<union> S')) \<and>
                                                            Serialization_filter_eff x \<sigma> (insert l (L \<union> xa \<union> L' \<union> S)) \<subseteq> S' \<union> Serialization_filter_eff x \<sigma> (insert l (L \<union> xa \<union> S'))) \<Longrightarrow>
                   x \<in> Serialization_filter_eff l \<sigma> (L \<union> L' \<union> S) \<Longrightarrow> x \<notin> Serialization_filter_eff l \<sigma> (L \<union> S') \<Longrightarrow> x \<in> S'"
apply(induct_tac list)
apply force
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply (rotate_tac -1,frule_tac x="(La \<union> Serialization_filter_eff a \<sigma> (L  \<union> La))" in spec)
apply (drule_tac x="(La \<union> Serialization_filter_eff a \<sigma> (L\<union>L'  \<union> La))" in spec)
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply auto
apply (case_tac "\<sigma> l'")
sorry
lemma Serialization_filter_effdouble[rule_format]: "   
   \<forall> L'. (Serialization_filter_eff l \<sigma> (L\<union>L'))\<subseteq> (Serialization_filter_eff l \<sigma> (L))"
apply (rule_tac P = " \<lambda> l \<sigma> L . \<forall> L'. (Serialization_filter_eff l \<sigma> (L\<union>L'))\<subseteq> (Serialization_filter_eff l \<sigma> (L))" in  Serialization_filter_eff.induct)
apply (clarsimp simp del: Serialization_filter_eff.simps)
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

lemma Serialization_2_excluded_set_subset: "\<forall> L . L\<subseteq>L' \<longrightarrow> Serialization_filter_eff l \<sigma> L' \<subseteq> Serialization_filter_eff l \<sigma> L"
apply (rule_tac P= "\<lambda> S l \<sigma> L'. (\<forall>L. L\<subseteq>L' \<longrightarrow> S \<subseteq> Serialization_filter_eff l \<sigma> L)" in   Serialization_filter_eff1)
apply clarsimp
apply (clarsimp split: Value.splits)
apply blast
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply rule
apply (subgoal_tac "l\<notin>La")
apply (clarsimp split: Value.splits Storable.splits)
apply (rule l_in_fold_union_selection_empty)
apply blast
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply (drule_tac x=xa in bspec,blast) 
apply (drule_tac x=xb in bspec,blast) 
apply (drule_tac x="insert l (La \<union> S xb)" in spec)
apply (clarsimp simp del: Serialization_filter_eff.simps)
apply (erule impE, blast)

apply clarsimp
apply (rule)
apply (force split: Value.splits )
apply (clarsimp split: split_if )
apply blast
apply clarsimp
apply (subgoal_tac "distinct (sorted_list_of_set (\<Union>(Referenced_locations_Value ` ran a)))")
apply (drule_tac SF=Serialization_filter_eff  and \<sigma>=\<sigma> and l = l and L = "La" and LS="{l}" in SF_fold_to_Union_what_F)
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
"\<forall> L'. ((serialization_filter l \<sigma> L)  \<subseteq> (Serialization_filter_eff l \<sigma> L') \<union> L \<union> L')"
apply (rule_tac P= 
"\<lambda> S l'' \<sigma> L. \<forall> L'. (S  \<subseteq> (Serialization_filter_eff l'' \<sigma> L') \<union> L \<union> L')" in   serialization_filter1)
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

