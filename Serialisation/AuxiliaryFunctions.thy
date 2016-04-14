 (*  Title:      AuxiliaryFunctions.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014
    Note:       Functions on Maps for Multi-active object formalisation
                Plus generic lemmas (not related to MAO)
*)

chapter {* Auxiliary functions for Multi-ASP *}

theory AuxiliaryFunctions imports Main begin


section{*generic lemmas*}
lemma map_of_zip_empty[rule_format,simp]: "ran (map_of (zip [] Y)) = {}"
by auto
lemma map_of_zip_replicate[rule_format,intro]: "x\<in>set vl \<longrightarrow>map_of (zip vl (replicate (length vl) Y)) x = Some Y"
by (induct_tac vl, auto)

lemma map_of_zip_outside_dom[rule_format,intro]: "x\<notin>set vl \<longrightarrow>map_of (zip vl (replicate (length vl) Y)) x = None"
by (induct_tac vl, auto)

lemma map_of_zip_replicate_simp[rule_format,simp]: 
    "map_of (zip vl (replicate (length vl) Y)) x = (if (x\<in>set vl) then Some Y else None)"
by (case_tac "(x\<in>set vl)",  auto simp: map_of_zip_replicate map_of_zip_outside_dom)

lemma map_of_zip_replicate_map_simp[rule_format,simp]: 
    "map_of (zip (map f vl) (replicate (length vl) Y)) x = (if (x\<in>set (map f vl)) then Some Y else None)"
apply (subgoal_tac "length vl = length (map f vl)")
apply (erule ssubst)
apply (simp only: map_of_zip_replicate_simp)
apply simp
done

lemma ran_map_of_zip_repl: "ran (map_of (zip (v#vl) (replicate (length (v#vl)) Y))) = {Y}"
by (auto simp: ran_def)
lemma ran_map_of_zip_2: "N=length L\<Longrightarrow>if (N=0) then ran (map_of (zip L (replicate N Y))) = {} else ran (map_of (zip L (replicate N Y))) = {Y}"
by (cases, auto simp: ran_def)


lemma ran_update: "ran (M(x\<mapsto>V)) \<subseteq> ran M \<union> {V}"
by (auto simp: ran_def)

lemma map_of_zip: "length xs=length ys \<Longrightarrow>(x \<in> set xs) = (\<exists>y\<in>set ys. map_of (zip xs ys) x = Some y)"
apply (induct rule: list_induct2)
apply (auto)
apply (drule Map.map_of_zip_is_None,auto)
done

lemma ran_map_of_zip: "map_of (zip xs ys) x = Some y \<Longrightarrow>length xs=length ys \<Longrightarrow>y\<in>set ys"
by (frule map_of_zip_is_Some, drule map_of_zip, auto)

primrec allTrue_list
where
  "allTrue_list Nil = True" |
  "allTrue_list (a#L) = (a\<and>allTrue_list L)"

lemma allTrue_list_nth: "allTrue_list L =(\<forall>n<length L. L!n)"
apply (induct_tac L)
apply auto
apply (case_tac n, auto)
done
(* abbreviation allTrue_list
where
"allTrue_list L \<equiv>\<forall>n<length L. L!n" *)

lemma allTrue_list_set: "allTrue_list L \<Longrightarrow>a\<in>set L \<Longrightarrow> a"
by (induct L,auto)
lemma allTrue_list_set_map: "allTrue_list (map f L) \<Longrightarrow>a\<in>set L \<Longrightarrow> f a"
by (induct L,auto)

lemma foldr_Un_larger: "x\<in> foldr (op \<union>) L (L') \<Longrightarrow> x \<in> foldr (op \<union>) L (a \<union> L')"
by (induct L, auto)
lemma foldr_Un_mapI[intro]: " {N} \<in> f ` set L \<Longrightarrow> N \<in> foldr op \<union> (map f L) S"
by (induct L, auto)

lemma foldr_Un_other: "x\<in> a \<Longrightarrow> x \<in> foldr (op \<union>) L (a \<union> L')"
by (induct L, auto)

lemma foldr_Un_init[rule_format]: "\<forall> L . x\<in>L \<longrightarrow>x\<in> fold (\<lambda>x S. S \<union> F x S) list L"
by (induct list, auto)

lemma foldr_Un_mapD :
"x \<in> foldr op \<union> (map f L) {} \<Longrightarrow> \<exists>y\<in>set L. x\<in>f y" 
by (induct L, auto)

lemma foldr_Un_Union[simp] :
"foldr op \<union> (map f L) {} = \<Union>(set (map f L))" 
by (induct L, auto)
(*SIMPLIFY ? ? ?  *)

lemma Map_restrict_Some: "(m|`A) x = Some y \<Longrightarrow> x\<in>A"
apply (erule contrapos_pp)
apply force
done

lemma ran_and_dom: "ran f = the`f`dom f  "
apply (auto simp: ran_def dom_def)
apply (subgoal_tac "x=the (f a) ")
apply blast
apply force
done

lemma sorted_list_of_set_card_length: " finite S \<Longrightarrow> card S = length (sorted_list_of_set S)"
apply (erule Finite_Set.finite_induct)
apply auto
done

lemma insortI_x: "x\<in>set (insort x L)"
apply (induct_tac L)
apply auto
done

lemma insortI_L[rule_format]: "x\<in>set L \<longrightarrow>x\<in>set (insort y L)"
apply (induct_tac L)
apply auto
done

lemma insortD[rule_format]: "y\<in>set (insort x L)\<longrightarrow>(y=x\<or>y\<in>set L)"
apply (induct_tac L)
apply auto
done


lemma sorted_list_of_set_nthI[rule_format]: " finite S \<Longrightarrow>x\<in>S \<longrightarrow>(\<exists> n<card S . (sorted_list_of_set S)!n = x) "
apply (erule Finite_Set.finite_induct)
apply (force)
apply (case_tac "x=xa",simp)
apply (insert insortI_x [of x])
apply (drule_tac x="(sorted_list_of_set F)" in meta_spec)
apply (drule sorted_list_of_set_card_length)
apply ( clarsimp simp: set_conv_nth)
apply force
apply clarsimp
apply (insert insortI_L)
apply (drule_tac x=x in meta_spec)+
apply (drule_tac x="(sorted_list_of_set F)" in meta_spec)+
apply (drule_tac x=xa in meta_spec)+
apply (erule meta_impE)
apply (clarsimp simp: set_conv_nth)
apply (rule_tac x=n in exI,simp)
apply (drule sorted_list_of_set_card_length,simp)
apply (clarsimp simp: set_conv_nth)
apply (rule_tac x=ia in exI,simp)
apply (drule sorted_list_of_set_card_length,simp)
done

lemma sorted_list_of_set_nthD[rule_format]: " finite S \<Longrightarrow> n<card S \<longrightarrow>(sorted_list_of_set S)!n = x \<longrightarrow>x\<in>S "
apply (erule Finite_Set.finite_induct)
apply clarsimp
apply clarsimp
apply (case_tac "x=xa")
apply simp
apply simp
apply (subgoal_tac "x \<in> set (insort xa (sorted_list_of_set F) )")
apply (drule insortD)
apply force
apply (clarsimp simp: set_conv_nth)
apply (rule_tac x=n in exI,simp)
apply (drule sorted_list_of_set_card_length,simp)
done

lemma UNION_eqI: " \<forall>x\<in>A.  \<exists>z\<in>C. B x = D z \<Longrightarrow> \<forall>z\<in>C. \<exists>x\<in>A.  B x = D z \<Longrightarrow>(\<Union>x\<in>A. B x) = (\<Union>z\<in>C. D z)"
apply auto
apply (drule_tac x=xa in bspec)
apply auto
apply (drule_tac x=z in bspec)
apply auto
done

lemma UNION_UNION_eqI: " \<forall>x\<in>A. \<forall> y\<in>F x. \<exists>z\<in>C. B y = D z \<Longrightarrow> \<forall>z\<in>C. \<exists>x\<in>A. \<exists> y\<in> F x. B y = D z \<Longrightarrow>(\<Union>x\<in>A.\<Union>y\<in>F x. B y) = (\<Union>z\<in>C. D z)"
apply auto
apply (drule_tac x=xa in bspec)
apply simp
apply (drule_tac x=y in bspec)
apply auto
apply (drule_tac x=z in bspec)
apply auto
apply blast
done

lemma map_le_eq: "dom \<sigma> \<subseteq> dom \<sigma>'\<Longrightarrow> \<sigma>=(\<sigma>'|`(dom \<sigma>) )  \<Longrightarrow> \<sigma> \<subseteq>\<^sub>m \<sigma>'"
apply  (auto simp: map_le_def Map.restrict_map_def)
apply (drule_tac x=a in  fun_cong)
apply (auto split: split_if_asm)
done


section{* Specific functions*}

definition
  remove_from_map :: "('a\<rightharpoonup> 'b) => 'a  => ('a \<rightharpoonup> 'b)"  (infixl "|``"  110) where
  "m|``x = m|`(dom m - {x})"

definition listunionMap:: "('a \<Rightarrow> 'b set) \<Rightarrow> ('a list) \<Rightarrow> 'b set"
where
  "listunionMap f l \<equiv> (foldr (op  \<union>) (map f l) {})"

lemma listunionMap_Empty[simp]: "listunionMap f [] = {}"
by (auto simp: listunionMap_def)

(*
lemma listunionMap_Empty_fun[simp]: "listunionMap (\<lambda>x.{}) (L::'a list) = {}"
apply (induct_tac L)
apply (auto simp: listunionMap_def)
done
*)

lemma listunionMap_Empty_fun[simp]: "listunionMap (\<lambda>x.{}) (L::'a list) = {}"
by (induct L, auto simp: listunionMap_def)
lemma listunionMap_Single[simp]: "listunionMap f [x] = f x"
by ( auto simp: listunionMap_def)

lemma listunionMap_Cons[simp]: "listunionMap f (x#L) = (f x) \<union> (listunionMap f L)"
by ( auto simp: listunionMap_def)

end
