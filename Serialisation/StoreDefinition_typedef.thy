(*  Title:      Store_typedef.thy
    Author:     Ludovic Henrio and Florian Kammuller
                2014

    Note:       Store definition for Multi-active object formalisation
                where we introduce a typedef of finite maps inspired by
                "./Library/FinFun_Syntax" but adapted to the Map type
                to additionally achieve the advantages of Maps like
                big theorem library and nice syntac plus pattern matching
                via option
    *)
theory StoreDefinition_typedef imports Main AuxiliaryFunctions  begin

type_synonym Location = nat
type_synonym VarName =  string
type_synonym ClassName = string

datatype Value = null | ObjRef Location  (* Other values can be added here *)

type_synonym  Object = "(VarName \<rightharpoonup> Value) * ClassName"

datatype Storable = Obj Object | StoredVal Value (* Other storables can be added here *)


(* This definition is inspired by the finfun datatype but
  the existentially quantified default value b is set to None 
  thereby amalgamating the advantages of finfun with the pragmatism of 
  the Map tyoe (and thus options and pattern matching) *)
typedef ('a, 'b) fmap =  "{f :: 'a  \<rightharpoonup> 'b. finite(dom f)}" 
morphisms fmap_apply Abs_fmap
apply (rule_tac x = empty in exI)
by simp

type_notation (xsymbols) "fmap" (infixr  "\<rightharpoonup>\<^sub>f" 0)

(* This abbreviation corresponds exactly to fmap_apply but name and 
   syntax is more intuitive in certain situations *)
abbreviation mapoffmap:: "('a \<rightharpoonup>\<^sub>f 'b) \<Rightarrow> 'a \<rightharpoonup> 'b" ("_\<^sub>f")
where "mapoffmap \<equiv> fmap_apply"

definition dom_f :: "('a  \<rightharpoonup>\<^sub>f 'b) \<Rightarrow> 'a set" ("dom\<^sub>f _")
where "dom\<^sub>f m \<equiv> dom((m)\<^sub>f)"

lemma domf_Some_eq: "(\<exists> y. (f :: 'a \<rightharpoonup>\<^sub>f 'b)\<^sub>f x = Some(y)) = (x \<in> dom\<^sub>f f)"
by (simp add: dom_f_def dom_def)

lemma domf_Some_dom[simp]: "((f :: 'a \<rightharpoonup>\<^sub>f 'b)\<^sub>f x = Some(y)) \<Longrightarrow> (x \<in> dom\<^sub>f f)"
by (simp add: dom_f_def dom_def)

lemma empty_dom: "x \<notin> (dom\<^sub>f Abs_fmap empty)" 
by (simp add: Abs_fmap_inverse dom_f_def)

lemma eq_inj: "(\<And> x y. (f x = f y) = (x = y)) \<Longrightarrow> inj f" 
apply (rule injI)
by force

lemma mapoffmap_inj: "inj mapoffmap"
apply (insert fmap_apply_inject)
by (erule eq_inj)

lemma inj_inverse: "inj f \<Longrightarrow> (inv f)(f x) = x"
by (erule inv_f_f)

lemma fmap_apply_inv: "inv(fmap_apply) (fmap_apply f) = f"
apply (rule inv_f_f)
by (rule mapoffmap_inj)

lemma mapoffmap_inv: "inv(mapoffmap) (mapoffmap f) = f"
apply (rule inv_f_f)
by (rule mapoffmap_inj)

thm "fmap_apply"
thm "fmap_apply_inverse"

lemma fmap_apply_injectE1[rule_format]: "((x :: 'a \<rightharpoonup>\<^sub>f 'b)\<^sub>f = (y  :: 'a \<rightharpoonup>\<^sub>f 'b)\<^sub>f \<longrightarrow> x = y)"
apply (insert fmap_apply_inject)
apply (drule_tac x = x in meta_spec)
apply (drule_tac x = y in meta_spec)
by simp

lemma fmap_apply_injectE2[rule_format]: "(x = y \<longrightarrow> (x :: 'a \<rightharpoonup>\<^sub>f 'b)\<^sub>f = (y  :: 'a \<rightharpoonup>\<^sub>f 'b)\<^sub>f )"
apply (insert fmap_apply_inject)
apply (drule_tac x = x in meta_spec)
apply (drule_tac x = y in meta_spec)
by simp


lemma Abs_fmap_inverse1: "finite (dom f) \<Longrightarrow> mapoffmap (Abs_fmap f) = f"
apply (rule Abs_fmap_inverse)
by (erule CollectI)


lemma Abs_fmap_inverse_ex1: "finite (dom f) \<Longrightarrow> (? g. fmap_apply g = f)"
apply (drule Abs_fmap_inverse1)
apply (erule subst)
by (rule exI, rule refl)

lemma Abs_fmap_inverse_ex2: "finite (dom f) \<Longrightarrow> (? g. mapoffmap g = f)"
apply (drule Abs_fmap_inverse1)
apply (erule subst)
by (rule exI, rule refl)


lemma Abs_inv: "finite (dom f) \<Longrightarrow> inv(fmap_apply) f = Abs_fmap f"
apply (drule Abs_fmap_inverse_ex1)
apply (erule exE)
apply (erule subst)
by (simp add: fmap_apply_inverse mapoffmap_inv)

lemma domf_dom: "finite (dom f) \<Longrightarrow> dom\<^sub>f(Abs_fmap(f)) = dom f"
by (simp add: Abs_fmap_inverse dom_f_def)

lemma finite_dom_Repfmap: "finite(dom ((f)\<^sub>f))"
apply (insert fmap_apply)
by force

lemma finite_dom_fmap: "finite(dom\<^sub>f m)"
apply (simp add: dom_f_def)
by (rule finite_dom_Repfmap)

type_synonym Store = "Location \<rightharpoonup>\<^sub>f Storable"

lemma finite_dom_Store : "finite (dom\<^sub>f (\<sigma>::Store))"
by (rule finite_dom_fmap)

setup_lifting type_definition_fmap

notation fmap_apply (infixl "$" 999)

definition fmap_subset :: "['a \<rightharpoonup>\<^sub>f 'b, 'a \<rightharpoonup>\<^sub>f 'b] \<Rightarrow> bool" ("_ \<subseteq>\<^sub>f _")
where "f \<subseteq>\<^sub>f g \<equiv> (f)\<^sub>f \<subseteq>\<^sub>m (g)\<^sub>f"

end
