section \<open> Collections \<close>

theory Collections
  imports Substitutions
begin

subsection \<open> Partial Lens Definedness \<close>

definition lens_defined :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "lens_defined x = ($\<^bold>v \<in> \<S>\<^bsub>\<guillemotleft>x\<guillemotright>\<^esub>)\<^sub>e"

syntax "_lens_defined" :: "svid \<Rightarrow> logic" ("\<^bold>D'(_')")
translations "_lens_defined x" == "CONST lens_defined x"

expr_constructor lens_defined

subsection \<open> Dynamic Lenses \<close>

definition dyn_lens :: "('i \<Rightarrow> ('a \<Longrightarrow> 's)) \<Rightarrow> ('s \<Rightarrow> 'i) \<Rightarrow> ('a \<Longrightarrow> 's)" where
[lens_defs]: "dyn_lens f x = \<lparr> lens_get = (\<lambda> s. get\<^bsub>f (x s)\<^esub> s), lens_put = (\<lambda> s v. put\<^bsub>f (x s)\<^esub> s v) \<rparr>"

lemma dyn_lens_mwb [simp]: "\<lbrakk> \<And> i. mwb_lens (f i); \<And> i. $f(i) \<sharp> e \<rbrakk> \<Longrightarrow> mwb_lens (dyn_lens f e)"
  apply (unfold_locales, auto simp add: expr_defs lens_defs lens_indep.lens_put_irr2)
  apply (metis lens_override_def mwb_lens_weak weak_lens.put_get)
  apply (metis lens_override_def mwb_lens.put_put)
  done

lemma ind_lens_vwb [simp]: "\<lbrakk> \<And> i. vwb_lens (f i); \<And> i. $f(i) \<sharp> e \<rbrakk> \<Longrightarrow> vwb_lens (dyn_lens f e)"
  by (unfold_locales, auto simp add: lens_defs expr_defs lens_indep.lens_put_irr2 lens_scene_override)
     (metis mwb_lens_weak vwb_lens_mwb weak_lens.put_get, metis mwb_lens.put_put vwb_lens_mwb)

lemma src_dyn_lens: "\<lbrakk> \<And> i. mwb_lens (f i); \<And> i. $f(i) \<sharp> e \<rbrakk> \<Longrightarrow> \<S>\<^bsub>dyn_lens f e\<^esub> = {s. s \<in> \<S>\<^bsub>f (e s)\<^esub>}"
  by (auto simp add: lens_defs expr_defs lens_source_def lens_scene_override unrest)
     (metis mwb_lens.put_put)+

lemma subst_lookup_dyn_lens [usubst]: "\<lbrakk> \<And> i. f i \<bowtie> x \<rbrakk> \<Longrightarrow> \<langle>subst_upd \<sigma> (dyn_lens f k) e\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (expr_simp, metis (mono_tags, lifting) lens_indep.lens_put_irr2)

lemma get_upd_dyn_lens [usubst_eval]: "\<lbrakk> \<And> i. f i \<bowtie> x \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (subst_upd \<sigma> (dyn_lens f k) e s) = get\<^bsub>x\<^esub> (\<sigma> s)"
  by (expr_simp, metis lens_indep.lens_put_irr2)

subsection \<open> Overloaded Collection Lens \<close>

consts collection_lens :: "'k \<Rightarrow> ('a \<Longrightarrow> 's)"

definition [lens_defs]: "fun_collection_lens = fun_lens"
definition [lens_defs]: "list_collection_lens = list_lens"

adhoc_overloading 
  collection_lens fun_collection_lens and
  collection_lens list_collection_lens  

lemma vwb_fun_collection_lens [simp]: "vwb_lens (fun_collection_lens k)"
  by (simp add: fun_collection_lens_def fun_vwb_lens)

lemma mwb_list_collection_lens [simp]: "mwb_lens (list_collection_lens i)"
  by (simp add: list_collection_lens_def list_mwb_lens)

lemma source_list_collection_lens: "\<S>\<^bsub>list_collection_lens i\<^esub> = {xs. i < length xs}"
  by (simp add: list_collection_lens_def source_list_lens)

subsection \<open> Syntax for Collection Lenses \<close>

abbreviation "dyn_lens_poly f x i \<equiv> dyn_lens (\<lambda> k. ns_alpha x (f k)) i"

syntax
  "_svid_collection" :: "svid \<Rightarrow> logic \<Rightarrow> svid" ("_[_]" [999, 0] 999)

translations
  "_svid_collection x e" == "CONST dyn_lens_poly CONST collection_lens x (e)\<^sub>e"

lemma source_ns_alpha: "\<lbrakk> mwb_lens a; mwb_lens x \<rbrakk> \<Longrightarrow> \<S>\<^bsub>ns_alpha a x\<^esub> = {s \<in> \<S>\<^bsub>a\<^esub>. get\<^bsub>a\<^esub> s \<in> \<S>\<^bsub>x\<^esub>}"
  by (simp add: ns_alpha_def source_lens_comp)

lemma defined_list_collection_lens [simp]:
  "\<lbrakk> vwb_lens x; $x \<sharp> e \<rbrakk> \<Longrightarrow> \<^bold>D(x[e]) = (e < length($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_list_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV)

end