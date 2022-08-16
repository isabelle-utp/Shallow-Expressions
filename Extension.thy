section \<open> Extension and Restriction \<close>

theory Extension
  imports Substitutions
begin

subsection \<open> Expressions \<close>

syntax 
  "_aext"      :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<up>" 80)
  "_ares"      :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<down>" 80)
  "_pre"       :: "logic \<Rightarrow> logic" ("_\<^sup><" [999] 1000)
  "_post"      :: "logic \<Rightarrow> logic" ("_\<^sup>>" [999] 1000)
  "_drop_pre"  :: "logic \<Rightarrow> logic" ("_\<^sub><" [999] 1000)
  "_drop_post" :: "logic \<Rightarrow> logic" ("_\<^sub>>" [999] 1000)

translations
  "_aext P a" == "CONST aext P a"
  "_ares P a" == "CONST ares P a"
  "_pre P" == "_aext (P)\<^sub>e fst\<^sub>L"
  "_post P" == "_aext (P)\<^sub>e snd\<^sub>L"
  "_drop_pre P" == "_ares (P)\<^sub>e fst\<^sub>L"
  "_drop_post P" == "_ares (P)\<^sub>e snd\<^sub>L"

expr_constructor aext
expr_constructor ares

lemma aext_var: "($x)\<^sub>e \<up> a = ($a:x)\<^sub>e"
  by (simp add: expr_defs lens_defs)

lemma ares_aext: "weak_lens a \<Longrightarrow> P \<up> a \<down> a = P"
  by (simp add: expr_defs)

lemma aext_ares: "\<lbrakk> mwb_lens a; (- $a) \<sharp> P \<rbrakk> \<Longrightarrow> P \<down> a \<up> a = P"
  unfolding unrest_compl_lens
  by (auto simp add: expr_defs fun_eq_iff lens_create_def)

lemma expr_pre [simp]: "e\<^sup>< (s\<^sub>1, s\<^sub>2) = (e)\<^sub>e s\<^sub>1"
  by (simp add: subst_ext_def subst_app_def)

lemma expr_post [simp]: "e\<^sup>> (s\<^sub>1, s\<^sub>2) = (@e)\<^sub>e s\<^sub>2"
  by (simp add: subst_ext_def subst_app_def)

lemma unrest_aext_expr_lens [unrest]: "\<lbrakk> mwb_lens x; x \<bowtie> a \<rbrakk> \<Longrightarrow> $x \<sharp> (P \<up> a)"
  by (expr_simp add: lens_indep.lens_put_irr2)

subsection \<open> Substitutions \<close>

definition subst_aext :: "'a subst \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'b subst"
  where [expr_defs]: "subst_aext \<sigma> x = (\<lambda> s. put\<^bsub>x\<^esub> s (\<sigma> (get\<^bsub>x\<^esub> s)))"

definition subst_ares :: "'b subst \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'a subst"
  where [expr_defs]: "subst_ares \<sigma> x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> (create\<^bsub>x\<^esub> s)))"

syntax 
  "_subst_aext" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<up>\<^sub>s" 80)
  "_subst_ares" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<down>\<^sub>s" 80)

translations
  "_subst_aext P a" == "CONST subst_aext P a"
  "_subst_ares P a" == "CONST subst_ares P a"

end
