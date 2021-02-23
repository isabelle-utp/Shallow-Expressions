section \<open> Extension and Restriction \<close>

theory Extension
  imports Substitutions
begin

definition saext :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>2, 's\<^sub>1) psubst" where
[expr_defs]: "saext a = get\<^bsub>a\<^esub>"

definition sares :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) psubst" where
[expr_defs]: "sares a = create\<^bsub>a\<^esub>"

abbreviation "aext P a \<equiv> subst_app (saext a) P"
abbreviation "ares P a \<equiv> subst_app (sares a) P"

expr_ctr aext
expr_ctr ares

syntax 
  "_aext" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<up>" 80)
  "_ares" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<down>" 80)
  "_pre"  :: "logic \<Rightarrow> logic" ("_\<^sup><" [999] 1000)
  "_post" :: "logic \<Rightarrow> logic" ("_\<^sup>>" [999] 1000)

translations
  "_aext P a" == "CONST aext (P)\<^sub>e a"
  "_ares P a" == "CONST ares (P)\<^sub>e a"
  "_pre P" == "_aext P fst\<^sub>L"
  "_post P" == "_aext P snd\<^sub>L"

lemma aext_var: "$x \<up> a = ($a:x)\<^sub>e"
  by (simp add: expr_defs lens_defs)

lemma ares_aext: "weak_lens a \<Longrightarrow> P \<up> a \<down> a = P"
  by (simp add: expr_defs)

lemma aext_ares: "\<lbrakk> mwb_lens a; (- $a) \<sharp> P \<rbrakk> \<Longrightarrow> P \<down> a \<up> a = P"
  unfolding unrest_compl_lens
  by (auto simp add: expr_defs fun_eq_iff lens_create_def)

lemma expr_pre [simp]: "e\<^sup>< (s\<^sub>1, s\<^sub>2) = (e)\<^sub>e s\<^sub>1"
  by (simp add: saext_def subst_app_def)

lemma expr_post [simp]: "e\<^sup>> (s\<^sub>1, s\<^sub>2) = (@e)\<^sub>e s\<^sub>2"
  by (simp add: saext_def subst_app_def)

end
