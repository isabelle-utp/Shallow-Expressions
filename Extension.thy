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

expr_ctr aext (1)
expr_ctr ares (1)

syntax 
  "_aext" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<up>" 80)
  "_ares" :: "logic \<Rightarrow> svid \<Rightarrow> logic" (infixl "\<down>" 80)
  "_pre"  :: "logic \<Rightarrow> logic" ("_\<^sup><" [999] 999)
  "_post" :: "logic \<Rightarrow> logic" ("_\<^sup>>" [999] 999)

translations
  "_aext P a" == "CONST aext (P)\<^sub>e a"
  "_ares P a" == "CONST ares (P)\<^sub>e a"
  "_pre P" == "_aext P fst\<^sub>L"
  "_post P" == "_aext P snd\<^sub>L"

lemma ares_aext: "weak_lens a \<Longrightarrow> P \<up> a \<down> a = P"
  by (simp add: expr_defs)

end
