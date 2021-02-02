section \<open> Unrestriction \<close>

theory Unrestriction
  imports Expressions
begin

text \<open> Unrestriction means that an expression does not depend on the value of the state space
  described by the given scene (i.e. set of variables) for its valuation. It is a semantic
  characterisation of fresh variables. \<close>

definition unrest :: "'s scene \<Rightarrow> ('b, 's) expr \<Rightarrow> bool" where
[expr_defs]: "unrest a e = (\<forall> s s'. e (s \<oplus>\<^sub>S s' on a) = e s)"

syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)

translations
  "_unrest x p" == "CONST unrest x (p)\<^sub>e"                                           

named_theorems unrest

lemma unrest_empty [unrest]: "\<emptyset> \<sharp> P"
  by (simp add: expr_defs lens_defs)

lemma unrest_var_union [unrest]:
  "\<lbrakk> x \<sharp> P; y \<sharp> P \<rbrakk> \<Longrightarrow> x;y \<sharp> P"
  by (simp add: expr_defs lens_defs)
     (metis scene_override_union scene_override_unit scene_union_incompat)

lemma unrest_neg_union:
  assumes "A ##\<^sub>S B" "- A \<sharp> P" "- B \<sharp> P"
  shows "(- (A ; B)) \<sharp> P"
  using assms by (simp add: unrest_def scene_override_commute scene_override_union)

lemma unrest_subscene: "\<lbrakk> idem_scene a; a \<sharp> e; b \<subseteq>\<^sub>S a \<rbrakk> \<Longrightarrow> b \<sharp> e"
  by (metis (mono_tags, hide_lams) subscene_eliminate unrest_def)

lemma unrest_lens_comp [unrest]: "\<lbrakk> vwb_lens x; vwb_lens y; $x \<sharp> e \<rbrakk> \<Longrightarrow> $x:y \<sharp> e"
  by (simp add: expr_defs)
     (metis comp_vwb_lens lens_comp_lb ns_alpha_def sublens_iff_subscene subscene_eliminate var_alpha_def vwb_impl_idem_scene)

lemma unrest_lit [unrest]: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (simp add: expr_defs)

lemma unrest_var [unrest]: 
  "\<lbrakk> vwb_lens x; idem_scene a; var_alpha x \<bowtie>\<^sub>S a \<rbrakk> \<Longrightarrow> a \<sharp> $x"
  by (auto simp add: unrest_def scene_indep_override var_alpha_def)
     (metis lens_override_def lens_override_idem lens_scene_override mwb_lens_weak vwb_lens_mwb weak_lens_def)

lemma unrest_var': 
  "x \<notin>\<^sub>S a \<Longrightarrow> a \<sharp> $x"
  by (simp add: unrest_def)

lemma unrest_var_single [unrest]:
  "\<lbrakk> mwb_lens x; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp> $y"
  by (simp add: expr_defs lens_indep.lens_put_irr2 lens_indep_sym lens_override_def lens_scene_override var_alpha_def)

lemma unrest_conj [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<and> Q)"
  by (auto simp add: expr_defs)

lemma unrest_not [unrest]:
  "\<lbrakk> x \<sharp> P \<rbrakk> \<Longrightarrow> x \<sharp> (\<not> P)"
  by (auto simp add: expr_defs)

lemma unrest_disj [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<or> Q)"
  by (auto simp add: expr_defs)

lemma unrest_implies [unrest]:
  "\<lbrakk> x \<sharp> P; x \<sharp> Q \<rbrakk> \<Longrightarrow> x \<sharp> (P \<longrightarrow> Q)"
  by (auto simp add: expr_defs)

lemma unrest_uop:
  "\<lbrakk> x \<sharp> e \<rbrakk> \<Longrightarrow> x \<sharp> \<guillemotleft>f\<guillemotright> e"
  by (auto simp add: expr_defs)

lemma unrest_bop:
  "\<lbrakk> x \<sharp> e\<^sub>1; x \<sharp> e\<^sub>2 \<rbrakk> \<Longrightarrow> x \<sharp> \<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2"
  by (auto simp add: expr_defs)

lemma unrest_trop:
  "\<lbrakk> x \<sharp> e\<^sub>1; x \<sharp> e\<^sub>2; x \<sharp> e\<^sub>3 \<rbrakk> \<Longrightarrow> x \<sharp> \<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2 e\<^sub>3"
  by (auto simp add: expr_defs)

end