theory Unrestriction
  imports Expressions
begin

definition unrest :: "('a \<Longrightarrow> 's) \<Rightarrow> ('b, 's) expr \<Rightarrow> bool" where
[expr_defs]: "unrest x e = (\<forall> s k. e (put\<^bsub>x\<^esub> s k) = e s)"

syntax
  "_unrest" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>" 20)

translations
  "_unrest x p" == "CONST unrest x (p)\<^sub>e"                                           
  "_unrest (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest (x +\<^sub>L y) P"

named_theorems unrest

lemma unrest_var_comp [unrest]:
  "\<lbrakk> x \<sharp> P; y \<sharp> P \<rbrakk> \<Longrightarrow> x;y \<sharp> P"
  by (simp add: expr_defs lens_defs)

lemma unrest_lens_comp [unrest]: "x \<sharp> e \<Longrightarrow> x:y \<sharp> e"
  by (simp add: expr_defs lens_defs)

lemma unrest_lit [unrest]: "x \<sharp> \<guillemotleft>v\<guillemotright>"
  by (simp add: expr_defs)

lemma unrest_var [unrest]:
  "x \<bowtie> y \<Longrightarrow> x \<sharp> &y"
  by (simp add: expr_defs lens_indep.lens_put_irr2)

lemma unrest_uop [unrest]:
  "\<lbrakk> x \<sharp> e \<rbrakk> \<Longrightarrow> x \<sharp> \<guillemotleft>f\<guillemotright> e"
  by (auto simp add: expr_defs)

lemma unrest_bop [unrest]:
  "\<lbrakk> x \<sharp> e\<^sub>1; x \<sharp> e\<^sub>2 \<rbrakk> \<Longrightarrow> x \<sharp> \<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2"
  by (auto simp add: expr_defs)

lemma unrest_trop [unrest]:
  "\<lbrakk> x \<sharp> e\<^sub>1; x \<sharp> e\<^sub>2; x \<sharp> e\<^sub>3 \<rbrakk> \<Longrightarrow> x \<sharp> \<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2 e\<^sub>3"
  by (auto simp add: expr_defs)

end