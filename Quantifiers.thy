subsection \<open> Quantifying lenses \<close>

theory Quantifiers
  imports Liberation
begin

definition ex_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "ex_expr x e = (\<lambda> s. (\<exists> v. e (put\<^bsub>x\<^esub> s v)))"

definition ex1_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "ex1_expr x e = (\<lambda> s. (\<exists>! v. e (put\<^bsub>x\<^esub> s v)))"

definition all_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "all_expr x e = (\<lambda> s. (\<forall> v. e (put\<^bsub>x\<^esub> s v)))"

expr_constructor ex_expr (1)
expr_constructor ex1_expr (1)
expr_constructor all_expr (1)

syntax 
  "_ex_expr"  :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<Zspot> _" [0, 20] 20)
  "_ex1_expr" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<exists>\<^sub>1 _ \<Zspot> _" [0, 20] 20)
  "_all_expr" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<Zspot> _" [0, 20] 20)

translations
  "_ex_expr x P" == "CONST ex_expr x P"
  "_ex1_expr x P" == "CONST ex1_expr x P"
  "_all_expr x P" == "CONST all_expr x P"

lemma ex_is_liberation: "mwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> P) = (P \\ $x)"
  by (expr_auto, metis mwb_lens_weak weak_lens.put_get)

lemma ex_unrest_iff: "\<lbrakk> mwb_lens x \<rbrakk> \<Longrightarrow> ($x \<sharp> P) \<longleftrightarrow> (\<exists> x \<Zspot> P) = P"
  by (simp add: ex_is_liberation unrest_liberate_iff)

lemma ex_unrest: "\<lbrakk> mwb_lens x; $x \<sharp> P \<rbrakk> \<Longrightarrow> (\<exists> x \<Zspot> P) = P"
  using ex_unrest_iff by blast

lemma unrest_ex_in [unrest]:
  "\<lbrakk> mwb_lens y; x \<subseteq>\<^sub>L y \<rbrakk> \<Longrightarrow> $x \<sharp> (\<exists> y \<Zspot> P)"
  by (simp add: ex_expr_def sublens_pres_mwb sublens_put_put unrest_lens)

lemma unrest_ex_out [unrest]:
  "\<lbrakk> mwb_lens x; $x \<sharp> P; x \<bowtie> y \<rbrakk> \<Longrightarrow> $x \<sharp> (\<exists> y \<Zspot> P)"
  by (simp add: ex_expr_def unrest_lens, metis lens_indep.lens_put_comm)

lemma ex_as_subst: "vwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> e) = (\<exists> v. e\<lbrakk>\<guillemotleft>v\<guillemotright>/x\<rbrakk>)\<^sub>e"
  by expr_auto

lemma ex_twice [simp]: "mwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> \<exists> x \<Zspot> P) = (\<exists> x \<Zspot> P)"
  by (expr_simp)

lemma ex_commute [simp]: "x \<bowtie> y \<Longrightarrow> (\<exists> x \<Zspot> \<exists> y \<Zspot> P) = (\<exists> y \<Zspot> \<exists> x \<Zspot> P)"
  by (expr_auto, metis lens_indep_comm)+
  
lemma ex_true [simp]: "(\<exists> x \<Zspot> (True)\<^sub>e) = (True)\<^sub>e"
  by expr_simp

lemma ex_false [simp]: "(\<exists> x \<Zspot> (False)\<^sub>e) = (False)\<^sub>e"
  by (expr_simp)

lemma ex_disj [simp]: "(\<exists> x \<Zspot> (P \<or> Q)\<^sub>e) = ((\<exists> x \<Zspot> P) \<or> (\<exists> x \<Zspot> Q))\<^sub>e"
  by (expr_auto)

lemma ex_plus:
  "(\<exists> (y,x) \<Zspot> P) = (\<exists> x \<Zspot> \<exists> y \<Zspot> P)"
  by (expr_auto)

lemma all_as_ex: "(\<forall> x \<Zspot> P) = (\<not> (\<exists> x \<Zspot> \<not> P))\<^sub>e"
  by (expr_auto)

lemma ex_as_all: "(\<exists> x \<Zspot> P) = (\<not> (\<forall> x \<Zspot> \<not> P))\<^sub>e"
  by (expr_auto)

end
