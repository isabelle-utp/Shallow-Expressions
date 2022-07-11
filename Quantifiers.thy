subsection \<open> Quantifying lenses \<close>

theory Quantifiers
  imports Liberation
begin

consts ex_lens  :: "('a \<Longrightarrow> 's) \<Rightarrow> 'p \<Rightarrow> 'p"
consts ex1_lens :: "('a \<Longrightarrow> 's) \<Rightarrow> 'p \<Rightarrow> 'p"
consts all_lens :: "('a \<Longrightarrow> 's) \<Rightarrow> 'p \<Rightarrow> 'p"

expr_ctr ex_lens (1)
expr_ctr ex1_lens (1)
expr_ctr all_lens (1)

syntax 
  "_ex_lens"  :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<exists> _ \<Zspot> _" [0, 20] 20)
  "_ex1_lens" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<exists>\<^sub>1 _ \<Zspot> _" [0, 20] 20)
  "_all_lens" :: "svid \<Rightarrow> logic \<Rightarrow> logic" ("\<forall> _ \<Zspot> _" [0, 20] 20)

translations
  "_ex_lens x P" == "CONST ex_lens x P"
  "_ex1_lens x P" == "CONST ex1_lens x P"
  "_all_lens x P" == "CONST all_lens x P"

definition ex_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "ex_expr x e = (\<lambda> s. (\<exists> v. e (put\<^bsub>x\<^esub> s v)))"

definition ex1_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "ex1_expr x e = (\<lambda> s. (\<exists>! v. e (put\<^bsub>x\<^esub> s v)))"

definition all_expr :: "('a \<Longrightarrow> 's) \<Rightarrow> (bool, 's) expr \<Rightarrow> (bool, 's) expr" where
[expr_defs]: "all_expr x e = (\<lambda> s. (\<forall> v. e (put\<^bsub>x\<^esub> s v)))"

adhoc_overloading
  ex_lens ex_expr and
  ex1_lens ex1_expr and
  all_lens all_expr

lemma ex_is_liberation: "mwb_lens x \<Longrightarrow> (\<exists> x \<Zspot> P) = (P \\ $x)"
  by (expr_auto, metis mwb_lens_weak weak_lens.put_get)

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

lemma all_as_ex: "(\<forall> x \<Zspot> P) = (\<not> (\<exists> x \<Zspot> \<not> P))\<^sub>e"
  by (expr_auto)

lemma ex_as_all: "(\<exists> x \<Zspot> P) = (\<not> (\<forall> x \<Zspot> \<not> P))\<^sub>e"
  by (expr_auto)

end
