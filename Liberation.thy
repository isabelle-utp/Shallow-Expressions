subsection \<open> Liberation \<close>

theory Liberation
  imports Extension
begin

consts liberate :: "'p \<Rightarrow> 's scene \<Rightarrow> 'p"

definition liberate_expr :: "('s \<Rightarrow> bool) \<Rightarrow> 's scene \<Rightarrow> ('s \<Rightarrow> bool)" where
[expr_defs]: "liberate_expr P x = (\<lambda> s. \<exists> s'. P (s \<oplus>\<^sub>S s' on x))"

adhoc_overloading liberate liberate_expr

syntax
  "_liberate" :: "logic \<Rightarrow> salpha \<Rightarrow> logic" (infixl "\\" 80)

translations
  "_liberate P x" == "CONST liberate P x"

expr_ctr liberate

lemma liberate_lens [expr_simps]: 
  "mwb_lens x \<Longrightarrow> P \\ $x = (\<lambda>s. \<exists>s'. P (s \<triangleleft>\<^bsub>x\<^esub> s'))"
  by (simp add: liberate_expr_def)

lemma unrest_liberate: "a \<sharp> P \\ a"
  by (expr_simp)

lemma unrest_liberate_iff: "(a \<sharp> P) \<longleftrightarrow> (P \\ a = P)"
  by (expr_simp, metis (full_types) scene_override_overshadow_left)

lemma liberate_none [simp]: "P \\ \<emptyset> = P"
  by (expr_simp)

lemma liberate_idem [simp]: "P \\ a \\ a = P \\ a"
  by (expr_simp)

lemma liberate_commute [simp]: "a \<bowtie>\<^sub>S b \<Longrightarrow> P \\ a \\ b = P \\ b \\ a"
  using scene_override_commute_indep by (expr_auto, fastforce+)

lemma liberate_false [simp]: "(False)\<^sub>e \\ a = (False)\<^sub>e"
  by (expr_simp)

lemma liberate_disj [simp]: "(P \<or> Q)\<^sub>e \\ a = (P \\ a \<or> Q \\ a)\<^sub>e"
  by (expr_auto)

end