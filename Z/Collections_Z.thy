section \<open> Collections from Z Toolkit \<close>

theory Collections_Z
  imports "Shallow_Expressions.Collections" "Z_Toolkit.Relation_Lib"
begin

subsection \<open> Partial Function Collection Lens \<close>

definition pfun_collection_lens :: "'a \<Rightarrow> 'b \<Longrightarrow> 'a \<Zpfun> 'b" where
[lens_defs]: "pfun_collection_lens = pfun_lens"

adhoc_overloading collection_lens \<rightleftharpoons> pfun_collection_lens

lemma pfun_collection_lens_mwb [simp]: "mwb_lens (pfun_collection_lens e)"
  by (simp add: pfun_collection_lens_def)

lemma source_pfun_collection_lens: "\<S>\<^bsub>pfun_collection_lens i\<^esub> = {f. i \<in> pdom(f)}"
  by (auto simp add: lens_defs lens_source_def, metis pfun_upd_ext)

lemma defined_pfun_collection_lens [simp, code_unfold]: 
  "\<lbrakk> vwb_lens x; $x \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> \<^bold>D(x[e]) = (e \<in> pdom($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_pfun_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV)

lemma lens_defined_pfun_code [code_unfold]: 
  "vwb_lens x \<Longrightarrow> lens_defined (ns_alpha x (pfun_collection_lens i)) = (\<guillemotleft>i\<guillemotright> \<in> pdom($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_pfun_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV)

subsection \<open> Finite Function Collection Lens \<close>

definition ffun_collection_lens :: "'a \<Rightarrow> 'b \<Longrightarrow> 'a \<Zffun> 'b" where
[lens_defs]: "ffun_collection_lens = ffun_lens"

adhoc_overloading collection_lens \<rightleftharpoons> ffun_collection_lens

lemma ffun_collection_lens_mwb [simp]: "mwb_lens (ffun_collection_lens e)"
  by (simp add: ffun_collection_lens_def)

lemma source_ffun_collection_lens: "\<S>\<^bsub>ffun_collection_lens i\<^esub> = {f. i \<in> fdom(f)}"
  by (auto simp add: lens_defs lens_source_def, metis ffun_upd_ext)

lemma defined_ffun_collection_lens [simp, code_unfold]: 
  "\<lbrakk> vwb_lens x; $x \<sharp> (e)\<^sub>e \<rbrakk> \<Longrightarrow> \<^bold>D(x[e]) = (e \<in> fdom($x))\<^sub>e"
  by (simp add: lens_defined_def src_dyn_lens unrest source_ns_alpha source_ffun_collection_lens)
     (simp add: lens_defs wb_lens.source_UNIV)

end