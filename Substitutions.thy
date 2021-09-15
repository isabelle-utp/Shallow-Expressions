section \<open> Substitutions \<close>

theory Substitutions
  imports Unrestriction
begin

type_synonym ('s\<^sub>1, 's\<^sub>2) psubst = "'s\<^sub>1 \<Rightarrow> 's\<^sub>2"
type_synonym 's subst = "'s \<Rightarrow> 's"

definition subst_nil :: "('s\<^sub>1, 's\<^sub>2) psubst" ("\<lparr>\<leadsto>\<rparr>") 
  where [expr_defs]: "\<lparr>\<leadsto>\<rparr> = (\<lambda> s. undefined)"

definition subst_id :: "'s subst" ("[\<leadsto>]") 
  where [expr_defs]: "subst_id = (\<lambda>s. s)"

definition subst_default :: "('s\<^sub>1, 's\<^sub>2::default) psubst" ("\<lblot>\<leadsto>\<rblot>") 
  where [expr_defs]: "\<lblot>\<leadsto>\<rblot> = (\<lambda> s. default)"

definition subst_aext :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>2, 's\<^sub>1) psubst" ("_\<^sup>\<up>" [999] 999) where
[expr_defs]: "subst_aext a = get\<^bsub>a\<^esub>"

definition subst_ares :: "('s\<^sub>1 \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) psubst" ("_\<^sub>\<down>" [999] 999) where
[expr_defs]: "subst_ares a = create\<^bsub>a\<^esub>"

consts subst_app :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> 'p\<^sub>1 \<Rightarrow> 'p\<^sub>2"

abbreviation "aext P a \<equiv> subst_app (a\<^sup>\<up>) P"
abbreviation "ares P a \<equiv> subst_app (a\<^sub>\<down>) P"

definition subst_app_expr :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('a, 's\<^sub>2) expr \<Rightarrow> ('a, 's\<^sub>1) expr" 
  where [expr_defs]: "subst_app_expr \<sigma> e = (\<lambda> s. e (\<sigma> s))"

adhoc_overloading subst_app subst_app_expr

definition subst_comp :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('s\<^sub>3, 's\<^sub>1) psubst \<Rightarrow> ('s\<^sub>3, 's\<^sub>2) psubst" (infixl "\<circ>\<^sub>s" 55) 
    where [expr_defs]: "subst_comp = comp"

definition sset :: "'s scene \<Rightarrow> 's \<Rightarrow> 's subst" 
  where [expr_defs]: "sset a s' = (\<lambda> s. s \<oplus>\<^sub>S s' on a)"

syntax "_subst_app" :: "logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<dagger>" 65)

translations
  "_subst_app \<sigma> e" == "CONST subst_app \<sigma> e"
  "_subst_app \<sigma> e" <= "_subst_app \<sigma> (e)\<^sub>e"

definition subst_upd :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('a \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('a, 's\<^sub>1) expr \<Rightarrow> ('s\<^sub>1, 's\<^sub>2) psubst"
  where [expr_defs]: "subst_upd \<sigma> x e = (\<lambda> s. put\<^bsub>x\<^esub> (\<sigma> s) (e s))"

definition subst_lookup :: "('s\<^sub>1, 's\<^sub>2) psubst \<Rightarrow> ('a \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('a, 's\<^sub>1) expr" ("\<langle>_\<rangle>\<^sub>s")
  where [expr_defs]: "\<langle>\<sigma>\<rangle>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> s))"

expr_ctr subst_lookup

definition unrest_usubst :: "('a \<Longrightarrow> 's) \<Rightarrow> 's subst \<Rightarrow> bool" 
  where [expr_defs]: "unrest_usubst x \<sigma> = (\<forall> \<rho> v. \<sigma> (put\<^bsub>x\<^esub> \<rho> v) = put\<^bsub>x\<^esub> (\<sigma> \<rho>) v)"

syntax
  "_unrest_usubst" :: "salpha \<Rightarrow> logic \<Rightarrow> logic \<Rightarrow> logic" (infix "\<sharp>\<^sub>s" 20)

translations
  "_unrest_usubst x p" == "CONST unrest_usubst x p"                                           
  "_unrest_usubst (_salphaset (_salphamk (x +\<^sub>L y))) P"  <= "_unrest_usubst (x +\<^sub>L y) P"

definition par_subst :: "'s subst \<Rightarrow> 's scene \<Rightarrow> 's scene \<Rightarrow> 's subst \<Rightarrow> 's subst"
  where [expr_defs]: "par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2 = (\<lambda> s. (s \<oplus>\<^sub>S (\<sigma>\<^sub>1 s) on A) \<oplus>\<^sub>S (\<sigma>\<^sub>2 s) on B)"

nonterminal uexprs and smaplet and smaplets

syntax
  "_smaplet"        :: "[svid, logic] => smaplet" ("_ \<leadsto>/ _")
  ""                :: "smaplet => smaplets" ("_")
  "_SMaplets"       :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  \<comment> \<open> A little syntax utility to extract a list of variable identifiers from a substitution \<close>
  "_smaplets_svids" :: "smaplets \<Rightarrow> logic"
  "_SubstUpd"       :: "[logic, smaplets] => logic" ("_/'(_')" [900,0] 900)
  "_Subst"          :: "smaplets => logic" ("(1[_])")
  "_PSubst"         :: "smaplets => logic" ("(1\<lparr>_\<rparr>)")
  "_DSubst"         :: "smaplets \<Rightarrow> logic" ("(1\<lblot>_\<rblot>)")
  "_psubst"         :: "[logic, svids, uexprs] \<Rightarrow> logic"
  "_subst"          :: "logic \<Rightarrow> uexprs \<Rightarrow> svids \<Rightarrow> logic" ("(_\<lbrakk>_'/_\<rbrakk>)" [990,0,0] 991)
  "_uexprs"         :: "[logic, uexprs] => uexprs" ("_,/ _")
  ""                :: "logic => uexprs" ("_")
  "_par_subst"      :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>s _" [100,0,0,101] 101)
    
translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x (y)\<^sub>e"
  "_smaplet (_svid_tuple (_of_svid_list (x +\<^sub>L y))) e" <= "_smaplet (x +\<^sub>L y) e"
  "_Subst ms"                         == "_SubstUpd [\<leadsto>] ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_PSubst ms"                        == "_SubstUpd \<lparr>\<leadsto>\<rparr> ms"
  "_PSubst (_SMaplets ms1 ms2)"       <= "_SubstUpd (_PSubst ms1) ms2"
  "_DSubst ms"                        == "_SubstUpd \<lblot>\<leadsto>\<rblot> ms"
  "_DSubst (_SMaplets ms1 ms2)"       <= "_SubstUpd (_DSubst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"
  "_smaplets_svids (_SMaplets (_smaplet x e) ms)" => "x +\<^sub>L (_smaplets_svids ms)"
  "_smaplets_svids (_smaplet x e)" => "x"
  "_subst P es vs" => "CONST subst_app (_psubst [\<leadsto>] vs es) P"
  "_psubst m (_svid_list x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x (v)\<^sub>e"
  "_subst P v x" <= "CONST subst_app (CONST subst_upd [\<leadsto>] x (v)\<^sub>e) P"
  "_subst P v x" <= "_subst (_sexp_quote P)  v x"
  "_subst P v (_svid_tuple (_of_svid_list (x +\<^sub>L y)))" <= "_subst P v (x +\<^sub>L y)"
  "_par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2" == "CONST par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2"

expr_ctr subst_app (1)
expr_ctr subst_id
expr_ctr subst_nil
expr_ctr subst_default
expr_ctr subst_upd

ML_file \<open>Expr_Util.ML\<close>

subsection \<open> Substitution Laws \<close>

named_theorems usubst and usubst_eval

lemma subst_unrest [usubst]:
  "\<lbrakk> vwb_lens x; $x \<sharp> v \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> e) \<dagger> v = \<sigma> \<dagger> v"
  by expr_auto

lemma subst_lookup_id [usubst]: "\<langle>[\<leadsto>]\<rangle>\<^sub>s x = var x"
  by expr_simp

lemma subst_id_var: "[\<leadsto>] = ($\<^bold>v)\<^sub>e"
  by expr_simp

lemma subst_upd_id_lam [usubst]: "subst_upd ($\<^bold>v)\<^sub>e x v = subst_upd [\<leadsto>] x v"
  by expr_simp

lemma subst_id [simp]: "[\<leadsto>] \<circ>\<^sub>s \<sigma> = \<sigma>" "\<sigma> \<circ>\<^sub>s [\<leadsto>] = \<sigma>"
  by expr_auto+

lemma subst_default_id [simp]: "\<lblot>\<leadsto>\<rblot> \<circ>\<^sub>s \<sigma> = \<lblot>\<leadsto>\<rblot>"
  by (simp add: expr_defs comp_def)

lemma subst_lookup_one_lens [usubst]: "\<langle>\<sigma>\<rangle>\<^sub>s 1\<^sub>L = \<sigma>"
  by expr_simp

(* FIXME: Figure out how to make laws like this parse and simplify *)

term "(f (\<sigma> \<dagger> e))\<^sub>e"

term "(\<forall> x. x + $y > $z)\<^sub>e"

term "(\<forall> k. P\<lbrakk>\<guillemotleft>k\<guillemotright>/x\<rbrakk>)\<^sub>e"

lemma subst_var [usubst]: "\<sigma> \<dagger> ($x)\<^sub>e = \<langle>\<sigma>\<rangle>\<^sub>s x"
  by (simp add: expr_defs)

text \<open> We can't use this as simplification unfortunately as the expression structure is too
  ambiguous to support automatic rewriting. \<close>

lemma subst_uop: "\<sigma> \<dagger> (\<guillemotleft>f\<guillemotright> e)\<^sub>e = (\<guillemotleft>f\<guillemotright> (\<sigma> \<dagger> e))\<^sub>e"
  by (simp add: expr_defs)

lemma subst_bop: "\<sigma> \<dagger> (\<guillemotleft>f\<guillemotright> e\<^sub>1 e\<^sub>2)\<^sub>e = (\<guillemotleft>f\<guillemotright> (\<sigma> \<dagger> e\<^sub>1) (\<sigma> \<dagger> e\<^sub>2))\<^sub>e"
  by (simp add: expr_defs)

text \<open> A substitution update naturally yields the given expression. \<close>
    
lemma subst_lookup_upd [usubst]:
  assumes "weak_lens x"
  shows "\<langle>\<sigma>(x \<leadsto> v)\<rangle>\<^sub>s x = (v)\<^sub>e"
  using assms by (simp add: expr_defs)

lemma subst_lookup_upd_diff [usubst]:
  assumes "x \<bowtie> y"
  shows "\<langle>\<sigma>(y \<leadsto> v)\<rangle>\<^sub>s x = \<langle>\<sigma>\<rangle>\<^sub>s x"
  using assms by (simp add: expr_defs)

lemma subst_lookup_pair [usubst]: 
  "\<langle>\<sigma>\<rangle>\<^sub>s (x +\<^sub>L y) = ((\<langle>\<sigma>\<rangle>\<^sub>s x, \<langle>\<sigma>\<rangle>\<^sub>s y))\<^sub>e"
  by (expr_simp)

text \<open> Substitution update is idempotent. \<close>

lemma usubst_upd_idem [usubst]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<leadsto> u, x \<leadsto> v) = \<sigma>(x \<leadsto> v)"
  using assms by (simp add: expr_defs)

lemma usubst_upd_idem_sub [usubst]:
  assumes "x \<subseteq>\<^sub>L y" "mwb_lens y"
  shows "\<sigma>(x \<leadsto> u, y \<leadsto> v) = \<sigma>(y \<leadsto> v)"
  using assms by (simp add: expr_defs assms fun_eq_iff sublens_put_put)

text \<open> Substitution updates commute when the lenses are independent. \<close>
    
lemma usubst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<leadsto> u, y \<leadsto> v) = \<sigma>(y \<leadsto> v, x \<leadsto> u)"
  using assms unfolding subst_upd_def
  by (auto simp add: subst_upd_def assms comp_def lens_indep_comm)

lemma usubst_upd_comm2:
  assumes "z \<bowtie> y"
  shows "\<sigma>(x \<leadsto> u, y \<leadsto> v, z \<leadsto> s) = \<sigma>(x \<leadsto> u, z \<leadsto> s, y \<leadsto> v)"
  using assms unfolding subst_upd_def
  by (auto simp add: subst_upd_def assms comp_def lens_indep_comm)

lemma usubst_upd_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<leadsto> $x] = [\<leadsto>]"
  by (simp add: subst_upd_def subst_id_def id_lens_def SEXP_def)

lemma usubst_upd_pair [usubst]:
  "x \<bowtie> y \<Longrightarrow> \<sigma>((x, y) \<leadsto> (e, f)) = \<sigma>(x \<leadsto> e, y \<leadsto> f)"
  by (simp add: subst_upd_def lens_defs SEXP_def fun_eq_iff lens_indep_comm)

lemma subst_upd_comp [usubst]:
  "\<rho>(x \<leadsto> v) \<circ>\<^sub>s \<sigma> = (\<rho> \<circ>\<^sub>s \<sigma>)(x \<leadsto> \<sigma> \<dagger> v)"
  by (simp add: expr_defs fun_eq_iff)

subsection \<open> Ordering substitutions \<close>

text \<open> A simplification procedure to reorder substitutions maplets lexicographically by variable syntax \<close>

simproc_setup subst_order ("subst_upd (subst_upd \<sigma> x u) y v") =
  \<open> (fn _ => fn ctx => fn ct => 
        case (Thm.term_of ct) of
          Const (@{const_name subst_upd}, _) $ (Const (@{const_name subst_upd}, _) $ s $ x $ u) $ y $ v
            => if (YXML.content_of (Syntax.string_of_term ctx x) > YXML.content_of(Syntax.string_of_term ctx y))
               then SOME (mk_meta_eq @{thm usubst_upd_comm})
               else NONE  |
          _ => NONE) 
  \<close>

subsection \<open> Substitution Unrestriction Laws \<close>

lemma unrest_subst_empty [unrest]: "x \<sharp>\<^sub>s [\<leadsto>]"
  by (expr_simp)

lemma unrest_subst_upd [unrest]: "\<lbrakk> vwb_lens x; x \<bowtie> y; $x \<sharp> (e)\<^sub>e; x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> x \<sharp>\<^sub>s \<sigma>(y \<leadsto> e)"
  by (expr_auto add: lens_indep_comm)

subsection \<open> Conditional Substitution Laws \<close>

lemma usubst_cond_upd_1 [usubst]:
  "\<sigma>(x \<leadsto> u) \<triangleleft> b \<triangleright> \<rho>(x \<leadsto> v) = (\<sigma> \<triangleleft> b \<triangleright> \<rho>)(x \<leadsto> (u \<triangleleft> b \<triangleright> v))"
  by expr_auto

lemma usubst_cond_upd_2 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp>\<^sub>s \<rho> \<rbrakk> \<Longrightarrow> \<sigma>(x \<leadsto> u) \<triangleleft> b \<triangleright> \<rho> = (\<sigma> \<triangleleft> b \<triangleright> \<rho>)(x \<leadsto> (u \<triangleleft> b \<triangleright> ($x)\<^sub>e))"
  by (expr_auto, metis lens_override_def lens_override_idem)

lemma usubst_cond_upd_3 [usubst]:
  "\<lbrakk> vwb_lens x; x \<sharp>\<^sub>s \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> \<triangleleft> b \<triangleright> \<rho>(x \<leadsto> v) = (\<sigma> \<triangleleft> b \<triangleright> \<rho>)(x \<leadsto> (($x)\<^sub>e \<triangleleft> b \<triangleright> v))"
  by (expr_auto, metis lens_override_def lens_override_idem)

subsection \<open> Evaluation \<close>

lemma subst_SEXP [usubst_eval]: "\<sigma> \<dagger> [\<lambda> s. e s]\<^sub>e = [\<lambda> s. e (\<sigma> s)]\<^sub>e"
  by (simp add: SEXP_def subst_app_expr_def fun_eq_iff)

lemma get_subst_id [usubst_eval]: "get\<^bsub>x\<^esub> ([\<leadsto>] s) = get\<^bsub>x\<^esub> s"
  by (simp add: subst_id_def)

lemma get_subst_upd_same [usubst_eval]: "weak_lens x \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma>(x \<leadsto> e)) s) = e s"
  by (simp add: subst_upd_def SEXP_def)

lemma get_subst_upd_indep [usubst_eval]: 
  "x \<bowtie> y \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma>(y \<leadsto> e)) s) = get\<^bsub>x\<^esub> (\<sigma> s)"
  by (simp add: subst_upd_def)

lemma unrest_ssubst: "(a \<sharp> P) \<longleftrightarrow> (\<forall> s'. sset a s' \<dagger> P = (P)\<^sub>e)"
  by (auto simp add: expr_defs fun_eq_iff)
  
lemma get_subst_sset_out [usubst_eval]: "\<lbrakk> vwb_lens x; var_alpha x \<bowtie>\<^sub>S a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (sset a s' s) = get\<^bsub>x\<^esub> s"
  by (simp add: expr_defs var_alpha_def get_scene_override_indep)

lemma get_subst_sset_in [usubst_eval]: "\<lbrakk> vwb_lens x; var_alpha x \<le> a \<rbrakk> \<Longrightarrow> get\<^bsub>x\<^esub> (sset a s' s) = get\<^bsub>x\<^esub> s'"
  by (simp add: get_scene_override_le sset_def var_alpha_def)

lemma get_subst_aext [usubst_eval]: "get\<^bsub>x\<^esub> (subst_aext a s) = get\<^bsub>ns_alpha a x\<^esub> s"
  by (expr_simp)

text \<open> A tactic for proving unrestrictions by evaluating a special kind of substitution. \<close>

method unrest = (simp add: unrest_ssubst var_alpha_combine usubst_eval)

end