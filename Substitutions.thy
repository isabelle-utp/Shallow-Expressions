section \<open> Substitutions \<close>

theory Substitutions
  imports Unrestriction
begin

type_synonym ('s\<^sub>1, 's\<^sub>2) psubst = "'s\<^sub>1 \<Rightarrow> 's\<^sub>2"
type_synonym 's subst = "'s \<Rightarrow> 's"

definition subst_nil :: "('s\<^sub>1, 's\<^sub>2) psubst" ("nil\<^sub>s") 
  where [expr_defs]: "nil\<^sub>s = (\<lambda> s. undefined)"

definition subst_id :: "'s subst" ("id\<^sub>s") 
  where [expr_defs]: "subst_id = (\<lambda>s. s)"

definition subst_app :: "'s subst \<Rightarrow> ('a, 's) expr \<Rightarrow> ('a, 's) expr" (infix "\<dagger>" 65) 
  where [expr_defs]: "subst_app \<sigma> e = (\<lambda> s. e (\<sigma> s))"

definition subst_upd :: "'s subst \<Rightarrow> ('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's subst"
  where [expr_defs]: "subst_upd \<sigma> x e = (\<lambda> s. put\<^bsub>x\<^esub> (\<sigma> s) (e s))"

definition subst_lookup :: "('s\<^sub>1,'s\<^sub>2) psubst \<Rightarrow> ('a \<Longrightarrow> 's\<^sub>2) \<Rightarrow> ('a, 's\<^sub>1) expr" ("\<langle>_\<rangle>\<^sub>s")
  where [expr_defs]: "\<langle>\<sigma>\<rangle>\<^sub>s x = (\<lambda> s. get\<^bsub>x\<^esub> (\<sigma> s))"

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
  "_smaplet"  :: "[svid, logic] => smaplet"             ("_ /\<mapsto>\<^sub>s/ _")
  ""          :: "smaplet => smaplets"            ("_")
  "_SMaplets" :: "[smaplet, smaplets] => smaplets" ("_,/ _")
  "_SubstUpd" :: "[logic, smaplets] => logic" ("_/'(_')" [900,0] 900)
  "_Subst"    :: "smaplets => logic"            ("(1[_])")
  "_PSubst"   :: "smaplets => logic"            ("(1\<lparr>_\<rparr>)")
  "_psubst"   :: "[logic, svars, uexprs] \<Rightarrow> logic"
  "_subst"    :: "logic \<Rightarrow> uexprs \<Rightarrow> svids \<Rightarrow> logic" ("(_\<lbrakk>_'/_\<rbrakk>)" [990,0,0] 991)
  "_uexprs"   :: "[logic, uexprs] => uexprs" ("_,/ _")
  ""          :: "logic => uexprs" ("_")
  "_par_subst" :: "logic \<Rightarrow> salpha \<Rightarrow> salpha \<Rightarrow> logic \<Rightarrow> logic" ("_ [_|_]\<^sub>s _" [100,0,0,101] 101)
    
translations
  "_SubstUpd m (_SMaplets xy ms)"     == "_SubstUpd (_SubstUpd m xy) ms"
  "_SubstUpd m (_smaplet x y)"        == "CONST subst_upd m x (y)\<^sub>e"
  "_Subst ms"                         == "_SubstUpd id\<^sub>s ms"
  "_Subst (_SMaplets ms1 ms2)"        <= "_SubstUpd (_Subst ms1) ms2"
  "_PSubst ms"                        == "_SubstUpd nil\<^sub>s ms"
  "_PSubst (_SMaplets ms1 ms2)"       <= "_SubstUpd (_PSubst ms1) ms2"
  "_SMaplets ms1 (_SMaplets ms2 ms3)" <= "_SMaplets (_SMaplets ms1 ms2) ms3"
  "_subst P es vs" => "CONST subst_app (_psubst id\<^sub>s vs es) P"
  "_psubst m (_svid_list x xs) (_uexprs v vs)" => "_psubst (_psubst m x v) xs vs"
  "_psubst m x v"  => "CONST subst_upd m x (v)\<^sub>e"
  "_subst P v x" <= "CONST subst_app (CONST subst_upd id\<^sub>s x (v)\<^sub>e) P"
  "_par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2" == "CONST par_subst \<sigma>\<^sub>1 A B \<sigma>\<^sub>2"

subsection \<open> Substitution Laws \<close>

named_theorems usubst and usubst_eval

lemma subst_unrest [usubst]:
  "\<lbrakk> vwb_lens x; &x \<sharp> v \<rbrakk> \<Longrightarrow> \<sigma>(x \<mapsto>\<^sub>s e) \<dagger> v = \<sigma> \<dagger> v"
  by (auto simp add: expr_defs fun_eq_iff)
     (metis lens_override_def lens_scene_override mwb_lens_def var_alpha_def vwb_lens_mwb weak_lens.put_get)

lemma subst_lookup_id [usubst]: "\<langle>id\<^sub>s\<rangle>\<^sub>s x = var x"
  by (simp add: expr_defs)

lemma subst_id_var: "id\<^sub>s = (&\<^bold>v)\<^sub>e"
  by (simp add: expr_defs lens_defs)

lemma subst_upd_id_lam [usubst]: "subst_upd (&\<^bold>v)\<^sub>e x v = subst_upd id\<^sub>s x v"
  by (simp add: subst_id_var)

lemma subst_id [simp]: "id\<^sub>s \<circ> \<sigma> = \<sigma>" "\<sigma> \<circ> id\<^sub>s = \<sigma>"
  by (auto simp add: expr_defs)

lemma subst_lookup_one_lens [usubst]: "\<langle>\<sigma>\<rangle>\<^sub>s 1\<^sub>L = \<sigma>"
  by (simp add: expr_defs lens_defs)

(* FIXME: Figure out how to make laws like this parse and simplify *)

expr_ctr subst_app

term "(f (\<sigma> \<dagger> e))\<^sub>e"

term "(\<forall> x. x + &y > &z)\<^sub>e"

term "(\<forall> k. P\<lbrakk>\<guillemotleft>k\<guillemotright>/x\<rbrakk>)\<^sub>e"

lemma subst_var [usubst]: "\<sigma> \<dagger> (&x)\<^sub>e = \<langle>\<sigma>\<rangle>\<^sub>s x"
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
  shows "\<langle>\<sigma>(x \<mapsto>\<^sub>s v)\<rangle>\<^sub>s x = (v)\<^sub>e"
  using assms by (simp add: expr_defs)

text \<open> Substitution update is idempotent. \<close>

lemma usubst_upd_idem [usubst]:
  assumes "mwb_lens x"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, x \<mapsto>\<^sub>s v) = \<sigma>(x \<mapsto>\<^sub>s v)"
  using assms by (simp add: expr_defs)

lemma usubst_upd_idem_sub [usubst]:
  assumes "x \<subseteq>\<^sub>L y" "mwb_lens y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v)"
  using assms by (simp add: expr_defs assms fun_eq_iff sublens_put_put)

text \<open> Substitution updates commute when the lenses are independent. \<close>
    
lemma usubst_upd_comm:
  assumes "x \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v) = \<sigma>(y \<mapsto>\<^sub>s v, x \<mapsto>\<^sub>s u)"
  using assms unfolding subst_upd_def
  by (auto simp add: subst_upd_def assms comp_def lens_indep_comm)

lemma usubst_upd_comm2:
  assumes "z \<bowtie> y"
  shows "\<sigma>(x \<mapsto>\<^sub>s u, y \<mapsto>\<^sub>s v, z \<mapsto>\<^sub>s s) = \<sigma>(x \<mapsto>\<^sub>s u, z \<mapsto>\<^sub>s s, y \<mapsto>\<^sub>s v)"
  using assms unfolding subst_upd_def
  by (auto simp add: subst_upd_def assms comp_def lens_indep_comm)

lemma usubst_upd_var_id [usubst]:
  "vwb_lens x \<Longrightarrow> [x \<mapsto>\<^sub>s &x] = id\<^sub>s"
  by (simp add: subst_upd_def subst_id_def id_lens_def SEXP_def)

subsection \<open> Evaluation \<close>

lemma subst_SEXP [usubst_eval]: "\<sigma> \<dagger> [\<lambda> s. e s]\<^sub>e = [\<lambda> s. e (\<sigma> s)]\<^sub>e"
  by (simp add: SEXP_def subst_app_def fun_eq_iff)

lemma get_subst_id [usubst_eval]: "get\<^bsub>x\<^esub> (id\<^sub>s s) = get\<^bsub>x\<^esub> s"
  by (simp add: subst_id_def)

lemma get_subst_upd_same [usubst_eval]: "weak_lens x \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma>(x \<mapsto>\<^sub>s e)) s) = e s"
  by (simp add: subst_upd_def SEXP_def)

lemma get_subst_upd_indep [usubst_eval]: 
  "x \<bowtie> y \<Longrightarrow> get\<^bsub>x\<^esub> ((\<sigma>(y \<mapsto>\<^sub>s e)) s) = get\<^bsub>x\<^esub> (\<sigma> s)"
  by (simp add: subst_upd_def)

end