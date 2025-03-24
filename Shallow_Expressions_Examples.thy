section \<open> Examples of Shallow Expressions \<close>

theory Shallow_Expressions_Examples
  imports Shallow_Expressions
begin

subsection \<open> Basic Expressions and Queries \<close>

text \<open> We define some basic variables using the @{command alphabet} command, process some simple
  expressions, and then perform some unrestriction queries and substitution transformations. \<close>

lit_vars

alphabet st =
  v1 :: int
  v2 :: int
  v3 :: string

term "(v1 > a)\<^sub>e"

full_exprs

term "(v1 > a)\<^sub>e"

pretty_exprs

lemma "$v2 \<sharp> (v1 > 5)\<^sub>e"
  by unrest

lemma "(v1 > 5)\<^sub>e\<lbrakk>v2/v1\<rbrakk> = (v2 > 5)\<^sub>e"
  by subst_eval 

text \<open> We can define an expression using the command below, which automatically performs expression
  lifting. \<close>

expression v1_is_big over st is "v1 > 100"

expression inc_v1 over "st \<times> st" is "v1\<^sup>> = v1\<^sup>< + 1"

subsection \<open> Hierarchical State \<close>

alphabet person =
  name :: string
  age  :: nat

alphabet company =
  adam :: person
  bella :: person
  carol :: person

term "($adam:age > $carol:age)\<^sub>e"

term "($adam:name \<noteq> $bella:name)\<^sub>e"

subsection \<open> Program Semantics \<close>

text \<open> We give a predicative semantics to a simple imperative programming language with sequence,
  conditional, and assignment, using lenses and shallow expressions. We then use these definitions
  to prove some basic laws of programming. \<close>

expr_vars

type_synonym 's prog = "'s \<times> 's \<Rightarrow> bool"

definition seq :: "'s prog \<Rightarrow> 's prog \<Rightarrow> 's prog" (infixr ";;" 85) where
[expr_defs]: "seq P Q = (\<exists> s. P\<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<^sup>>\<rbrakk> \<and> Q\<lbrakk>\<guillemotleft>s\<guillemotright>/\<^bold>v\<^sup><\<rbrakk>)\<^sub>e"

definition ifthenelse :: "(bool, 's) expr \<Rightarrow> 's prog \<Rightarrow> 's prog \<Rightarrow> 's prog" ("IF _ THEN _ ELSE _" [0, 0, 84] 84) where
[expr_defs]: "ifthenelse p C D = (if p\<^sup>< then C else D)\<^sub>e"

definition assign :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr \<Rightarrow> 's prog" ("_ ::= _" [86, 87] 87) where
[expr_defs]: "assign x e = ($x\<^sup>> = e\<^sup>< \<and> \<^bold>v\<^sup>> \<simeq>\<^bsub>\<guillemotleft>x\<guillemotright>\<^esub> \<^bold>v\<^sup><)\<^sub>e"

lemma seq_assoc: "P ;; (Q ;; R) = (P ;; Q) ;; R"
  by expr_auto

lemma assign_twice:
  assumes "mwb_lens x"
  shows "x ::= e ;; x ::= f = x ::= f\<lbrakk>e/x\<rbrakk>"
  using assms
  apply expr_simp
  apply (metis mwb_lens.put_put mwb_lens_weak weak_lens.put_get)
  done

lemma assign_commute:
  assumes "mwb_lens x" "mwb_lens y" "x \<bowtie> y" "$y \<sharp> e" "$x \<sharp> f"
  shows "(x ::= e ;; y ::= f) = (y ::= f ;; x ::= e)"
  using assms
  apply expr_simp
  apply auto
  apply (metis lens_indep_def mwb_lens_weak weak_lens.put_get)+
  done

end