section \<open> Shallow Expressions with Z \<close>

theory Shallow_Expressions_Z
  imports 
    "Shallow_Expressions.Shallow_Expressions" 
    "Z_Toolkit.Relation_Lib"
    Collections_Z
    Z_Store
begin 

text \<open> Allow substitution maplets to be written in a Z-like way. \<close>

syntax "_zmaplet" :: "[svid, logic] => smaplet" ("_\<Zprime> = _")
translations "_zmaplet x e" => "_smaplet x e"

lemma ref_by_pred_iff [expr_simps]: "P \<sqsubseteq> Q \<longleftrightarrow> `Q \<longrightarrow> P`"
  by (simp add: ref_by_bool_def ref_by_fun_def taut_def) 

end