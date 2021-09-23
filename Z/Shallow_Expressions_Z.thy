section \<open> Shallow Expressions with Z \<close>

theory Shallow_Expressions_Z
  imports 
    "Shallow-Expressions.Shallow_Expressions" 
    "Z_Toolkit.Relation_Lib"
    Collections_Z
begin 

text \<open> Allow substitution maplets to be written in a Z-like way. \<close>

syntax "_zmaplet" :: "[svid, logic] => smaplet" ("_\<Zprime> = _")
translations "_zmaplet x e" => "_smaplet x e"

end