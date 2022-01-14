section \<open> Z Stores \<close>

theory Z_Store
  imports "Shallow-Expressions.EDefinitions" "Z_Toolkit.Relation_Lib"
  keywords "zstore" :: "thy_decl_block"
begin

text \<open> This theory creates a command for adding Z-like state schemas. It creates both an alphabet,
  which can be used in program constructions, and an associated locale that groups together
  a set of assumptions. \<close>

named_theorems z_defs and z_locale_defs

ML_file \<open>Z_Store.ML\<close>

end