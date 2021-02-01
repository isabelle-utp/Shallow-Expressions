theory Variables
  imports "Optics.Optics"
begin

no_notation   
  Set.member ("op :") and
  Set.member ("(_/ : _)" [51, 51] 50)

text \<open> Variables can also be used to effectively define sets of variables. Here we define the
  the universal alphabet ($\Sigma$) to be the bijective lens @{term "1\<^sub>L"}. This characterises
  the whole of the source type, and thus is effectively the set of all alphabet variables. \<close>

definition univ_var :: "('\<alpha> \<Longrightarrow> '\<alpha>)" where
[lens_defs]: "univ_var = 1\<^sub>L"

definition univ_alpha :: "'s scene" where
[lens_defs]: "univ_alpha = \<top>\<^sub>S"

definition emp_alpha :: "'s scene" where
[lens_defs]: "emp_alpha = \<bottom>\<^sub>S"

definition var_alpha :: "('a \<Longrightarrow> 's) \<Rightarrow> 's scene" where
[lens_defs]: "var_alpha x = lens_scene x"

definition ns_alpha :: "('b \<Longrightarrow> 'c) \<Rightarrow> ('a \<Longrightarrow> 'b) \<Rightarrow> 'a \<Longrightarrow> 'c" where
[lens_defs]: "ns_alpha a x = x ;\<^sub>L a"

definition res_alpha :: "('a \<Longrightarrow> 'b) \<Rightarrow> ('c \<Longrightarrow> 'b) \<Rightarrow> 'a \<Longrightarrow> 'c" where
[lens_defs]: "res_alpha x a = x /\<^sub>L a"

lemma idem_scene_var [simp]:
  "vwb_lens x \<Longrightarrow> idem_scene (var_alpha x)"
  by (simp add: lens_defs)

lemma not_member_var_alpha [simp]: 
  "\<lbrakk> vwb_lens y; x \<bowtie> y \<rbrakk> \<Longrightarrow> x \<notin>\<^sub>S (var_alpha y)"
  by (simp add: lens_indep_comm lens_member_def lens_override_def lens_scene_override scene_override_commute var_alpha_def)

text \<open> In order to support nice syntax for variables, we here set up some translations. The first
  step is to introduce a collection of non-terminals. \<close>
  
nonterminal svid and svids and salpha

text \<open> These non-terminals correspond to the following syntactic entities. Non-terminal 
  @{typ "svid"} is an atomic variable identifier, and @{typ "svids"} is a list of identifier. 
  @{typ "salpha"} is an alphabet or set of variables. Such sets can 
  be constructed only through lens composition due to typing restrictions. Next we introduce some 
  syntax constructors. \<close>
   
syntax \<comment> \<open> Identifiers \<close>
  "_svid"         :: "id_position \<Rightarrow> svid" ("_" [999] 999)
  "_svlongid"     :: "longid_position \<Rightarrow> svid" ("_" [999] 999)
  ""              :: "svid \<Rightarrow> svids" ("_")
  "_svid_list"    :: "svid \<Rightarrow> svids \<Rightarrow> svids" ("_,/ _")
  "_svid_alpha"   :: "svid" ("\<^bold>v")
  "_svid_tuple"   :: "svids \<Rightarrow> svid" ("'(_')")
  "_svid_dot"     :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_:_" [999,998] 998)
  "_svid_res"     :: "svid \<Rightarrow> svid \<Rightarrow> svid" ("_\<restriction>_" [999,998] 998)
  "_svid_fst"     :: "svid \<Rightarrow> svid" ("_\<^sup>\<lhd>" [997] 997)
  "_svid_snd"     :: "svid \<Rightarrow> svid" ("_\<^sup>\<rhd>" [997] 997)
  "_mk_svid_list" :: "svids \<Rightarrow> logic" \<comment> \<open> Helper function for summing a list of identifiers \<close>
  "_svid_view"    :: "logic \<Rightarrow> svid" ("\<V>[_]") \<comment> \<open> View of a symmetric lens \<close>
  "_svid_coview"  :: "logic \<Rightarrow> svid" ("\<C>[_]") \<comment> \<open> Coview of a symmetric lens \<close>

text \<open> A variable can be decorated with an ampersand, to indicate it is a predicate variable, with 
  a dollar to indicate its an unprimed relational variable, or a dollar and ``acute'' symbol to 
  indicate its a primed relational variable. Isabelle's parser is extensible so additional
  decorations can be and are added later. \<close>

syntax \<comment> \<open> Variable sets \<close>
  "_salphaid"    :: "id_position \<Rightarrow> salpha" ("_" [990] 990)
  "_salphavar"   :: "svid \<Rightarrow> salpha" ("$_" [990] 990)
  "_salphaparen" :: "salpha \<Rightarrow> salpha" ("'(_')")
  "_salphacomp"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr ";" 75)
  "_salphaprod"  :: "salpha \<Rightarrow> salpha \<Rightarrow> salpha" (infixr "\<times>" 85)
  "_salphacompl" :: "salpha \<Rightarrow> salpha" ("- _" [81] 80)
  "_salpha_all"  :: "salpha" ("\<Sigma>")
  "_salpha_none" :: "salpha" ("\<emptyset>")
  "_salphaset"   :: "svids \<Rightarrow> salpha" ("{_}")
  "_salphamk"    :: "logic \<Rightarrow> salpha"
  "_mk_alpha_list" :: "svids \<Rightarrow> logic"

text \<open> The terminals of an alphabet are either HOL identifiers or UTP variable identifiers. 
  We support two ways of constructing alphabets; by composition of smaller alphabets using
  a semi-colon or by a set-style construction $\{a,b,c\}$ with a list of UTP variables. \<close>

syntax \<comment> \<open> Quotations \<close>
  "_svid_set"    :: "svids \<Rightarrow> logic" ("{_}\<^sub>v")
  "_svid_empty"  :: "logic" ("{}\<^sub>v")
  "_svar"        :: "svid \<Rightarrow> logic" ("'(_')\<^sub>v")
  
text \<open> For various reasons, the syntax constructors above all yield specific grammar categories and
  will not parser at the HOL top level (basically this is to do with us wanting to reuse the syntax
  for expressions). As a result we provide some quotation constructors above. 

  Next we need to construct the syntax translations rules. Finally, we set up the translations rules. \<close>

translations
  \<comment> \<open> Identifiers \<close>
  "_svid x" \<rightharpoonup> "x"
  "_svlongid x" \<rightharpoonup> "x"
  "_svid_alpha" \<rightleftharpoons> "CONST univ_var"
  "_svid_tuple xs" \<rightharpoonup> "_mk_svid_list xs"
  "_svid_dot x y" \<rightleftharpoons> "CONST ns_alpha x y"
  "_svid_res x y" \<rightleftharpoons> "x /\<^sub>L y" 
  "_svid_fst x" \<rightleftharpoons> "_svid_dot fst\<^sub>L x"
  "_svid_snd x" \<rightleftharpoons> "_svid_dot snd\<^sub>L x"
  "_mk_svid_list (_svid_list x xs)" \<rightharpoonup> "x +\<^sub>L _mk_svid_list xs"
  "_mk_svid_list x" \<rightharpoonup> "x"
  "_mk_alpha_list (_svid_list x xs)" \<rightharpoonup> "CONST var_alpha x \<squnion>\<^sub>S _mk_alpha_list xs"
  "_mk_alpha_list x" \<rightharpoonup> "CONST var_alpha x"

  "_svid_view a" => "\<V>\<^bsub>a\<^esub>"
  "_svid_coview a" => "\<C>\<^bsub>a\<^esub>"

  \<comment> \<open> Alphabets \<close>
  "_salphaparen a" \<rightharpoonup> "a"
  "_salphaid x" \<rightharpoonup> "x"
  "_salphacomp x y" \<rightharpoonup> "x \<squnion>\<^sub>S y"
  "_salphacompl x"  \<rightharpoonup> "- x"
(*  "_salphaprod a b" \<rightleftharpoons> "a \<times>\<^sub>L b" *)
  "_salphavar x" \<rightleftharpoons> "CONST var_alpha x"
  "_salphaset A" \<rightharpoonup> "_mk_alpha_list A"  
  "(_svid_list x (_salphamk y))" \<leftharpoondown> "_salphamk (x +\<^sub>L y)" 
  "x" \<leftharpoondown> "_salphamk x"
  "_salpha_all" \<rightleftharpoons> "CONST univ_alpha"
  "_salpha_none" \<rightleftharpoons> "CONST emp_alpha"

  \<comment> \<open> Quotations \<close>
  "_svid_set A" \<rightharpoonup> "_mk_alpha_list A"
  "_svid_empty" \<rightharpoonup> "0\<^sub>L"
  "_svar x" \<rightharpoonup> "x"

text \<open> The translation rules mainly convert syntax into lens constructions, using a mixture
  of lens operators and the bespoke variable definitions. Notably, a colon variable identifier
  qualification becomes a lens composition, and variable sets are constructed using len sum. 
  The translation rules are carefully crafted to ensure both parsing and pretty printing. 

  Finally we create the following useful utility translation function that allows us to construct a 
  UTP variable (lens) type given a return and alphabet type. \<close>

syntax
  "_uvar_ty"      :: "type \<Rightarrow> type \<Rightarrow> type"

parse_translation \<open>
let
  fun uvar_ty_tr [ty] = Syntax.const @{type_syntax lens} $ ty $ Syntax.const @{type_syntax dummy}
    | uvar_ty_tr ts = raise TERM ("uvar_ty_tr", ts);
in [(@{syntax_const "_uvar_ty"}, K uvar_ty_tr)] end
\<close>

end