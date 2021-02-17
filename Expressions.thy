section \<open> Expressions \<close>

theory Expressions
  imports Variables
  keywords "pretty_exprs" "full_exprs" "lit_vars" "expr_vars" "expr_ctr" :: "thy_decl_block"
begin

subsection \<open> Types and Constructs \<close>

named_theorems expr_defs

text \<open> An expression is represented simply as a function from the state space @{typ "'s"} to
  the return type @{typ "'a"}, which is the simplest shallow model for Isabelle/HOL. 

  The aim of this theory is to provide transparent conversion between this representation 
  and a more intuitive expression syntax. For example, an expression @{term "x + y"} where 
  $x$ and $y$ are both state variables, can be represented by @{term "\<lambda> s. get\<^bsub>x\<^esub> s + get\<^bsub>y\<^esub> s"} 
  when both variables are modelled using lenses. Rather than having to write $\lambda$-terms 
  directly, it is more convenient to hide this threading of state behind a parser.
\<close>

type_synonym ('a, 's) expr = "'s \<Rightarrow> 'a"

text \<open> The following constructor is used to syntactically mark functions that actually
  denote expressions. It is semantically vacuous. \<close>

definition SEXP :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a, 's) expr" ("[_]\<^sub>e") where
[expr_defs]: "SEXP x = x"

lemma SEXP_apply [simp]: "SEXP e s = (e s)" by (simp add: SEXP_def)

lemma SEXP_idem [simp]: "[[e]\<^sub>e]\<^sub>e = [e]\<^sub>e" by (simp add: SEXP_def)

text \<open> We can create the core constructs of a simple expression language as indicated below. \<close>

abbreviation (input) var :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr" where
"var x \<equiv> (\<lambda> s. get\<^bsub>x\<^esub> s)"

abbreviation (input) lit :: "'a \<Rightarrow> ('a, 's) expr" where
"lit k \<equiv> (\<lambda> s. k)"

abbreviation (input) uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr" where
"uop f e \<equiv> (\<lambda> s. f (e s))"

abbreviation (input) bop 
  :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('c, 's) expr" where
"bop f e\<^sub>1 e\<^sub>2 \<equiv> (\<lambda> s. f (e\<^sub>1 s) (e\<^sub>2 s))"

definition taut :: "(bool, 's) expr \<Rightarrow> bool" where
[expr_defs]: "taut e = (\<forall> s. e s)"

subsection \<open> Lifting Parser and Printer \<close>

text \<open> The lifting parser creates a parser directive that converts an expression to a 
  @{const SEXP} boxed $\lambda$-term that gives it a semantics. A pretty printer converts
  a boxed $\lambda$-term back to an expression. \<close>

ML_file \<open>Lift_Expr_Options.ML\<close>

text \<open> We create a number of commands for configuring the way the parser works. \<close> 

full_exprs
pretty_exprs

text \<open> We can disable pretty printing of $\lambda$ expressions using \textbf{full\_exprs} and
  re-enable pretty printing with \textbf{pretty\_exprs}. \<close>

lit_vars
expr_vars

text \<open> Expressions, of course, can contain variables. However, a variable can denote one of
  three things: (1) a state variable (i.e. a lens); (2) a placeholder for a value (i.e. a
  HOL literal); and (3) a placeholder for another expression. The command \textbf{lit\_vars}
  selects option (2) as the default behaviour, and \textbf{expr\_vars} selects option (3). \<close>

nonterminal sexp

text \<open> Next, we create some syntactic constants and define parse and print translations for
  them. \<close>

syntax
  "_sexp_state"      :: "id"
  "_sexp_quote"      :: "logic \<Rightarrow> logic" ("'(_')\<^sub>e")
  \<comment> \<open> Convert the expression to a lambda term, but do not box it. \<close>
  "_sexp_quote_1way" :: "logic \<Rightarrow> logic" ("'(_')\<^sup>e")
  "_sexp_lit"        :: "logic \<Rightarrow> logic" ("\<guillemotleft>_\<guillemotright>")
  "_sexp_var"        :: "svid \<Rightarrow> logic" ("$_" [990] 990)
  "_sexp_evar"       :: "id_position \<Rightarrow> logic" ("@_" [999] 999)
  "_sexp_pqt"        :: "logic \<Rightarrow> sexp" ("[_]\<^sub>e")
  "_sexp_taut"       :: "logic \<Rightarrow> logic" ("`_`")

ML_file \<open>Lift_Expr.ML\<close>

parse_translation \<open> 
  [(@{syntax_const "_sexp_state"}, fn ctx => fn term => Syntax.free Lift_Expr.state_id),
   (@{syntax_const "_sexp_quote"}
   , fn ctx => fn terms =>
      case terms of
        [Const (@{const_syntax SEXP}, t) $ e] => Const (@{const_name SEXP}, t) $ e |
        [e] =>
            Syntax.const @{const_name SEXP} 
            $ (lambda (Syntax.free Lift_Expr.state_id) 
                      (Lift_Expr.lift_expr ctx (Term_Position.strip_positions e)))),
   (@{syntax_const "_sexp_quote_1way"}
   , fn ctx => fn terms =>
      case terms of
        [e] =>
            (lambda (Syntax.free Lift_Expr.state_id) 
                    (Lift_Expr.lift_expr ctx (Term_Position.strip_positions e))))]
\<close>

print_translation \<open>
  [(@{const_syntax "SEXP"}
   , fn ctx => fn ts =>
     if (FullExprs.get (Proof_Context.theory_of ctx)) 
     then Term.list_comb (Syntax.const @{syntax_const "_sexp_pqt"}, ts)
     else
     Syntax.const @{syntax_const "_sexp_quote"} 
     $ Lift_Expr.print_expr ctx (betapply ((hd ts), Syntax.const @{syntax_const "_sexp_state"})))]
\<close>

translations
  "_sexp_var x" => "get\<^bsub>x\<^esub> _sexp_state"
  "_sexp_taut p" == "CONST taut (p)\<^sub>e"

text \<open> The main directive is the $e$ subscripted brackets, @{term "(e)\<^sub>e"}. This converts the 
  expression $e$ to a boxed $\lambda$ term. Essentially, the parser behaviour is as follows:

  \begin{enumerate}
    \item a new $\lambda$ abstraction over the state variable $s$ is wrapped around $e$;
    \item every occurrence of free lens @{term "$x"} in $e$ is replace by @{term "get\<^bsub>x\<^esub> s"};
    \item every occurrence of an expression variable @{term "e"} is replaced by @{term "e s"}.
  \end{enumerate}

  The pretty printer does this in reverse. Some examples follow. For now, we turn of the 
  pretty printer so that we can see the results of the parser.
\<close>

full_exprs

term "(f + g)\<^sub>e"
term "(f + g)\<^sup>e"

text \<open> The default behaviour of our parser is to recognise identifiers as expression variables.
  So, the above expression becomes the term @{term "[\<lambda>\<s>. f \<s> + g \<s>]\<^sub>e"}. We can easily change
  this: \<close>

lit_vars

term "(f + g)\<^sub>e"

text \<open> Now, @{term f} and @{term g} are both parsed as literals, and so the term is 
  @{term "[\<lambda>\<s>. f + g]\<^sub>e"}. Alternatively, we could have a lens in the expression: \<close>

term "($x + g)\<^sub>e"

text \<open> This gives the term @{term "[\<lambda>\<s>. get\<^bsub>x\<^esub> \<s> + g]\<^sub>e"}. Although we have default behaviours
  for parsing, we can use different markup to coerce identifiers to particular variable kinds. \<close>

term "($x + @g)\<^sub>e"

text \<open> This gives @{term "[\<lambda>\<s>. get\<^bsub>x\<^esub> \<s> + g \<s>]\<^sub>e"}, the we have requested that @{term "g"} is 
  treated as an expression variable. We can do similar with literal, as show below. \<close>

term "(f + \<guillemotleft>x\<guillemotright>)\<^sub>e"

text \<open> Some further examples follow. \<close>

term "(\<guillemotleft>f\<guillemotright> (@e))\<^sub>e"

term "(@f + @g)\<^sub>e"

term "(@x)\<^sub>e"

term "SEXP(\<lambda> \<s>. get\<^bsub>x\<^esub> \<s> + e \<s> + v)"


term "(v \<in> $xs \<union> ($f) ys \<union> {} \<and> @e)\<^sub>e"

pretty_exprs
expr_vars

term "($x\<^sup>< = $x\<^sup>>)\<^sub>e"

text \<open> The pretty printer works even when we don't use the parser, as shown below. \<close>

term "[\<lambda> \<s>. get\<^bsub>x\<^esub> \<s> + e \<s> + v]\<^sub>e"

subsection \<open> Reasoning \<close>

lemma expr_eq_iff: "P = Q \<longleftrightarrow> `P = Q`"
  by (simp add: taut_def fun_eq_iff)

lemma refine_iff_implies: "P \<le> Q \<longleftrightarrow> `P \<longrightarrow> Q`"
  by (simp add: le_fun_def taut_def)

lemma taut_True [simp]: "`True` = True"
  by (simp add: taut_def)

lemma taut_False [simp]: "`False` = False"
  by (simp add: taut_def)

method expr_simp uses add = (simp add: expr_defs alpha_splits lens_defs add fun_eq_iff)
method expr_auto uses add = (expr_simp, (auto)?)

end