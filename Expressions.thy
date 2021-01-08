theory Expressions
  imports Variables
  keywords "pretty_exprs" "full_exprs" "lit_vars" "expr_vars" "expr_ctr" :: "thy_decl_block"
begin

named_theorems expr_defs

text \<open> An expression is represented simply as a function from the state space @{typ "'s"} to
  the return type @{typ "'a"}, which is the simplest shallow model for Isabelle/HOL. 

  The aim of this theory is to provide transparent conversion between this representation 
  and a more intuitive expression syntax. For example, an expression @{term "x + y"} where 
  $x$ and $y$ are both state variables, can be represented by @{term "\<lambda> s. get\<^bsub>x\<^esub> s + get\<^bsub>y\<^esub> s"} 
  when both variables are modelled using lenses. Rather than having to write $\lambda$-terms 
  directly, it is more convenient to hide this threading of state behind a parser. \<close>

type_synonym ('a, 's) expr = "'s \<Rightarrow> 'a"

definition SEXP :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a, 's) expr" ("[_]\<^sub>e") where
[expr_defs]: "SEXP x = x"

lemma SEXP_idem [simp]: "[[e]\<^sub>e]\<^sub>e = [e]\<^sub>e" by (simp add: SEXP_def)

abbreviation (input) var :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr" where
"var x \<equiv> (\<lambda> s. get\<^bsub>x\<^esub> s)"

abbreviation (input) uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr" where
"uop f e \<equiv> (\<lambda> s. f (e s))"

abbreviation (input) bop 
  :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('c, 's) expr" where
"bop f e\<^sub>1 e\<^sub>2 \<equiv> (\<lambda> s. f (e\<^sub>1 s) (e\<^sub>2 s))"

nonterminal sexp

syntax
  "_sexp_state" :: "id"
  "_sexp_quote" :: "logic \<Rightarrow> logic" ("'(_')\<^sub>e")
  "_sexp_lit"   :: "logic \<Rightarrow> logic" ("\<guillemotleft>_\<guillemotright>")
  "_sexp_var"   :: "svid \<Rightarrow> logic" ("&_" [990] 990)
  "_sexp_evar"  :: "id_position \<Rightarrow> logic" ("@_" [999] 999)
  "_sexp_pqt"   :: "logic \<Rightarrow> sexp" ("[_]\<^sub>e")


ML \<open>
val state_id = "\<s>";
\<close>

parse_translation \<open> 
  [(@{syntax_const "_sexp_state"}, fn ctx => fn term => Syntax.free state_id)]
\<close>

translations
(*  "_sexp_lit x" => "x" *)
  "_sexp_var x" => "get\<^bsub>x\<^esub> _sexp_state"
(*  "_sexp_evar e" => "e _sexp_state" *)

ML \<open>
structure LitVars = Theory_Data
  (type T = bool
   val empty = false
   val extend = I
   val merge = (fn (x, y) => x orelse y));

Outer_Syntax.command @{command_keyword "lit_vars"} "treat variables as literals by default" 
  (Scan.succeed (Toplevel.theory (LitVars.put true)));

Outer_Syntax.command @{command_keyword "expr_vars"} "treat variables as expressions by default" 
  (Scan.succeed (Toplevel.theory (LitVars.put false)));

structure FullExprs = Theory_Data
  (type T = bool
   val empty = false
   val extend = I
   val merge = (fn (x, y) => x orelse y));

Outer_Syntax.command @{command_keyword "full_exprs"} "print full form of expressions" 
  (Scan.succeed (Toplevel.theory (FullExprs.put true)));

Outer_Syntax.command @{command_keyword "pretty_exprs"} "pretty print expressions" 
  (Scan.succeed (Toplevel.theory (FullExprs.put false)));

structure NoLift = Theory_Data
  (type T = unit Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

fun nolift_const thy n =  
          let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n 
          in NoLift.map (Symtab.update (c, ())) thy end;

Outer_Syntax.command @{command_keyword "expr_ctr"} "declare that certain constants should not be lifted"
    (Scan.repeat1 (Parse.term)
     >> (fn ns => 
         Toplevel.theory 
         (fn thy => Library.foldl (fn (thy, n) => nolift_const thy n) (thy, ns))));


Outer_Syntax.command @{command_keyword "full_exprs"} "print full form of expressions" 

\<close>

ML \<open> 
fun lift_expr_aux ctx (Const (n', t), args) =
  let 
    open Syntax
    val n = (if (Lexicon.is_marked n') then Lexicon.unmark_const n' else n')
    val args' = map (lift_expr ctx) args
  in if (n = @{const_name lens_get} orelse n = @{const_name SEXP}) 
     then Term.list_comb (Const (n', t), args)
     else if (n = @{syntax_const "_sexp_lit"})
     then Term.list_comb (hd args, tl args')
     else if (n = @{syntax_const "_sexp_evar"})
     then Term.list_comb (hd args $ free state_id, tl args')
     else if (member (op =) (Symtab.keys (NoLift.get (Proof_Context.theory_of ctx))) n)
     then Term.list_comb (Const (n', t), args) $ free state_id
     else
     case (Type_Infer_Context.const_type ctx n) of
      SOME (Type (\<^type_name>\<open>lens_ext\<close>, _)) 
        => Term.list_comb (const @{const_name lens_get} $ Const (n', t) $ free state_id, args') |
      _ => Term.list_comb (Const (n, t), args')
  end |
lift_expr_aux ctx (Free (n, t), args) = 
    let val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n in
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        if (Name_Space.declared const_space c) then
          lift_expr_aux ctx (Const (c, t), args)
        \<comment> \<open> Otherwise, we leave it alone \<close>
        else
          let val trm = if (LitVars.get (Proof_Context.theory_of ctx)) 
                        then Free (n, t) else Free (n, t) $ Syntax.free state_id
          in Term.list_comb (trm, map (lift_expr ctx) args) end
  end |
lift_expr_aux ctx (e, args) = Term.list_comb (e, args)
and 
lift_expr ctx (Abs (n, t, e)) = 
  if (n = state_id) then Abs (n, t, e) else Abs (n, t, lift_expr ctx e) |
lift_expr ctx e = lift_expr_aux ctx ((Term.strip_comb e))
\<close>

parse_translation \<open>
  [(@{syntax_const "_sexp_quote"}
   , fn ctx => fn terms =>
      case terms of
        [Const (@{const_syntax SEXP}, t) $ e] => Const (@{const_name SEXP}, t) $ e |
        [e] =>
            Syntax.const @{const_name SEXP} 
            $ (lambda (Syntax.free state_id) (lift_expr ctx (Term_Position.strip_positions e))))]
\<close>

ML \<open> \<close>

ML \<open> 
tl;

fun print_expr_aux ctx (f, args) =
  let open Proof_Context
      fun sexp_evar x = if (LitVars.get (theory_of ctx)) then Syntax.const "_sexp_evar" $ x else x
  in
  case (f, args) of
    (Const (@{syntax_const "_free"}, _), (Free (n, t) :: Const (@{syntax_const "_sexp_state"}, _) :: r)) => 
     sexp_evar (Term.list_comb (Syntax.const @{syntax_const "_free"} $ Free (n, t)
                              , map (print_expr ctx) r)) |
    (Const (@{const_syntax lens_get}, _), [x, Const (@{syntax_const "_sexp_state"}, _)])
      => Syntax.const @{syntax_const "_sexp_var"} $ x |
    (Free (n, t), [Const (@{syntax_const "_sexp_state"}, _)]) 
      => sexp_evar (Free (n, t)) | 
    _ => if (length args > 0)
         then case (List.last args) of
           Const (@{syntax_const "_sexp_state"}, _) => 
             Term.list_comb (f, map (print_expr ctx) (take (length args - 1) args)) |
           _ => Term.list_comb (f, map (print_expr ctx) args)
         else Term.list_comb (f, map (print_expr ctx) args)
   end
and 
print_expr ctx (Abs (n, t, e)) = Abs (n, t, print_expr ctx e) |
print_expr ctx e = print_expr_aux ctx (Term.strip_comb e)

fun strip_sexp_state (f, args) =
  let val args' = filter (fn x => case x of Const (@{syntax_const "_sexp_state"}, _) => false | _ => true) args
      val args'' = map (strip_sexp_state o Term.strip_comb) args'
  in Term.list_comb (f, args'') end;
\<close>

print_translation \<open>
  [(@{const_syntax "SEXP"}
   , fn ctx => fn ts =>
     if (FullExprs.get (Proof_Context.theory_of ctx)) 
     then Syntax.const @{syntax_const "_sexp_pqt"} $ hd ts 
     else
     Syntax.const @{syntax_const "_sexp_quote"} 
     $ print_expr ctx (betapply ((hd ts), Syntax.const @{syntax_const "_sexp_state"})))]
\<close>

lit_vars

term "(f \<s> + \<guillemotleft>x\<guillemotright>)\<^sub>e"

full_exprs

term "(\<guillemotleft>f\<guillemotright> (@e))\<^sub>e"

term "(f)\<^sub>e"

expr_vars

full_exprs

term "SEXP(\<lambda> \<s>. get\<^bsub>x\<^esub> \<s> + e \<s> + v)"

pretty_exprs
expr_vars

term "(@x)\<^sub>e"

term "SEXP(\<lambda> \<s>. get\<^bsub>x\<^esub> \<s> + e \<s> + v)"

lemma "(v \<in> (&xs) \<union> (&f) ys \<union> {} \<and> @e)\<^sub>e = undefined"
  apply (simp) oops

end