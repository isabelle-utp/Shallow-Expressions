theory Expressions
  imports Variables
begin

named_theorems expr_defs

type_synonym ('a, 's) expr = "'s \<Rightarrow> 'a"

definition SEXP :: "('s \<Rightarrow> 'a) \<Rightarrow> ('a, 's) expr" ("[_]\<^sub>E") where
[expr_defs]: "SEXP x = x"

lemma SEXP_idem [simp]: "[[e]\<^sub>E]\<^sub>E = [e]\<^sub>E" by (simp add: SEXP_def)

abbreviation (input) var :: "('a \<Longrightarrow> 's) \<Rightarrow> ('a, 's) expr" where
"var x \<equiv> (\<lambda> s. get\<^bsub>x\<^esub> s)"

abbreviation (input) uop :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr" where
"uop f e \<equiv> (\<lambda> s. f (e s))"

abbreviation (input) bop 
  :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> ('a, 's) expr \<Rightarrow> ('b, 's) expr \<Rightarrow> ('c, 's) expr" where
"bop f e\<^sub>1 e\<^sub>2 \<equiv> (\<lambda> s. f (e\<^sub>1 s) (e\<^sub>2 s))"

syntax
  "_sexp_state" :: "id"
  "_sexp_quote" :: "logic \<Rightarrow> logic" ("U'(_')")
  "_sexp_lit"   :: "logic \<Rightarrow> logic" ("\<guillemotleft>_\<guillemotright>")
  "_sexp_var"   :: "svid \<Rightarrow> logic" ("&_" [990] 990)
  "_sexp_evar"  :: "id \<Rightarrow> logic" ("@_" [999] 999)

parse_translation \<open> 
  [(@{syntax_const "_sexp_state"}, fn ctx => fn term => Syntax.free "STATE")]
\<close>

translations
  "_sexp_lit x" => "x"
  "_sexp_var x" => "get\<^bsub>x\<^esub> _sexp_state"
  "_sexp_evar e" => "e _sexp_state"

ML \<open>
structure NoLift = Theory_Data
  (type T = unit Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

fun nolift_const n thy =  
          let val Const (c, _) = Proof_Context.read_const {proper = true, strict = false} (Proof_Context.init_global thy) n 
          in NoLift.map (Symtab.update (c, ())) thy end
\<close>

ML \<open> 
fun lift_expr_aux ctx (Const (n', t), args) =
  let 
    open Syntax
    val n = (if (Lexicon.is_marked n') then Lexicon.unmark_const n' else n')
    val args' = map (lift_expr ctx) args
  in if (n = @{const_name lens_get} orelse n = @{const_name SEXP}) 
     then Term.list_comb (Const (n', t), args)
     else if (member (op =) (Symtab.keys (NoLift.get (Proof_Context.theory_of ctx))) n)
     then Term.list_comb (Const (n', t), args) $ free "STATE"
     else
     case (Type_Infer_Context.const_type ctx n) of
      SOME (Type (\<^type_name>\<open>lens_ext\<close>, _)) 
        => Term.list_comb (const @{const_name lens_get} $ Const (n', t) $ free "STATE", args') |
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
          Term.list_comb (Free (n, t), args)
  end |
lift_expr_aux ctx (e, args) = Term.list_comb (e, args)
and 
lift_expr ctx (Abs (n, t, e)) = 
  if (n = "STATE") then Abs (n, t, e) else Abs (n, t, lift_expr ctx e) |
lift_expr ctx e = lift_expr_aux ctx (Term.strip_comb e)

(*
fun
  (* FIXME: Add a command to allow certain constants to be ignored and their parameters not interpreted. *)
  lift_expr _ (Const (@{const_syntax lens_get}, t) $ x) = (Const (@{const_name lens_get}, t) $ x) |
  lift_expr _ (Const (@{const_syntax lens_get}, t) $ x $ y) = (Const (@{const_name lens_get}, t) $ x $ y) |
  lift_expr ctx (Const (n', t)) =
  let val n = (if (Lexicon.is_marked n') then Lexicon.unmark_const n' else n')
  in case (Type_Infer_Context.const_type ctx n) of
      SOME (Type (\<^type_name>\<open>lens_ext\<close>, _)) => Const (@{const_name lens_get}, dummyT) $ Const (n', t) $ Syntax.free "STATE" |
      _ => Const (n, t)
  end |
lift_expr ctx (Free (n, t)) = 
    let val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n in
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        if (Name_Space.declared const_space c) then
          lift_expr ctx (Const (c, t))
        \<comment> \<open> Otherwise, we leave it alone \<close>
        else
          Free (n, t)
  end |
lift_expr ctx (f $ x) = lift_expr ctx f $ lift_expr ctx x |
lift_expr _ x = x 
*)
\<close>

parse_translation \<open>
  [(@{syntax_const "_sexp_quote"}
   , fn ctx => fn term => 
      Syntax.const @{const_name SEXP} 
      $ (lambda (Syntax.free "STATE") (lift_expr ctx (hd term))))]
\<close>
print_translation \<open>
  [(@{const_syntax "SEXP"}
   , fn ctx => fn ts =>
     Syntax.const @{syntax_const "_sexp_quote"} 
     $ betapply (hd ts, Syntax.const @{syntax_const "_sexp_state"}))]
\<close>

translations
  "&x" <= "get\<^bsub>x\<^esub> _sexp_state"
  "@e" <= "e _sexp_state"

lemma "U(v \<in> &xs \<union> ys \<union> {} \<and> @e) = undefined"
  apply (simp) oops

end