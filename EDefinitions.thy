section \<open> Lifted Expression Definitions \<close>

theory EDefinitions
  imports Expressions
  keywords "edefinition" "expression" :: "thy_decl_block" and "over"
begin

text \<open> Here, we add a command that allows definition of a named expression. It provides a more
  concise version of @{command definition} and inserts the expression brackets. \<close>

named_theorems named_expr_defs

ML \<open>
structure Expr_Def =
struct

  fun mk_expr_def_eq ctx term =
    case (Type.strip_constraints term) of
      Const (@{const_name "HOL.eq"}, b) $ c $ t => 
        @{const Trueprop} $ (Const (@{const_name "HOL.eq"}, b) $ c $ (Syntax.const @{const_name SEXP} 
            $ (lambda (Syntax.free Lift_Expr.state_id) 
                      (Lift_Expr.lift_expr ctx (Term_Position.strip_positions t))))) |
      _ => raise Match;

  val expr_defs = [[Token.make_string (Binding.name_of @{binding expr_defs}, Position.none)]];

  fun expr_def attr decl term ctx =
    Specification.definition 
      (Option.map (fn x => fst (Proof_Context.read_var x ctx)) decl) [] [] 
      ((fst attr, map (Attrib.check_src ctx) (expr_defs @ snd attr)), mk_expr_def_eq ctx term) ctx

  fun named_expr n t st expr thy =
    let val named_expr_defs = @{attributes [named_expr_defs]}
        val ctx = Named_Target.theory_init thy
        val term = Const (@{const_name "HOL.eq"}, dummyT) $ Syntax.free n $ (Syntax.parse_term ctx expr)
        val stateT = Syntax.read_typ ctx st
        val typ = Syntax.read_typ ctx t
        val ctx' = snd (Specification.definition 
                       (SOME (Binding.name n, SOME (stateT --> typ), Mixfix.NoSyn)) [] [] 
                       ((Binding.name (n ^ "_def"), named_expr_defs), mk_expr_def_eq ctx term) ctx)
        val thy' = NoLift_Const.nolift_const (Local_Theory.exit_global ctx') (n, [])
        in thy' 
  end

end;

val _ =
let
  open Expr_Def;
in
  Outer_Syntax.local_theory \<^command_keyword>\<open>edefinition\<close> "UTP constant definition"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, (attr, term)), _), _) =>
        (fn ctx => snd (expr_def attr decl (Syntax.parse_term ctx term) ctx))))
end

val _ =
let
  open Expr_Def;
  val named_expr_defs = @{attributes [named_expr_defs]}
in
  Outer_Syntax.command \<^command_keyword>\<open>expression\<close> "define named expressions"
    ((((Parse.name -- Scan.optional (@{keyword "::"} |-- Parse.typ) "_" -- Scan.optional (@{keyword "over"} |-- Parse.typ) "_") --| @{keyword "is"}) -- Parse.term)  >> (fn (((n, t), st), expr) => 
        Toplevel.theory 
          (fn thy => 
            let val ctx = Named_Target.theory_init thy
                val term = Const (@{const_name "HOL.eq"}, dummyT) $ Syntax.free n $ (Syntax.parse_term ctx expr)
                val stateT = Syntax.read_typ ctx st
                val typ = Syntax.read_typ ctx t
                val ctx' = snd (Specification.definition 
                             (SOME (Binding.name n, SOME (stateT --> typ), Mixfix.NoSyn)) [] [] 
                             ((fst (Binding.name (n ^ "_def"), named_expr_defs), map (Attrib.check_src ctx) (expr_defs @ snd (Binding.name (n ^ "_def"), named_expr_defs))), mk_expr_def_eq ctx term) ctx)
                val thy' = NoLift_Const.nolift_const (Local_Theory.exit_global ctx') (n, [])
                in thy' end)))
end;

\<close>

end