section \<open> Lifted Expression Definitions \<close>

theory EDefinitions
  imports Expressions
  keywords "edefinition" :: "thy_decl_block"
begin

(* FIXME: Change interface so that it accepts typs and terms, rather than strings. *)

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

end

val _ =
let
  open Expr_Def;
in
  Outer_Syntax.local_theory \<^command_keyword>\<open>edefinition\<close> "UTP constant definition"
    (Scan.option Parse_Spec.constdecl -- (Parse_Spec.opt_thm_name ":" -- Parse.prop) --
      Parse_Spec.if_assumes -- Parse.for_fixes >> (fn (((decl, (attr, term)), _), _) =>
        (fn ctx => snd (expr_def attr decl (Syntax.parse_term ctx term) ctx))))
end
\<close>               

end