section \<open> Schemas \<close>

theory Schemas
  imports EDefinitions
  keywords "schema" :: "thy_decl_block"
begin

text \<open> Create a type with invariants attached; similar to a Z schema. \<close>

(* TODO: Allow names for each invariant. Change implement to avoid relying on string constructions. *)

ML \<open>
val _ =
  Outer_Syntax.command @{command_keyword schema} "define a new schema type"
    (Parse_Spec.overloaded -- (Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding) -- Scan.optional (@{keyword "where"} |-- (Scan.repeat1 (Scan.option (Parse.binding --| Parse.$$$ ":") |-- Parse.term))) ["True"]
    >> (fn (((overloaded, x), (y, z)), ts) =>
        let (* Get the new type name *)
            val n = Binding.name_of (snd x)
            (* Produce a list of type variables *)
            val varl = fold (fn _ => fn y => "_, " ^ y) (1 upto length (fst x)) "'a"
            (* Name for the new invariant *)
            val invn = n ^ "_inv"
            val itb = Binding.make (invn ^ "_def", Position.none)               
            val ib = (SOME (Binding.make (invn, Position.none), SOME ("((" ^ varl ^ ")" ^ n ^ "_scheme) => bool"), NoSyn))
            open HOLogic in
        Toplevel.theory
          (Lens_Utils.add_alphabet_cmd {overloaded = overloaded} x y z
           #> (fn thy =>
               let val ctx = Named_Target.theory_init thy
                   val invs = Library.foldr1 HOLogic.mk_conj (map (Syntax.parse_term ctx) ts)
                   val sinv = case y of
                      NONE => invs |
                      SOME t => case (Syntax.parse_typ ctx t) of
                        Type (n, _) => (case (Syntax.parse_term ctx (n ^ "_inv")) of
                          Const (\<^syntax_const>\<open>_type_constraint_\<close>, _) $ Const (n', _) => HOLogic.mk_conj (Const (n', dummyT), invs) | _ => invs) |
                        _ => invs
                   val (_, ctx') = Expr_Def.expr_def (itb, []) ib (mk_eq (Free (invn, dummyT), sinv)) ctx
                   val thy' = Local_Theory.exit_global ctx'
               in 
                 thy'
               end)
           #> (fn thy => 
               let val ctx = Named_Target.theory_init thy
                   val Const (cn, _) = Syntax.read_term ctx invn 
                   val varl = 
                     if (length (fst x) = 0)
                     then ""
                     else "(" ^ foldr1 (fn (x, _) => "_, " ^ x) (map (fn _ => "_") (1 upto length (fst x))) ^ ") "
                   val ty = Syntax.read_typ ctx (varl ^ n ^ " => bool")
                   val ctx' = Specification.abbreviation Syntax.mode_default (SOME (Binding.make (n, Position.none), SOME ty, NoSyn)) [] (Logic.mk_equals (Free (n, dummyT), Const (cn, dummyT))) false ctx
               in NoLift_Const.nolift_const (Local_Theory.exit_global ctx') (cn, [])
               end)
           #> (fn thy =>
                let
                  val ctx = Named_Target.theory_init thy
                  val Const (cn, _) = Proof_Context.read_const {proper = false, strict = false} ctx n
                in NoLift_Const.nolift_const thy (cn, []) end)
)              
        end));
\<close>

end
