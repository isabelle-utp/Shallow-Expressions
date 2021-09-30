section \<open> Z Stores \<close>

theory Z_Store
  imports "Shallow-Expressions.EDefinitions" "Z_Toolkit.Relation_Lib"
  keywords "zstore" :: "thy_decl_block"
begin

text \<open> This theory creates a command for adding Z-like state schemas. It creates both an alphabet,
  which can be used in program constructions, and an associated locale that groups together
  a set of assumptions. \<close>

ML \<open>

structure ZStore =
struct

fun mk_zstore x y z invs thy = 
    let val ctx = Named_Target.theory_init thy
      (* Get the new type name *)
      val n = Binding.name_of (snd x)
      (* Produce a list of type variables *)
      val varl = fold (fn _ => fn y => "_, " ^ y) (1 upto length (fst x)) "'a"
      (* Name for the new invariant *)
      val assmsn = "invariants"
      val invn = n ^ "_inv"
      val fixes = Element.Fixes (map (fn (n, t, s) => (n, SOME (Syntax.parse_typ ctx t), s)) z)
      val assms = (if (invs = []) then [] else [Element.Assumes [((Binding.name assmsn, []), (map (fn (_, t) => (HOLogic.mk_Trueprop (Syntax.parse_term ctx t), [])) invs))]])
      val itb = Binding.make (invn ^ "_def", Position.none)               
      val ib = (SOME (Binding.make (invn, Position.none), SOME ("((" ^ varl ^ ")" ^ n ^ "_scheme) => bool"), NoSyn))
        open HOLogic in
        Lens_Utils.add_alphabet_cmd x y z thy |>
        Record_Default_Instance.mk_rec_default_instance n |>
        Local_Theory.exit_global o 
           (snd o Expression.add_locale (snd x) Binding.empty [] ([], []) ([fixes] @ assms) 
            #> (fn ctx => snd (Local_Theory.notes (map_index (fn (i, (n, _)) => ((n, []), [([nth (Proof_Context.get_thms ctx "invariants") i],[])])) invs) ctx))
           ) |>
        (fn thy =>
               let val ctx = Named_Target.theory_init thy
                   val vars = map (fn (n, _, _) => Syntax.free (Binding.name_of n)) z
                   val sinv = Term.list_comb (Syntax.free n, vars)
                   val (_, ctx') = Expr_Def.expr_def (itb, []) ib (mk_eq (Free (invn, dummyT), sinv)) ctx
                   val thy' = Local_Theory.exit_global ctx'
               in 
                 thy'
        end) |>
        (fn thy =>
                let
                  val ctx = Named_Target.theory_init thy
                  val Const (cn, _) = Proof_Context.read_const {proper = false, strict = false} ctx invn
                in NoLift_Const.nolift_const thy (cn, []) end)
        end
end

val _ =
  Outer_Syntax.command @{command_keyword zstore} "define a new Z store type"
    ((Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding) -- Scan.optional (@{keyword "where"} |-- (Scan.repeat1 (Scan.optional (Parse.binding --| Parse.$$$ ":") (Binding.name "") -- Parse.term))) []
    >> (fn ((x, (y, z)), ts) => Toplevel.theory (ZStore.mk_zstore x y z ts)))
\<close>

end