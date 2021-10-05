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

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

fun mk_zstore (raw_params, binding) raw_parent raw_fields invs thy = 
    let val ctx = Named_Target.theory_init thy
      (* Get the new type name *)
      val n = Binding.name_of binding
      (* Produce a list of type variables *)
      val varl = fold (fn _ => fn y => "_, " ^ y) (1 upto length raw_params) "'a"
      (* Name for the new invariant *)
      val assmsn = (n ^ "_invariants")
      val invn = n ^ "_inv"
      val fixes = Element.Fixes (map (fn (n, t, s) => (n, SOME (Syntax.parse_typ ctx t), s)) raw_fields)
      val assms = (if (invs = []) then [] else [Element.Assumes [((Binding.name assmsn, []), (map (fn (_, t) => (HOLogic.mk_Trueprop (Syntax.parse_term ctx t), [])) invs))]])
      val itb = Binding.make (invn ^ "_def", Position.none)
      val (parent, _) = (read_parent raw_parent (Proof_Context.init_global thy))
      val locex = case parent of NONE => [] | SOME n => [(snd n, (("", false), (Expression.Named [], [])))]

      val ib = (SOME (Binding.make (invn, Position.none), SOME ("((" ^ varl ^ ")" ^ n ^ "_scheme) => bool"), NoSyn))
        open HOLogic in
        Lens_Utils.add_alphabet_cmd (raw_params, binding) raw_parent raw_fields thy |>
        Record_Default_Instance.mk_rec_default_instance n |>
        Local_Theory.exit_global o 
           (snd o Expression.add_locale binding Binding.empty [] (locex, []) ([fixes] @ assms) 
            #> (fn ctx => snd (Local_Theory.notes (map_index (fn (i, (n, _)) => ((n, []), [([nth (Proof_Context.get_thms ctx assmsn) i],[])])) invs) ctx))
            #> (fn ctx =>
                  let val passms = case parent of NONE => [] | SOME (_, n) => Proof_Context.get_thms ctx ((Long_Name.base_name n) ^ "_invariants")                 
                  in snd (Local_Theory.note ((Binding.name "invariants", []), (passms @ Proof_Context.get_thms ctx assmsn)) ctx) end)
           ) |>
        (fn thy => 
               let val Const (ln, _) = Syntax.read_term (Proof_Context.init_global thy) n 
                   val vars = (map (Syntax.free o fst o fst) (Locale.params_of thy ln))
                   val ctx = Named_Target.theory_init thy
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