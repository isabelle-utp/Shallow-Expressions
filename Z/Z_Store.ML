signature ZSTORE =
sig
  val mk_zstore: 
        (string * string option) list * binding -> 
        string option -> (binding * string * mixfix) list -> 
        (binding * string) list -> theory -> theory
end

structure ZStore : ZSTORE =
struct

fun read_parent NONE ctxt = (NONE, ctxt)
  | read_parent (SOME raw_T) ctxt =
      (case Proof_Context.read_typ_abbrev ctxt raw_T of
        Type (name, Ts) => (SOME (Ts, name), fold Variable.declare_typ Ts ctxt)
      | T => error ("Bad parent record specification: " ^ Syntax.string_of_typ ctxt T));

(* Get the subset of the parameters that the locale's assumptions depend on *)
fun dep_params_of thy l = 
  case fst (Locale.specification_of thy l) of
    SOME (Const (@{const_name Trueprop}, _) $ t) => map dest_Free (snd (Term.strip_comb t)) |
    _ => []

fun mk_zstore (raw_params, binding) raw_parent raw_fields invs thy = 
  let (* Get the new type name *)
      val n = Binding.name_of binding
      (* Produce a list of type variables *)
      val varl = fold (fn _ => fn y => "_, " ^ y) (1 upto length raw_params) "'a"
      (* Name for the new invariant *)
      val assmsn = (n ^ "_invariants")
      val invn = n ^ "_inv"
      (* Need to enumerate all variables in a fake assumption *)
      val invs = if invs = [] then [(Binding.empty, "True")] else invs
      val fixes = Element.Fixes (map (fn (n, t, s) => (n, SOME t, s)) raw_fields)
      val assms = [Element.Assumes [((Binding.name assmsn, []), (map (fn (_, t) => (t, [])) invs))]]
      val itb = Binding.make (invn ^ "_def", Position.none)
      val (parent, _) = (read_parent raw_parent (Proof_Context.init_global thy))
      val locex = case parent of NONE => [] | SOME n => [((snd n, Position.none), (("", false), (Expression.Named [], [])))]
      val z_defs = Attrib.check_src @{context} (Token.make_src ("z_defs", Position.none) [])

      val ib = (SOME (Binding.make (invn, Position.none), SOME ("((" ^ varl ^ ")" ^ n ^ "_scheme) => bool"), NoSyn))
        open HOLogic in
        Lens_Utils.add_alphabet_cmd (raw_params, binding) raw_parent raw_fields thy |>
        Record_Default_Instance.mk_rec_default_instance n |>
        Local_Theory.exit_global o 
           (snd o Expression.add_locale_cmd binding Binding.empty [] (locex, []) ([fixes] @ assms)
            #> (fn ctx => snd (Local_Theory.notes (map_index (fn (i, (n, _)) => ((n, []), [([nth (Proof_Context.get_thms ctx assmsn) i],[])])) invs) ctx))
            #> (fn ctx =>
                  let val passms = case parent of NONE => [] | SOME (_, n) => Proof_Context.get_thms ctx ((Long_Name.base_name n) ^ "_invariants")                 
                  in snd (Local_Theory.note ((Binding.name "invariants", []), (passms @ Proof_Context.get_thms ctx assmsn)) ctx) end)
           ) |>
        (fn thy => 
               let open Attrib
                   val Const (ln, _) = Syntax.read_term (Proof_Context.init_global thy) n 
                   val loc_def = Global_Theory.get_thm thy (n ^ "_def")
                   val z_locale_defs = attribute_global @{theory} (check_src @{context} (Token.make_src ("z_locale_defs", Position.none) []))
                   val loc_thms = [((Binding.empty, loc_def), [z_locale_defs])]
                                  (* If there is a parent, then we also need to unfold the locale axioms definition *)
                                  @ (if parent = NONE then [] 
                                     else [((Binding.empty, Global_Theory.get_thm thy (n ^ "_axioms_def")), [z_locale_defs])])
                   val vars = (map (Syntax.free o fst) (dep_params_of thy ln))
                   val ctx = Named_Target.theory_init thy
                   val sinv = Term.list_comb (Syntax.free n, vars)
                   val (_, ctx') = Expr_Def.expr_def (itb, [z_defs]) ib (mk_eq (Free (invn, dummyT), sinv)) ctx
                   val thy' = Local_Theory.exit_global ctx'
                   val thy'' = snd (Global_Theory.add_thms loc_thms  thy')
               in 
                 thy''
        end) |>
        (fn thy =>
                let
                  val ctx = Named_Target.theory_init thy
                  val Const (cn, _) = Proof_Context.read_const {proper = false, strict = false} ctx invn
                in Local_Theory.exit_global (ExprCtr_Const.exprctr_const (cn, []) ctx) end)
        end
end

val _ =
  Outer_Syntax.command @{command_keyword zstore} "define a new Z store type"
    ((Parse.type_args_constrained -- Parse.binding) --
      (@{keyword "="} |-- Scan.option (Parse.typ --| @{keyword "+"}) --
        Scan.repeat1 Parse.const_binding) -- Scan.optional (@{keyword "where"} |-- (Scan.repeat1 (Scan.optional (Parse.binding --| Parse.$$$ ":") (Binding.name "") -- Parse.term))) []
    >> (fn ((x, (y, z)), ts) => Toplevel.theory (ZStore.mk_zstore x y z ts)))

val _ =
let
  open Expr_Def;
  val z_defs = Attrib.check_src @{context} (Token.make_src ("z_defs", Position.none) [])
in
  Outer_Syntax.command \<^command_keyword>\<open>zexpr\<close> "define expressions over a Z store"
    (((Parse.name --| @{keyword "is"}) -- Parse.term)  >> (fn (n, expr) => 
        Toplevel.theory 
          (fn thy => 
            let val ctx = Named_Target.theory_init thy
                val term = Const (@{const_name "HOL.eq"}, dummyT) $ Syntax.free n $ (Syntax.parse_term ctx expr)
                val ctx' = snd (expr_def (Binding.name (n ^ "_def"), [z_defs]) NONE term ctx) 
                val thy' = Local_Theory.exit_global (ExprCtr_Const.exprctr_const (n, []) ctx')
                in thy' end)))
end
