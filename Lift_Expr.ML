signature LIFT_EXPR =
sig
val state_id: string
val lift_expr: Proof.context -> term -> term
val print_expr: Proof.context -> term -> term
end

structure Lift_Expr: LIFT_EXPR =
struct
val state_id = "\<s>";

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
     (* FIXME: Allow some parameters of an expression constructor to be ignored and not lifted *) 
     then let val (SOME aopt) = Symtab.lookup (NoLift.get (Proof_Context.theory_of ctx)) n in
          Term.list_comb 
            (Const (n', t)
            , map_index (fn (i, t) => 
                         if (member (op =) aopt i) 
                         then const @{const_name SEXP} $ (lambda (free state_id) (lift_expr ctx t)) 
                         else t) args) $ free state_id
          end
     else
     case (Type_Infer_Context.const_type ctx n) of
      SOME (Type (\<^type_name>\<open>lens_ext\<close>, _)) 
        => Term.list_comb (const @{const_name lens_get} $ Const (n', t) $ free state_id, args') |
      _ => Term.list_comb (Const (n, t), args')
  end |
lift_expr_aux ctx (Free (n, t), args) = 
    let open Syntax
        val consts = (Proof_Context.consts_of ctx)
        val {const_space, ...} = Consts.dest consts
        val t' = case (Syntax.check_term ctx (Free (n, t))) of
                   Free (_, t') => t' | _ => t
        \<comment> \<open> The name must be internalised in case it needs qualifying. \<close>
        val c = Consts.intern consts n in
        \<comment> \<open> If the name refers to a declared constant, then we lift it as a constant. \<close>
        if (Name_Space.declared const_space c) then
          lift_expr_aux ctx (Const (c, t), args)
        \<comment> \<open> Otherwise, we leave it alone \<close>
        else
          let val trm = 
                \<comment> \<open> We check whether the free variable has a lens type, and if so lift it as one\<close>
                case t' of 
                 Type (\<^type_name>\<open>lens_ext\<close>, _) => const @{const_name lens_get} $ Free (n, t') $ free state_id |
                 \<comment> \<open> Otherwise, we leave it alone, or apply it to the state variable if it's an expression constructor \<close>
                 _ => if (LitVars.get (Proof_Context.theory_of ctx)) 
                        then Free (n, t) else Free (n, t) $ Syntax.free state_id
          in Term.list_comb (trm, map (lift_expr ctx) args) end
  end |
lift_expr_aux _ (e, args) = Term.list_comb (e, args)
and 
lift_expr ctx (Abs (n, t, e)) = 
  if (n = state_id) then Abs (n, t, e) else Abs (n, t, lift_expr ctx e) |
lift_expr ctx e = lift_expr_aux ctx ((Term.strip_comb e))

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

end