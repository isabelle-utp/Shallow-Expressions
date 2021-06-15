(* Utilities for manipulating shallow expression syntax *)

signature EXPR_UTIL =
sig
  val subst_tab: term -> term Symtab.table
  val log_vars: term -> string list
end

structure Expr_Util: EXPR_UTIL =
struct

  (* Extract a table of variable assignments for a substitution *)
  fun subst_tab' m (Const (@{const_name subst_upd}, _) $ s $ x $ e) = 
    (case x of
       Const (n, _) => subst_tab' (Symtab.update (n, e) m) s |
       Free (n, _) => subst_tab' (Symtab.update (n, e) m) s |
       _ => m) |
  subst_tab' m _ = m;

  val subst_tab = subst_tab' Symtab.empty;

  (* Extract the "logical variables" from an expression, excluding lenses *)
  fun log_vars (Const (@{const_name lens_get}, _) $ _ $ _) = Ord_List.make string_ord [] 
  | log_vars (Bound _) = []
  | log_vars (Abs (_, _, e)) = log_vars e
  | log_vars (Const (_, _)) = []
  | log_vars (Free (n, _)) = Ord_List.make string_ord [n]
  | log_vars (e $ f) = Ord_List.union string_ord (log_vars e) (log_vars f)
  | log_vars (Var (_, _)) = [];

end