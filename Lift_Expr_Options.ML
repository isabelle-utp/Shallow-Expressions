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
  (type T = int list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

structure NoLift_Const =
struct

fun nolift_const thy (n, opt) =  
      let open Proof_Context
      in case read_const {proper = true, strict = false} (init_global thy) n of
         Const (c, _) => NoLift.map (Symtab.update (c, (map Value.parse_int opt))) thy |
         _ => raise Match
      end;
end;

Outer_Syntax.command @{command_keyword "expr_ctr"} "declare that certain constants should not be lifted; the parameter indicates which arguments should be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         Toplevel.theory 
         (fn thy => Library.foldl (fn (thy, n) => NoLift_Const.nolift_const thy n) (thy, ns))));
