structure LitVars = Theory_Data
  (type T = bool
   val empty = false
   val extend = I
   val merge = (fn (x, y) => x orelse y));

Outer_Syntax.local_theory @{command_keyword "lit_vars"} "treat variables as literals by default" 
  (Scan.succeed (Local_Theory.background_theory (LitVars.put true)));

Outer_Syntax.local_theory @{command_keyword "expr_vars"} "treat variables as expressions by default" 
  (Scan.succeed (Local_Theory.background_theory (LitVars.put false)));

structure FullExprs = Theory_Data
  (type T = bool
   val empty = false
   val extend = I
   val merge = (fn (x, y) => x orelse y));

Outer_Syntax.local_theory @{command_keyword "full_exprs"} "print full form of expressions" 
  (Scan.succeed (Local_Theory.background_theory (FullExprs.put true)));

Outer_Syntax.local_theory @{command_keyword "pretty_exprs"} "pretty print expressions" 
  (Scan.succeed (Local_Theory.background_theory (FullExprs.put false)));

structure NoLift = Theory_Data
  (type T = int list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

structure NoLift_Const =
struct

fun nolift_const ctx (n, opt) =  
      let open Proof_Context; open Syntax
      in case read_const {proper = true, strict = false} ctx n of
         Const (c, _) => Local_Theory.background_theory (NoLift.map (Symtab.update (c, (map Value.parse_int opt)))) ctx |
         _ => raise Match
      end;
end;

Outer_Syntax.local_theory @{command_keyword "expr_ctr"} "declare that certain constants are expression constructors; the parameter indicates which arguments should be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         (fn ctx => Library.foldl (fn (ctx, n) => 
                                   let open Markup 
                                       val _ = Output.warning ("Command " ^ markup keyword1 "expr_ctr" ^ " is deprecated: use " ^ markup keyword1 "expr_constructor" ^ " instead.")
                                   in NoLift_Const.nolift_const ctx n end) (ctx, ns))));

Outer_Syntax.local_theory @{command_keyword "expr_constructor"} "declare that certain constants are expression constructors; the parameter indicates which arguments should be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         (fn ctx => Library.foldl (fn (ctx, n) => NoLift_Const.nolift_const ctx n) (ctx, ns))));

