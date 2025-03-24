type expr_config = {lit_vars:bool, full_exprs:bool, mark_vars:bool}

structure Expr_Config = Theory_Data
  (type T = expr_config
   val empty = {lit_vars = false, full_exprs = false, mark_vars = true}
   val merge = (fn (x, _) => x));

Outer_Syntax.local_theory @{command_keyword "lit_vars"} "treat variables as literals by default" 
  (Scan.succeed 
    (Local_Theory.background_theory 
      (fn thy => let val {lit_vars = _, full_exprs = fe, mark_vars = mv} = Expr_Config.get thy
                 in Expr_Config.put {lit_vars = true, full_exprs = fe, mark_vars = mv} thy
                 end)));

Outer_Syntax.local_theory @{command_keyword "expr_vars"} "treat variables as expressions by default" 
  (Scan.succeed 
    (Local_Theory.background_theory 
      (fn thy => let val {lit_vars = _, full_exprs = fe, mark_vars = mv} = Expr_Config.get thy
                 in Expr_Config.put {lit_vars = false, full_exprs = fe, mark_vars = mv} thy
                 end)));

Outer_Syntax.local_theory @{command_keyword "full_exprs"} "print full form of expressions"  
  (Scan.succeed 
    (Local_Theory.background_theory 
      (fn thy => let val {lit_vars = lv, full_exprs = _, mark_vars = mv} = Expr_Config.get thy
                 in Expr_Config.put {lit_vars = lv, full_exprs = true, mark_vars = mv} thy
                 end)));

Outer_Syntax.local_theory @{command_keyword "pretty_exprs"} "pretty print expressions" 
  (Scan.succeed 
    (Local_Theory.background_theory 
      (fn thy => let val {lit_vars = lv, full_exprs = _, mark_vars = mv} = Expr_Config.get thy
                 in Expr_Config.put {lit_vars = lv, full_exprs = false, mark_vars = mv} thy
                 end)));

Outer_Syntax.local_theory @{command_keyword "expr_mark_vars"} "mark state variables during pretty printing"  
  (Scan.succeed 
    (Local_Theory.background_theory 
      (fn thy => let val {lit_vars = lv, full_exprs = fe, mark_vars = _} = Expr_Config.get thy
                 in Expr_Config.put {lit_vars = lv, full_exprs = fe, mark_vars = true} thy
                 end)));

Outer_Syntax.local_theory @{command_keyword "expr_no_mark_vars"} "don't mark state variables during pretty printing"  
  (Scan.succeed 
    (Local_Theory.background_theory 
      (fn thy => let val {lit_vars = lv, full_exprs = fe, mark_vars = _} = Expr_Config.get thy
                 in Expr_Config.put {lit_vars = lv, full_exprs = fe, mark_vars = false} thy
                 end)));

structure NoLift = Theory_Data
  (type T = int list Symtab.table
   val empty = Symtab.empty
   val extend = I
   val merge = Symtab.merge (K true));

structure NoLift_Const =
struct

fun nolift_const (n, opt) ctx =  
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
                                   in NoLift_Const.nolift_const n ctx end) (ctx, ns))));

Outer_Syntax.local_theory @{command_keyword "expr_constructor"} "declare that certain constants are expression constructors; the parameter indicates which arguments should be lifted"
    (Scan.repeat1 (Parse.term -- Scan.optional (Parse.$$$ "(" |-- Parse.!!! (Scan.repeat1 Parse.number --| Parse.$$$ ")")) [])
     >> (fn ns => 
         (fn ctx => Library.foldl (fn (ctx, n) => NoLift_Const.nolift_const n ctx) (ctx, ns))));

