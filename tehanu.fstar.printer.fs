module Tehanu.FStar.Printer

open Tehanu.Core
open Tehanu.Core.Patterns
                             
let sprintType typ =
  match typ with
  | TypeId name -> name

let sprintId id =
  match id with
  | Id i -> i              
  | _ -> " !!!oh!!!problems!!! " + string id + " !!!problems!!!oh!!!"

let rec sprintExpr exp =
  match exp with            
  | ExprConstInt i -> string i
  | ExprId id -> id             
  | ExprIf(cond, th, el) -> "(if " + (sprintExpr cond) + " then " + (sprintExpr th) + " else " + (sprintExpr el) + ")"                                                                       
  | ExprApp (ExprApp (ExprId "<==>", l), r) -> "(" + (sprintExpr l) + " <==> " + (sprintExpr r) + ")"              
  | ExprApp (ExprApp (ExprId "==>", l), r) -> "(" + (sprintExpr l) + " ==> " + (sprintExpr r) + ")"              
  | ExprApp (ExprApp (ExprId "==", l), r) -> "(" + (sprintExpr l) + " == " + (sprintExpr r) + ")"              
  | ExprApp (ExprApp (ExprId "!=", l), r) -> "(" + (sprintExpr l) + " != " + (sprintExpr r) + ")"     
  | ExprApp (ExprApp (ExprId "<=", l), r) -> "(" + (sprintExpr l) + " <= " + (sprintExpr r) + ")"
  | ExprApp (ExprApp (ExprId ">=", l), r) -> "(" + (sprintExpr l) + " >= " + (sprintExpr r) + ")"  
  | ExprApp (ExprApp (ExprId "<", l), r) -> "(" + (sprintExpr l) + " < " + (sprintExpr r) + ")"
  | ExprApp (ExprApp (ExprId ">", l), r) -> "(" + (sprintExpr l) + " > " + (sprintExpr r) + ")"   
  | ExprApp (ExprApp (ExprId "+", l), r) -> "(" + (sprintExpr l) + " + " + (sprintExpr r) + ")"
  | ExprApp (ExprApp (ExprId "-", l), r) -> "(" + (sprintExpr l) + " - " + (sprintExpr r) + ")"
  | ExprApp (ExprApp (ExprId "*", l), r) -> "(" + (sprintExpr l) + " * " + (sprintExpr r) + ")"
  | ExprApp (ExprApp (ExprId "/", l), r) -> "(" + (sprintExpr l) + " / " + (sprintExpr r) + ")"
  | ExprApp (l, r) -> "(" + (sprintExpr l) + " " + (sprintExpr r) + ")"                        
  | ExprForall (List names, expr) -> "forall " + (String.concat " " [for name in names -> sprintId name]) + " . " + (sprintExpr expr)
  | ExprExist (List names, expr) -> "exist " + (String.concat " " [for name in names -> sprintId name]) + " . " + (sprintExpr expr)
  | _ -> " !!!oh!!!problems!!! " + string exp + " !!!problems!!!oh!!!"

let sprintArgType arg =
  match arg with
  | Arg (name, typ) ->
    sprintType typ
  | _ -> " !!!oh!!!problems!!! " + string arg + " !!!problems!!!oh!!!"

let sprintArgTypes args =
  match args with
  | List xs -> String.concat " * " [for x in xs -> sprintArgType x]
  | _ -> " !!!oh!!!problems!!! " + string args + " !!!problems!!!oh!!!"

let sprintArgTypess argss =
  match argss with
  | List xs -> String.concat " -> " [for x in xs -> sprintArgTypes x]
  | _ -> " !!!oh!!!problems!!! " + string argss + " !!!problems!!!oh!!!"

let sprintAttr name attr argss ret =
  match attr with
  | Attr ("Total", expr) ->
    "val " + name + " : i : (" + (sprintArgTypess argss) + " -> Tot " + (sprintArgType ret) + ") {" + (sprintExpr expr) + "} "
  | _ -> " !!!oh!!!problems!!! " + string attr + " !!!problems!!!oh!!!"
                            
let sprintArgName arg =
  match arg with
  | Arg (name, typ) ->
    name
  | _ -> " !!!oh!!!problems!!! " + string arg + " !!!problems!!!oh!!!"

let sprintArgNames args =
  match args with                                                                      
  | List [x] -> sprintArgName x
  | List xs -> "(" + String.concat ", " [for x in xs -> sprintArgName x] + ")"
  | _ -> " !!!oh!!!problems!!! " + string args + " !!!problems!!!oh!!!"

let sprintArgNamess argss =
  match argss with
  | List xs -> String.concat " " [for x in xs -> sprintArgNames x]
  | _ -> " !!!oh!!!problems!!! " + string argss + " !!!problems!!!oh!!!"

let sprintLet l =
  match l with
  | Let (List attrs, name, Pair(argss, ret), expr) ->
    (String.concat "\n" [for attr in attrs -> sprintAttr name attr !argss !ret]) + "\nlet " + name + " " + (sprintArgNamess !argss) + " = " + (sprintExpr expr)
  | _ -> " !!!oh!!!problems!!! " + string l + " !!!problems!!!oh!!!"

let sprintModule modul =
  match modul with
  | Module (name, List items) ->
    "module " + name + "\n\n" + (String.concat "\n\n" [for it in items -> sprintLet it])
  | Module (name, items) -> 
    "module " + name + "\n\n"
  | _ -> " !!!oh!!!problems!!! " + string modul + " !!!problems!!!oh!!!"

let sprintModules modules =
  match modules with
  | List its ->
    String.concat "\n\n" [for it in its -> sprintModule it]
  | _ -> " !!!oh!!!problems!!! " + string modules + " !!!problems!!!oh!!!"
