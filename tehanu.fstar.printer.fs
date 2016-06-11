module Tehanu.FStar.Printer

open Tehanu.Core
open Tehanu.Core.Patterns
              
let mutable ispos = true

let orOpt sep (a, b)=
  match a, b with
  | Some(a), Some(b) -> Some(a + sep + b)
  | Some(a), None -> Some(a)
  | None, Some(b) -> Some(b)
  | None, None -> None  
               
let sprintType typ =
  match typ with
  | TypeId name -> Success name     
  | _ -> Hint ("It is not type", Fail <| string id)

let sprintId id =
  match id with
  | Id i -> Success <| i              
  | _ -> Hint ("It is not id", Fail <| string id)

let rec sprintIds ids =    
  match ids with
  | [] -> Hint ("It is empty list", Nothing)
  | [x] -> sprintId x
  | x :: xs -> (sprintId x).AndResult(sprintIds xs, orOpt " ", ispos)
    
let rec sprintExpr exp =
  match exp with            
  | ExprConstInt i -> Success <| string i
  | ExprId id -> Success id             
  | ExprIf (cond, th, el) ->
    match sprintExpr cond, sprintExpr th, sprintExpr el with
    | Success c, Success t, Success e -> Success <| "(if " + c + " then " + t + " else " + e + ")"         
    | c, t, e -> c.CombineHints(t, e.CombineHints(Nothing, Fail <| string exp))                      
  | ExprApp (ExprApp (ExprId "<==>", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " <==> " + re + ")"    
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                           
  | ExprApp (ExprApp (ExprId "==>", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " ==> " + re + ")"  
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                              
  | ExprApp (ExprApp (ExprId "==", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " == " + re + ")"
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                      
  | ExprApp (ExprApp (ExprId "!=", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " != " + re + ")"      
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                      
  | ExprApp (ExprApp (ExprId "=<", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " =< " + re + ")"      
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                           
  | ExprApp (ExprApp (ExprId "=>", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " => " + re + ")"      
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                         
  | ExprApp (ExprApp (ExprId "<", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " < " + re + ")"       
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                           
  | ExprApp (ExprApp (ExprId ">", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " > " + re + ")"       
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                      
  | ExprApp (ExprApp (ExprId "+", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " + " + re + ")"       
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                           
  | ExprApp (ExprApp (ExprId "-", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " - " + re + ")"       
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                           
  | ExprApp (ExprApp (ExprId "*", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " * " + re + ")"   
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                               
  | ExprApp (ExprApp (ExprId "/", l), r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " / " + re + ")"       
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                      
  | ExprApp (l, r) ->
    match sprintExpr l, sprintExpr r with
    | Success le, Success re -> Success <| "(" + le + " " + re + ")"  
    | lr, rr -> lr.CombineHints(rr, Fail <| string exp)                                                  
  | ExprForall (List names, expr) ->    
    let forallCombinator (ns, e) =
      match ns, e with   
      | Some a, Some b -> Some <| "forall " + a + " . " + b
      | Some a, None -> Some <| "forall " + a + " . "
      | None, Some b -> Some <| "forall . " + b
      | None, None -> None
    (sprintIds names).AndResult(sprintExpr expr, forallCombinator, ispos)
  | ExprExist (List names, expr) ->                                       
    let existCombinator (ns, e) =
      match ns, e with   
      | Some a, Some b -> Some <| "exist " + a + " . " + b
      | Some a, None -> Some <| "exist " + a + " . "
      | None, Some b -> Some <| "exist . " + b
      | None, None -> None
    (sprintIds names).AndResult(sprintExpr expr, existCombinator, ispos)
  | _ -> Hint("It is not expr", Fail <| string exp)

let sprintArgType arg =
  match arg with
  | Arg (name, typ) -> sprintType typ
  | _ -> Hint("It is not arg type", Fail <| string arg)

let rec sprintArgTypeList args =
  match args with                       
  | [] -> Success <| "unit"
  | [x] -> sprintArgType x
  | x::xs -> (sprintArgType x).AndResult(sprintArgTypeList xs, orOpt " * ", ispos)

let sprintArgTypes args =
  match args with
  | List xs -> sprintArgTypeList xs
  | _ -> Hint("It is not arg types", Fail <| string args)

let rec sprintArgTypesList args =
  match args with                       
  | [] -> Hint("Is empty list", Nothing)
  | [x] -> sprintArgTypes x
  | x::xs -> (sprintArgTypes x).AndResult(sprintArgTypesList xs, orOpt " -> ", ispos)

let sprintArgTypess argss =
  match argss with
  | List xs -> sprintArgTypesList xs
  | _ -> Hint("It is not arg typess", Fail <| string argss)

let sprintAttr name attr argss ret =
  match attr with
  | Attr ("Total", expr) ->
    let valCombinator (a, b) =
      match orOpt ") {" (a, b) with
      | Some(c) -> Some <| "val " + name + " : i : (" + c + "}"
      | None -> None
    (sprintArgTypess argss).AndResult(sprintArgType ret, orOpt " -> Tot ", ispos).AndResult(sprintExpr expr, valCombinator, ispos)                          
  | _ -> Hint("It is not total attribute", Fail <| string attr)
                            
let sprintArgName arg =
  match arg with
  | Arg (name, typ) -> Success name
  | _ -> Hint("It is not arg name", Fail <| string arg)

let rec sprintArgNameList args =
  match args with                       
  | [] -> Success <| "()"
  | [x] -> sprintArgName x
  | x::xs -> (sprintArgName x).AndResult(sprintArgNameList xs, orOpt " , ", ispos)

let sprintArgNames args =
  match args with                                                                      
  | List xs ->
    let brackets (a, None) =
      match a with                         
      | Some(ar) -> Some <| "(" + ar + ")"
      | None -> None
    (sprintArgNameList xs).AndResult(Nothing, brackets, ispos)
  | _ -> Hint("It is not arg name", Fail <| string args)

let rec sprintArgNamesList args =
  match args with                       
  | [] -> Hint ("It is empty list", Nothing)
  | [x] -> sprintArgNames x
  | x::xs -> (sprintArgNames x).AndResult(sprintArgNamesList xs, orOpt " ", ispos)

let sprintArgNamess argss =
  match argss with
  | List xs -> sprintArgNamesList xs
  | _ -> Hint("It is not arg namess", Fail <| string argss)

let sprintLet l =
  match l with
  | Let (List [attr], name, Pair(argss, ret), expr) ->
    (sprintAttr name attr !argss !ret).AndResult(sprintArgNamess !argss, orOpt <| "\nlet " + name + " ", ispos).AndResult(sprintExpr expr, orOpt " = ", ispos) 
  | _ -> Fail <| string l

let rec sprintModuleItems its =
  match its with   
  | [] -> Hint ("It is empty list", Nothing) 
  | [x] -> sprintLet x
  | x :: xs -> (sprintLet x).AndResult(sprintModuleItems xs, orOpt "\n  ", ispos)

let sprintModule modul =
  match modul with
  | Module (name, List items) ->
    let mits = sprintModuleItems items
    Nothing.AndResult(mits, orOpt <| "module " + name, ispos)
  | _ -> Hint("is not module", Fail <| string modul)

let rec sprintModuleList lst =   
  match lst with
  | [] -> Hint ("It is empty list", Nothing)
  | [x] -> sprintModule x
  | x :: xs -> (sprintModule x).AndResult(sprintModuleList xs, orOpt "\n\n", ispos)
                            
let sprintModules modules =
  match modules with
  | List its -> sprintModuleList its
  | _ -> Hint ("It is not module list", Fail <| string modules)
