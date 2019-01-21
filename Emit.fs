module Emit

open Error
open Expr
open Infer
open Util

let currentId = ref 0

let nextId () =
    let id = !currentId
    currentId := id + 1
    id

let getNewVar () =
    let id = nextId ()
    sprintf "_lua%d" id

let emitBinop op =
    match op with
    | Plus -> "+"
    | Minus -> "-"
    | Multiply -> "*"
    | Divide -> "/"
    | And -> "and"
    | Or -> "or"
    | Equal -> "=="
    | NotEqual -> "~="
    | Greater -> ">"
    | GreaterEqual -> ">="
    | Lesser -> "<"
    | LesserEqual -> "<="

let emitUnop op =
    match op with
    | Negative -> "-"

let isSingleLineExpr expr =
    match expr with
    | EPrint _
    | EBool _
    | EInt _
    | EFloat _
    | EString _
    | EVar _
    | ECall _
    | ERecordSelect _
    | ERecordExtend _
    | ERecordRestrict _
    | ERecordEmpty 
    | EVariant _
    | EFix _
    | EBinOp _
    | EUnOp _
    | EOpen _
    | EError _ -> true
    | EFun _
    | ELet _
    | EIfThenElse _ -> false
    | _ -> failwith "TODO"
    // | ECase of Expr * (Pattern * Expr * Guard option) list * (Name * Expr) option
    // | EListEmpty
    // | EListCons of Expr * Expr
    // | EType of Expr * Ty

let isStatement expr =
    match expr with
    | EPrint _
    | EBool _
    | EInt _
    | EFloat _
    | EString _
    | EVar _
    | ECall _
    | EFun _
    | ERecordSelect _
    | ERecordExtend _
    | ERecordRestrict _
    | ERecordEmpty
    | EVariant _
    | EBinOp _
    | EUnOp _
    | EFix _
    | EOpen _
    | EError _ -> false
    | ELet _
    | ECase _
    | EIfThenElse _ -> true
    // | EListEmpty
    // | EListCons of Expr * Expr
    // | EType of Expr * Ty

let rec extractBindingsAndVariantGuards pattern var bindings guards =
    match pattern with
    | EVar name -> Map.add name var bindings, guards
    | ERecordEmpty -> bindings, guards
    | ERecordExtend (field, fieldPattern, record) ->
        let fieldAccess = sprintf "%s.%s" var field
        let map, guards = extractBindingsAndVariantGuards fieldPattern.Value fieldAccess bindings guards
        extractBindingsAndVariantGuards record.Value var map guards
    | EVariant (name, variant) ->
        let fieldAccess = sprintf "%s.variant_%s" var name
        let guard = sprintf "%s.variant_name = %s" var name
        let guards = guard :: guards
        extractBindingsAndVariantGuards variant.Value fieldAccess bindings guards
    | _ -> failwithf "impossible, got pattern %O" pattern

let extractValueGuard guard bindings =
    match guard with
    | EVar name -> Map.find name bindings
    | EBool b -> string b
    | EInt i -> string i
    | EFloat f -> string f
    | EString s -> sprintf "'%s'" s
    | _ -> failwithf "impossible, got guard %O" guard

let rec emitCaseExpr oAssignVar map value cases oDefault =
    let valueVar =
        match value with
        | EVar name -> name
        | _ -> failwith "value is not a var"
    let assignVar =
        match oAssignVar with
        | Some var -> var
        | None -> getNewVar ()
    let cases =
        cases
        |> List.map (fun (pattern, body, oGuard) ->
            let bindings, guards = extractBindingsAndVariantGuards pattern.Value valueVar Map.empty []
            let guards =
                match oGuard with
                | None -> guards
                | Some guard -> 
                    emitExpr None bindings guard.Value :: guards
            let guard =
                match guards with
                | [] -> failwith "invalid, will always match"
                | guards -> 
                    guards
                    |> String.concat " and "
            sprintf "if %s then\n%s\n" guard (emitExpr (Some assignVar) bindings body.Value)
        )
        |> String.concat "else"
    let def =
        match oDefault with
        | Some (var, body) -> 
            sprintf "else\nlocal %s = %s\n%s\nend" var valueVar (emitExpr (Some var) map body.Value)
        | None -> sprintf "else\nerror('no match')\nend"
    match oAssignVar with
    | Some _ -> cases + def
    | None -> sprintf "local %s\n%s%s" assignVar cases def

and emitExpr oAssignVar map expr =
    let getVar var =
        map
        |> Map.tryFind var
        |> Option.defaultValue var
    match expr with
    | EBool false -> "false"
    | EBool true -> "true"
    | EInt i -> string i
    | EFloat f -> string f
    | EString s -> sprintf "'%s'" s
    | EVar name -> getVar name
    | ECall (fn, arg) ->
        sprintf "%s(%s)" (emitExpr None map fn.Value) (emitExpr None map arg.Value)
    | EFun ({Value = EVar name}, body) ->
        let var = getNewVar ()
        sprintf "function(%s)\nlocal %s\n%s\nreturn %s\nend" name var (emitExpr (Some var) map body.Value) var
    | ELet ({Value = EVar name}, value, body) ->
        match oAssignVar with
        | None when isStatement value.Value ->
            sprintf "local %s\n%s\n%s" name (emitExpr (Some name) map value.Value) (emitExpr oAssignVar map body.Value)
        | Some assignName when assignName = name -> 
            sprintf "%s = %s\n%s" name (emitExpr None map value.Value) (emitExpr oAssignVar map body.Value)
        | _ ->
            sprintf "local %s = %s\n%s" name (emitExpr None map value.Value) (emitExpr oAssignVar map body.Value)
    | ERecordSelect (record, field) ->
        sprintf "%s.%s" (emitExpr None map record.Value) field
    | ERecordExtend (field, value, record) ->
        sprintf "table.add(%s, '%s', %s)" (emitExpr None map record.Value) field (emitExpr None map value.Value)
    | ERecordRestrict (record, field) ->
        sprintf "table.remove(%s, '%s')" (emitExpr None map record.Value) field
    | ERecordEmpty -> "{}"
    | EVariant (name, value) ->
        sprintf "{ variant_name = '%s', variant_%s = %s }" name name (emitExpr None map value.Value)
    | ECase (value, cases, oDefault) ->
        emitCaseExpr oAssignVar map value.Value cases oDefault
    | EIfThenElse (i, t, e) ->
        match oAssignVar with
        | None -> 
            let var = getNewVar ()
            sprintf "local %s\nif %s then\n%s\nelse\n%s\nend" var (emitExpr None map i.Value) (emitExpr (Some var) map t.Value) (emitExpr (Some var) map e.Value)
        | Some var -> 
            let var = getVar var
            sprintf "if %s then\n%s\nelse\n%s\nend" (emitExpr None map i.Value) (emitExpr (Some var) map t.Value) (emitExpr (Some var) map e.Value)
    | EBinOp (l, op, r) ->
        sprintf "%s %s %s" (emitExpr None map l.Value) (emitBinop op) (emitExpr None map r.Value)
    | EUnOp (op, e) ->
        sprintf "%s%s" (emitUnop op) (emitExpr None map e.Value)
    | EFix name -> sprintf "fix(%s)" name
    // | EListEmpty
    // | EListCons of Expr * Expr
    // | EOpen of string
    // | EType of Expr * Ty
    | EPrint e -> sprintf "print(%s)" (emitExpr None map e.Value)
    | _ -> failwithf "impossible, got %O" expr

    |> (fun result ->
        match oAssignVar with
        // | Some assignVar when isSingleLineExpr expr -> sprintf "%s = %s" assignVar result
        | Some assignVar when not (isStatement expr) -> 
            let assignVar = getVar assignVar
            sprintf "%s = %s" assignVar result
        | _ -> result
    )

let emitPrelude =
    [
        "function table.copy(t)"
        "    local u = {}"
        "    for k, v in pairs(t) do u[k] = v end"
        "    return u"
        "end"
        "function table.add(t, k, v)"
        "    local u = table.copy(t)"
        "    u[k] = v"
        "    return u"
        "end"
        "function table.remove(t, k)"
        "    local u = table.copy(t)"
        "    u[k] = nil"
        "    return u"
        "end"
        "function table.inspect(t)"
        "    for k, v in pairs(t) do print(k, v) end"
        "end"
        "function fix(f)"
        "    return function(...)"
        "        return (function(x) return x(x) end)(function(x) return f(function(y) return x(x)(y) end) end)(...)"
        "    end"
        "end"
    ]
    |> String.concat " "

let emit expr =
    emitPrelude + "\n\n" + emitExpr None Map.empty expr