module Transform

open Error
open Expr

let currentId = ref 0

let nextId () =
    let id = !currentId
    currentId := id + 1
    id

let getNewVar () =
    let id = nextId ()
    sprintf "_var%d" id

let rec transformRowBinding var body expr =
    match expr with
    | EBool b -> failwith ""
    | EInt i -> failwith ""
    | EFloat f -> failwith ""
    | EString s -> failwith ""
    | EVar _  -> body
    | EVariant (_, {Value = EVar _}) -> 
        ECase (EVar var, [expr, body, None], None)
    | EVariant (case, sub) ->
        let subVar = getNewVar ()
        let subBody = transformRowBinding subVar body sub
        ECase (EVar var, [EVariant (case, EVar subVar), subBody, None], None)
    | ERecordExtend (name, EVar nameVar, record) ->
        let body = transformRowBinding var body record 
        ELet (EVar nameVar, ERecordSelect (EVar var, name), body)
    | ERecordExtend (name, sub, record) ->
        let recordBody = transformRowBinding var body record
        let subVar = getNewVar ()
        let subBody = transformRowBinding subVar recordBody sub
        ELet (EVar subVar, ERecordSelect (EVar var, name), subBody)
    | ERecordEmpty -> body
    | _ -> raise (genericError (InvalidPattern expr))

let isValueType expr =
    match expr with
    | EBool _
    | EInt _
    | EFloat _ 
    | EString _ -> true
    | _ -> false

let extractValueGuard var expr =
    match expr with
    | EBool _
    | EInt _
    | EFloat _
    | EString _ -> EBinOp (EVar var, BinOp.Equal, expr)
    | _ -> raise (genericError (InvalidPattern expr))

let rec extractGuards pattern guards =
    match pattern with
    | EVar _  -> pattern, guards
    | EVariant (_, EVar _) -> pattern, guards
    | EVariant (case, body) when isValueType body -> 
        let var = getNewVar ()
        let guard = extractValueGuard var body
        EVariant (case, EVar var), guard :: guards
    | EVariant (case, body) ->
        let body, guards = extractGuards body guards
        EVariant (case, body), guards
    | ERecordExtend (_, EVar _, record) -> extractGuards record guards
    | ERecordExtend (name, body, record) when isValueType body ->
        let var = getNewVar ()
        let record, guards = extractGuards record guards
        let guard = extractValueGuard var body
        ERecordExtend (name, EVar var, record), guard :: guards
    | ERecordExtend (name, body, record) ->
        let body, guards = extractGuards body guards
        let record, guards = extractGuards record guards
        ERecordExtend (name, body, record), guards
    | ERecordEmpty -> pattern, guards
    | _ -> raise (genericError (InvalidPattern pattern))

let isRowType expr =
    match expr with
    | EVariant _
    | ERecordExtend _
    | ERecordEmpty -> true
    | _ -> false

let rec transformExpr expr =
    match expr with
    | EIfThenElse (i, t, e) ->
        match i with
        | EVar _ -> EIfThenElse (i, transformExpr t, transformExpr e)
        | _ -> 
            let var = getNewVar ()
            ELet (EVar var, i, EIfThenElse (EVar var, transformExpr t, transformExpr e))
    | EFun (pattern, body) ->
        match pattern with
        | EVar _  -> EFun (pattern, transformExpr body)
        | EVariant _ 
        | ERecordExtend _ -> 
            let var = getNewVar ()
            let body = transformRowBinding var body pattern
            EFun (EVar var, body)
        | _ -> raise (genericError (InvalidPattern pattern))
    | ELet (EVar var, value, body) ->
        ELet (EVar var, transformExpr value, transformExpr body)
    | ELet (pattern, value, body) when isRowType pattern ->
            let var = 
                match value with
                | EVar var -> var
                | _ -> getNewVar ()
            let body = transformRowBinding var body pattern
            match value with
            | EVar _ -> transformExpr body
            | _ -> ELet (EVar var, transformExpr value, transformExpr body)
    | ECase (value, cases, oDefault) ->
        let var =
            match value with
            | EVar name -> name
            | _ -> getNewVar ()
        let fixedCases = 
            cases
            |> List.map (fun (pattern, body, oGuard) ->
                let guards =
                    match oGuard with
                    | None -> []
                    | Some previousGuards -> [previousGuards]
                let pattern, guards = extractGuards pattern guards
                let oGuard =
                    match guards with
                    | [] -> None
                    | guard :: [] -> Some guard
                    | guard :: guards ->
                        (guard, guards)
                        ||> List.fold (fun state guard ->
                            EBinOp (state, BinOp.And, guard)
                        )
                        |> Some
                pattern, body, oGuard
            )
        match value with
        | EVar name -> ECase (value, fixedCases, oDefault)
        | _ -> ELet (EVar var, value, ECase (EVar var, fixedCases, oDefault))
    | _ -> expr

let transform expr =
    currentId := 0
    transformExpr expr
