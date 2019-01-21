module TestUtil

open Xunit

open Error
open Expr

type ParseResult =
    | POk of Expr
    | PSkip
    | PFail of OrdoError

type InferResult =
    | IOk of string
    | ISkip
    | IFail of OrdoError

type EvalResult =
    | EOk of Value
    | ESkip
    | EFail of OrdoError

let test input parserExpected inferExpected evalExpected =
    let parserResult = 
        try
            ParserExpr.readExpr input
            |> POk
        with
        | OrdoException error -> PFail error
    if parserExpected <> PSkip then
        Assert.StrictEqual(parserExpected, parserResult)
    let inferResult =
        match parserResult with
        | PSkip -> failwith "Impossible"
        | PFail e -> IFail e
        | POk expr ->
            try
                Infer.infer Map.empty expr
                |> stringOfTy
                |> IOk
            with
            | OrdoException error -> IFail error
    if inferExpected <> ISkip then
        Assert.StrictEqual(inferExpected, inferResult)
    let evalResult =
        match parserResult with
        | PSkip -> failwith "Impossible"
        | PFail e -> EFail e
        | POk expr ->
            try
                Eval.eval Map.empty expr
                |> EOk
            with
            | OrdoException error -> EFail error
    if evalExpected <> ESkip then 
        Assert.StrictEqual(evalExpected, evalResult)

let g e = OrdoError.Generic e
let e e = OrdoError.Eval e
let i e = OrdoError.Infer e

let eLocated e = { Filename = "test"; Start = { Line = 0; Column = 0 }; End = { Line = 0; Column = 0}; Value = e }

let eRecordWith (x, xs) =
    (x, xs)
    ||> List.fold (fun record (label, value) ->
        ERecordExtend (label, eLocated value, eLocated record)
    )
let eRecord xs = eRecordWith (ERecordEmpty, xs)

let eVariant (name, value) = EVariant (name, eLocated value)
let eCase (pattern, cases, oDefault) = 
    let cases =
        cases
        |> List.map (fun (pattern, body, oGuard) ->
            eLocated pattern, eLocated body, oGuard |> Option.map eLocated
        )
    ECase (eLocated pattern, cases, oDefault |> Option.map (fun (name, body) -> name, eLocated body))
let eLet (pattern, value, body) = ELet (eLocated pattern, eLocated value, eLocated body)
let eRecordSelect (record, name) = ERecordSelect (eLocated record, name)
let eBinOp (a, op, b) = EBinOp (eLocated a, op, eLocated b)
let eFun (pattern, body) = EFun (eLocated pattern, eLocated body)
let eCall (fn, arg) = ECall (eLocated fn, eLocated arg)
let eRecordRestrict (record, name) = ERecordRestrict (eLocated record, name)
let eIfThenElse (i, t, e) = EIfThenElse (eLocated i, eLocated t, eLocated e)
let eUnOp (op, e) = EUnOp (op, eLocated e)
let eList xs = 
    (EListEmpty, xs)
    ||> List.fold (fun list element ->
        EListCons (eLocated element, eLocated list)
    )
let eType (e, t) = EType (eLocated e, t)
let ePrint e = EPrint (eLocated e)

let tRecord xs =
    (TRowEmpty, xs)
    ||> List.fold (fun record (label, value) ->
        TRowExtend (label, value, record)
    )
    |> TRecord

let tVariant xs =
    (TVar {contents = Generic 0}, xs)
    ||> List.fold (fun variant (label, value) ->
        TRowExtend (label, value, variant)
    )
    |> TVariant

let vRecord xs =
    (Map.empty, xs)
    ||> List.fold (fun record (label, value) ->
        Map.add label value record
    )
    |> VRecord
