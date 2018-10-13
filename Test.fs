module Test

open System
open System.IO

open Xunit
open Xunit.Abstractions

open Eval
open Error
open Expr
open Util

type ParseResult =
    | POk of Expr
    | PFail of OrdoError

type InferResult =
    | IOk of Ty
    | IFail of OrdoError

type EvalResult =
    | EOk of Value
    | EFail of OrdoError

let test input parserExpected inferExpected evalExpected =
    let parserResult = 
        try
            Parser.readExpr input
            |> POk
        with
        | OrdoException error -> PFail error
    Assert.StrictEqual(parserExpected, parserResult)
    let inferResult =
        match parserResult with
        | PFail e -> IFail e
        | POk expr ->
            try
                Infer.infer expr
                |> IOk
            with
            | OrdoException error -> IFail error
    Assert.StrictEqual(inferExpected, inferResult)
    let evalResult =
        match parserResult with
        | PFail e -> EFail e
        | POk expr ->
            try
                Eval.eval expr
                |> EOk
            with
            | OrdoException error -> EFail error
    Assert.StrictEqual(evalExpected, evalResult)

let g e = OrdoError.Generic e
let e e = OrdoError.Eval e
let i e = OrdoError.Infer e

let eRecord xs =
    (ERecordEmpty, xs)
    ||> List.fold (fun record (label, value) ->
        ERecordExtend (label, value, record)
    )

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

[<Fact>]
let ``Positive integer`` () =
    test 
        "1"
        (POk (EInt 1))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Negative integer`` () =
    test 
        "-1"
        (POk (EInt -1))
        (IOk (TConst "int"))
        (EOk (VInt -1))

[<Fact>]
let ``Positive float`` () =
    test 
        "3.14"
        (POk (EFloat 3.14))
        (IOk (TConst "float"))
        (EOk (VFloat 3.14))

[<Fact>]
let ``Negative float`` () =
    test 
        "-3.14"
        (POk (EFloat -3.14))
        (IOk (TConst "float"))
        (EOk (VFloat -3.14))

[<Fact>]
let ``Float that stops at dot`` () =
    test 
        "3."
        (POk (EFloat 3.))
        (IOk (TConst "float"))
        (EOk (VFloat 3.))

[<Fact>]
let ``Boolean true`` () =
    test
        "true"
        (POk (EBool true))
        (IOk (TConst "bool"))
        (EOk (VBool true))

[<Fact>]
let ``Boolean false`` () =
    test
        "false"
        (POk (EBool false))
        (IOk (TConst "bool"))
        (EOk (VBool false))

[<Fact>]
let ``Unbound variable`` () =
    test
        "a"
        (POk (EVar "a"))
        (IFail (g (VariableNotFound "a")))
        (EFail (g (VariableNotFound "a")))

[<Fact>]
let ``Simple function call`` () =
    test
        "f x"
        (POk (ECall (EVar "f", EVar "x")))
        (IFail (g (VariableNotFound "f")))
        (EFail (g (VariableNotFound "f")))

[<Fact>]
let ``Function call with multiple args`` () =
    test
        "f x y"
        (POk (ECall (ECall (EVar "f", EVar "x"), EVar "y")))
        (IFail (g (VariableNotFound "f")))
        (EFail (g (VariableNotFound "f")))

[<Fact>]
let ``Simple let`` () =
    test
        "let a = 1 in a"
        (POk (ELet (EVar "a", EInt 1, EVar "a")))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Let call function`` () =
    test
        "let f = fun a -> a in f 1"
        (POk (ELet (EVar "f", EFun (EVar "a", EVar "a"), ECall (EVar "f", EInt 1))))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Empty record`` () =
    test
        "{}"
        (POk (eRecord []))
        (IOk (tRecord []))
        (EOk (vRecord []))

[<Fact>]
let ``Record restrict`` () =
    test
        "let r = { a = 1 } in { r - a }"
        (POk (ELet (EVar "r", eRecord ["a", EInt 1], ERecordRestrict (EVar "r", "a"))))
        (IOk (tRecord []))
        (EOk (vRecord []))

[<Fact>]
let ``Record extend`` () =
    test
        "let r = { a = 1 } in { b = 2 | r }"
        (POk (ELet (EVar "r", eRecord ["a", EInt 1], ERecordExtend ("b", EInt 2, EVar "r"))))
        (IOk (tRecord ["a", TConst "int"; "b", TConst "int"]))
        (EOk (vRecord ["a", VInt 1; "b", VInt 2]))

[<Fact>]
let ``Record select`` () =
    test
        "let r = { a = 1 } in r.a"
        (POk (ELet (EVar "r", eRecord ["a", EInt 1], ERecordSelect (EVar "r", "a"))))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Variant`` () =
    test
        ":a 1"
        (POk (EVariant ("a", EInt 1)))
        (IOk (tVariant ["a", TConst "int"]))
        (EOk (VVariant ("a", VInt 1)))

[<Fact>]
let ``Match variant`` () =
    test
        "match :a 1 { :a a -> 1 | :y a -> 2 }"
        (POk (ECase ((EVariant ("a", EInt 1)), ["a", EVar "a", EInt 1;"y", EVar "a", EInt 2], None)))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Match open variant`` () =
    test
        "match :b 1 { :a a -> 1 | otherwise -> 2 }"
        (POk (ECase ((EVariant ("b", EInt 1)), ["a", EVar "a", EInt 1], Some (EVar "otherwise", EInt 2))))
        (IOk (TConst "int"))
        (EOk (VInt 2))

[<Fact>]
let ``If then else`` () =
    test
        "if true then 1 else 0"
        (POk (EIfThenElse (EBool true, EInt 1, EInt 0)))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``If value must be bool`` () =
    test
        "if 1 then 1 else 0"
        (POk (EIfThenElse (EInt 1, EInt 1, EInt 0)))
        (IFail (g IfValueNotBoolean))
        (EFail (g IfValueNotBoolean))

[<Fact>]
let ``Record pattern`` () =
    test
        "let { a = a } = { a = 1 } in a"
        (POk (ELet (eRecord ["a", EVar "a"], eRecord ["a", EInt 1], EVar "a")))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Record pattern multiple unordered fields`` () =
    test
        "let { a = a, b = b } = { b = 2, a = 1 } in a + b"
        (POk (ELet (eRecord ["a", EVar "a"; "b", EVar "b"], eRecord ["b", EInt 2; "a", EInt 1], EBinOp (EVar "a", Plus, EVar "b"))))
        (IOk (TConst "int"))
        (EOk (VInt 3))

[<Fact>]
let ``Record patterns dont need all the fields`` () =
    test
        "let { a = a } = { a = 1, b = 2 } in a"
        (POk (ELet (ERecordExtend ("a", EVar "a", ERecordEmpty), eRecord ["a", EInt 1; "b", EInt 2], EVar "a")))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``More complex record pattern`` () =
    test
        "let { a = a | r } = { b = 2, a = 1 } in r.b"
        (POk (ELet (ERecordExtend ("a", EVar "a", EVar "r"), eRecord ["b", EInt 2; "a", EInt 1], ERecordSelect (EVar "r", "b"))))
        (IOk (TConst "int"))
        (EOk (VInt 2))

let gen id = TVar {contents = Generic id}

[<Fact>]
let ``Record pattern in lambda`` () =
    test
        "let f = fun { a = a } -> a in f { a = 1 }"
        (POk (ELet (EVar "f", EFun (ERecordExtend ("a", EVar "a", ERecordEmpty), EVar "a"), ECall (EVar "f", ERecordExtend ("a", EInt 1, ERecordEmpty)))))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Imbricked records`` () =
    test
        "let { a = { b = b } } = { a = { b = 2 } } in b"
        (POk (ELet (ERecordExtend ("a", ERecordExtend ("b", EVar "b", ERecordEmpty), ERecordEmpty), 
                    ERecordExtend ("a", ERecordExtend ("b", EInt 2, ERecordEmpty), ERecordEmpty),
                    EVar "b")))
        (IOk (TConst "int"))
        (EOk (VInt 2))

[<Fact>]
let ``Variant pattern`` () =
    test
        "let :a a = :a 1 in a"
        (POk (ELet (EVariant ("a", EVar "a"), EVariant ("a", EInt 1), EVar "a")))
        (IOk (TConst "int"))
        (EOk (VInt 1))

// TODO This probably should infer correctly, even if it makes little sense, should be generic
[<Fact>]
let ``Bad variant pattern`` () =
    test
        "let :b b = :a 1 in b"
        (POk (ELet (EVariant ("b", EVar "b"), EVariant ("a", EInt 1), EVar "b")))
        (IFail (i RowTypeExpected))
        (EFail (e (BadVariantPattern ("b", "a"))))

[<Fact>]
let ``Variant pattern in lambda`` () =
    test
        "let f = fun (:a a) -> a in f (:a 1)"
        (POk (ELet (EVar "f", EFun (EVariant ("a", EVar "a"), EVar "a"), ECall (EVar "f", EVariant ("a", EInt 1)))))
        (IOk (TConst "int"))
        (EOk (VInt 1))

[<Fact>]
let ``Plus integer`` () =
    test
        "1 + 2"
        (POk (EBinOp (EInt 1, Plus, EInt 2)))
        (IOk (TConst "int"))
        (EOk (VInt 3))

[<Fact>]
let ``Plus float`` () =
    test
        "1. + 2."
        (POk (EBinOp (EFloat 1., Plus, EFloat 2.)))
        (IOk (TConst "float"))
        (EOk (VFloat 3.))

[<Fact>]
let ``Binop fail`` () =
    test
        "1 + 2."
        (POk (EBinOp (EInt 1, Plus, EFloat 2.)))
        (IFail (i (UnifyFail (TConst "int", TConst "float"))))
        (EFail (e BadBinOp))

// [<Fact>]
// let ``Record pattern in match`` () =
//     test
//         "match :a { a = 1 } { :a { a = a } -> a }"
//         (POk (ECase ((EVariant ("a", eRecord ["a", EInt 1])), ["a", eRecord ["a", EVar "a"], EVar "a"], None)))
//         (IOk (TConst "int"))
//         (EOk (VInt 1))