module TestAnnotation

open Xunit

open Error
open Expr
open TestUtil

[<Fact>]
let ``Let ann`` () =
    test 
        "let (a: int) = 1 in a"
        (POk (eLet (eType (EVar "a", TInt), EInt 1, EVar "a")))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Let wrong ann`` () =
    test 
        "let (a: float) = 1 in a"
        (POk (eLet (eType (EVar "a", TFloat), EInt 1, EVar "a")))
        (IFail (i (UnifyFail (TFloat, TInt))))
        (EOk (VInt 1))

[<Fact>]
let ``Fun ann`` () =
    test
        "let f = fun (a: int) -> a + 1 in f 1"
        PSkip
        (IOk "int")
        (EOk (VInt 2))

[<Fact>]
let ``Fun wrong ann`` () =
    test
        "let f = fun (a: float) -> a + 1 in f 1"
        PSkip
        (IFail (i (UnifyFail (TFloat, TInt))))
        (EOk (VInt 2))

[<Fact>]
let ``Fun sugar ann`` () =
    test
        "let f (a: int) = a + 1 in f 1"
        PSkip
        (IOk "int")
        (EOk (VInt 2))

[<Fact>]
let ``Fun sugar wrong ann`` () =
    test
        "let f (a: float) = a + 1 in f 1"
        PSkip
        (IFail (i (UnifyFail (TFloat, TInt))))
        (EOk (VInt 2))
