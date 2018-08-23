module TestEval

open System
open System.IO

open Xunit
open Xunit.Abstractions

open Eval
open Expr
open Util

type Result =
    | OK of Value
    | Fail

let record fields = VRecord (Map.ofList fields)

let tests = [
    ("1", OK (VInt 1));
    ("-1", OK (VInt (-1)));
    ("true", OK (VBool true));
    ("false", OK (VBool false));
    ("3.14", OK (VFloat 3.14));
    ("-3.14", OK (VFloat (-3.14)));
    ("1.", OK (VFloat 1.));
    ("let a = 1 in a", OK (VInt 1));
    ("let f = fun a -> a in f 1", OK (VInt 1));
    ("{}", OK (VRecord Map.empty))
    ("{ a = 1 }", OK (record ["a", VInt 1]))
    ("{ a = 1 | { b = 2 } }", OK (record ["a", VInt 1; "b", VInt 2]))
    ("{ { a = 1 } - a }", OK (VRecord Map.empty))
    ("{ a = 1 }.a", OK (VInt 1))
    (":a 1", OK (VVariant ("a", VInt 1)))
]

type TestEval (output: ITestOutputHelper) =

    [<Fact>]
    member x.TestEval () =
        tests
        |> List.iter (fun (input, expected) ->
            let result =
                try
                    Parser.readExpr input
                    |> eval
                    |> OK
                with e ->
                    Fail
            if result <> expected then
                output.WriteLine(sprintf "TestEval: %s failed" input)
            Assert.StrictEqual(expected, result)
        )
