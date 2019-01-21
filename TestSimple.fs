module TestSimple

open Xunit

open Error
open Expr
open TestUtil

[<Fact>]
let ``Positive integer`` () =
    test 
        "1"
        (POk (EInt 1))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Negative integer`` () =
    test 
        "-1"
        (POk (eUnOp (Negative, EInt 1)))
        (IOk "int")
        (EOk (VInt -1))

[<Fact>]
let ``Positive float`` () =
    test 
        "3.14"
        (POk (EFloat 3.14))
        (IOk "float")
        (EOk (VFloat 3.14))

[<Fact>]
let ``Negative float`` () =
    test 
        "-3.14"
        (POk (eUnOp (Negative, EFloat 3.14)))
        (IOk "float")
        (EOk (VFloat -3.14))

[<Fact>]
let ``Float that stops at dot`` () =
    test 
        "3."
        (POk (EFloat 3.))
        (IOk "float")
        (EOk (VFloat 3.))

[<Fact>]
let ``Boolean true`` () =
    test
        "true"
        (POk (EBool true))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Boolean false`` () =
    test
        "false"
        (POk (EBool false))
        (IOk "bool")
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
        (POk (eCall (EVar "f", EVar "x")))
        (IFail (g (VariableNotFound "f")))
        (EFail (g (VariableNotFound "f")))

[<Fact>]
let ``Function call with multiple args`` () =
    test
        "f x y"
        (POk (eCall (eCall (EVar "f", EVar "x"), EVar "y")))
        (IFail (g (VariableNotFound "f")))
        (EFail (g (VariableNotFound "f")))

[<Fact>]
let ``Simple let`` () =
    test
        "let a = 1 in a"
        (POk (eLet (EVar "a", EInt 1, EVar "a")))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Let call function`` () =
    test
        "let f = fun a -> a in f 1"
        (POk (eLet (EVar "f", eFun (EVar "a", EVar "a"), eCall (EVar "f", EInt 1))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Empty record`` () =
    test
        "{}"
        (POk (eRecord []))
        (IOk "{}")
        (EOk (vRecord []))

[<Fact>]
let ``Record restrict`` () =
    test
        "let r = { a = 1 } in r\\a"
        (POk (eLet (EVar "r", eRecord ["a", EInt 1], eRecordRestrict (EVar "r", "a"))))
        (IOk "{}")
        (EOk (vRecord []))

[<Fact>]
let ``Record extend`` () =
    test
        "let r = { a = 1 } in { b = 2 | r }"
        (POk (eLet (EVar "r", eRecord ["a", EInt 1], eRecordWith (EVar "r", ["b", EInt 2]))))
        (IOk "{a : int, b : int}")
        (EOk (vRecord ["a", VInt 1; "b", VInt 2]))

[<Fact>]
let ``Record select`` () =
    test
        "let r = { a = 1 } in r.a"
        (POk (eLet (EVar "r", eRecord ["a", EInt 1], eRecordSelect (EVar "r", "a"))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Variant`` () =
    test
        ":a 1"
        (POk (eVariant ("a", EInt 1)))
        (IOk "forall r. (r\\a) => <a : int | r>")
        (EOk (VVariant ("a", VInt 1)))

[<Fact>]
let ``If then else`` () =
    test
        "if true then 1 else 0"
        (POk (eIfThenElse (EBool true, EInt 1, EInt 0)))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``If value must be bool`` () =
    test
        "if 1 then 1 else 0"
        (POk (eIfThenElse (EInt 1, EInt 1, EInt 0)))
        (IFail (i (UnifyFail (TInt, TBool))))
        (EFail (g IfValueNotBoolean))

[<Fact>]
let ``Plus integer`` () =
    test
        "1 + 2"
        (POk (eBinOp (EInt 1, Plus, EInt 2)))
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Plus float`` () =
    test
        "1. + 2."
        (POk (eBinOp (EFloat 1., Plus, EFloat 2.)))
        (IOk "float")
        (EOk (VFloat 3.))

[<Fact>]
let ``Binop fail`` () =
    test
        "1 + 2."
        (POk (eBinOp (EInt 1, Plus, EFloat 2.)))
        (IFail (i (UnifyFail (TInt, TFloat))))
        (EFail (e BadBinOp))

[<Fact>]
let ``Minus integer`` () =
    test
        "3 - 2"
        (POk (eBinOp (EInt 3, Minus, EInt 2)))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Minus float`` () =
    test
        "3. - 2."
        (POk (eBinOp (EFloat 3., Minus, EFloat 2.)))
        (IOk "float")
        (EOk (VFloat 1.))

[<Fact>]
let ``Multiply integer`` () =
    test
        "3 * 2"
        (POk (eBinOp (EInt 3, Multiply, EInt 2)))
        (IOk "int")
        (EOk (VInt 6))

[<Fact>]
let ``Multiply float`` () =
    test
        "3. * 2."
        (POk (eBinOp (EFloat 3., Multiply, EFloat 2.)))
        (IOk "float")
        (EOk (VFloat 6.))

[<Fact>]
let ``Divide integer`` () =
    test
        "6 / 2"
        (POk (eBinOp (EInt 6, Divide, EInt 2)))
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Divide float`` () =
    test
        "6. / 2."
        (POk (eBinOp (EFloat 6., Divide, EFloat 2.)))
        (IOk "float")
        (EOk (VFloat 3.))
    
[<Fact>]
let ``And true`` () =
    test
        "true && true"
        (POk (eBinOp (EBool true, And, EBool true)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``And false`` () =
    test
        "true && false"
        (POk (eBinOp (EBool true, And, EBool false)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Or true`` () =
    test
        "true || false"
        (POk (eBinOp (EBool true, Or, EBool false)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Or false`` () =
    test
        "false || false"
        (POk (eBinOp (EBool false, Or, EBool false)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Integer Equal true`` () =
    test
        "1 = 1"
        (POk (eBinOp (EInt 1, Equal, EInt 1)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Integer Equal false`` () =
    test
        "1 = 2"
        (POk (eBinOp (EInt 1, Equal, EInt 2)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Float Equal true`` () =
    test
        "1. = 1."
        (POk (eBinOp (EFloat 1., Equal, EFloat 1.)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Float Equal false`` () =
    test
        "1. = 2."
        (POk (eBinOp (EFloat 1., Equal, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Bool Equal true`` () =
    test
        "true = true"
        (POk (eBinOp (EBool true, Equal, EBool true)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Bool Equal false`` () =
    test
        "true = false"
        (POk (eBinOp (EBool true, Equal, EBool false)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Integer NotEqual true`` () =
    test
        "1 <> 2"
        (POk (eBinOp (EInt 1, NotEqual, EInt 2)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Integer NotEqual false`` () =
    test
        "1 <> 1"
        (POk (eBinOp (EInt 1, NotEqual, EInt 1)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Float NotEqual true`` () =
    test
        "1. <> 2."
        (POk (eBinOp (EFloat 1., NotEqual, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Float NotEqual false`` () =
    test
        "1. <> 1."
        (POk (eBinOp (EFloat 1., NotEqual, EFloat 1.)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Bool NotEqual true`` () =
    test
        "true <> false"
        (POk (eBinOp (EBool true, NotEqual, EBool false)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Bool NotEqual false`` () =
    test
        "true <> true"
        (POk (eBinOp (EBool true, NotEqual, EBool true)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Integer Greater true`` () =
    test
        "2 > 1"
        (POk (eBinOp (EInt 2, Greater, EInt 1)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Integer Greater false`` () =
    test
        "1 > 2"
        (POk (eBinOp (EInt 1, Greater, EInt 2)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Float Greater true`` () =
    test
        "2. > 1."
        (POk (eBinOp (EFloat 2., Greater, EFloat 1.)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Float Greater false`` () =
    test
        "1. > 2."
        (POk (eBinOp (EFloat 1., Greater, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Integer GreaterEqual true`` () =
    test
        "2 >= 2"
        (POk (eBinOp (EInt 2, GreaterEqual, EInt 2)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Integer GreaterEqual false`` () =
    test
        "1 >= 2"
        (POk (eBinOp (EInt 1, GreaterEqual, EInt 2)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Float GreaterEqual true`` () =
    test
        "2. >= 2."
        (POk (eBinOp (EFloat 2., GreaterEqual, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Float GreaterEqual false`` () =
    test
        "1. >= 2."
        (POk (eBinOp (EFloat 1., GreaterEqual, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Integer Lesser true`` () =
    test
        "2 < 3"
        (POk (eBinOp (EInt 2, Lesser, EInt 3)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Integer Lesser false`` () =
    test
        "3 < 2"
        (POk (eBinOp (EInt 3, Lesser, EInt 2)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Float Lesser true`` () =
    test
        "2. < 3."
        (POk (eBinOp (EFloat 2., Lesser, EFloat 3.)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Float Lesser false`` () =
    test
        "3. < 2."
        (POk (eBinOp (EFloat 3., Lesser, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Integer LesserEqual true`` () =
    test
        "2 <= 2"
        (POk (eBinOp (EInt 2, LesserEqual, EInt 2)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Integer LesserEqual false`` () =
    test
        "3 <= 2"
        (POk (eBinOp (EInt 3, LesserEqual, EInt 2)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``Float LesserEqual true`` () =
    test
        "2. <= 2."
        (POk (eBinOp (EFloat 2., LesserEqual, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Float LesserEqual false`` () =
    test
        "3. <= 2."
        (POk (eBinOp (EFloat 3., LesserEqual, EFloat 2.)))
        (IOk "bool")
        (EOk (VBool false))

[<Fact>]
let ``String`` () =
    test
        "\"a\""
        (POk (EString "a"))
        (IOk "string")
        (EOk (VString "a"))

[<Fact>]
let ``Print`` () =
    test
        "print 3"
        (POk (ePrint (EInt 3)))
        (IOk "{}")
        (EOk (VRecord Map.empty))
