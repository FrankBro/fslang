module Test

open System
open System.IO

open Xunit
open Xunit.Abstractions

open Eval
open Error
open Expr
open TestUtil
open Util

[<Fact>]
let ``Match variant`` () =
    test
        "match :a 1 { :a a -> 1 , :y a -> 2 }"
        (POk (eCase ((eVariant ("a", EInt 1)), [eVariant ("a", EVar "a"), EInt 1, None;eVariant ("y", EVar "a"), EInt 2, None], None)))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Match open variant`` () =
    test
        "match :b 1 { :a a -> 1 | otherwise -> 2 }"
        (POk (eCase ((eVariant ("b", EInt 1)), [eVariant ("a", EVar "a"), EInt 1, None], Some ("otherwise", EInt 2))))
        (IOk "int")
        (EOk (VInt 2))

[<Fact>]
let ``Record pattern`` () =
    test
        "let { a = a } = { a = 1 } in a"
        (POk (eLet (eRecord ["a", EVar "a"], eRecord ["a", EInt 1], EVar "a")))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Record pattern multiple unordered fields`` () =
    test
        "let { a = a, b = b } = { b = 2, a = 1 } in a + b"
        (POk (eLet (eRecord ["a", EVar "a"; "b", EVar "b"], eRecord ["b", EInt 2; "a", EInt 1], eBinOp (EVar "a", Plus, EVar "b"))))
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Record patterns dont need all the fields`` () =
    test
        "let { a = a } = { a = 1, b = 2 } in a"
        (POk (eLet (eRecord ["a", EVar "a"], eRecord ["a", EInt 1; "b", EInt 2], EVar "a")))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``More complex record pattern`` () =
    test
        "let { a = a | r } = { b = 2, a = 1 } in r.b"
        (POk (eLet (eRecordWith (EVar "r", ["a", EVar "a"]), eRecord ["b", EInt 2; "a", EInt 1], eRecordSelect (EVar "r", "b"))))
        (IOk "int")
        (EOk (VInt 2))

[<Fact>]
let ``Record pattern in lambda`` () =
    test
        "let f = fun { a = a } -> a in f { a = 1 }"
        (POk (eLet (EVar "f", eFun (eRecord ["a", EVar "a"], EVar "a"), eCall (EVar "f", eRecord ["a", EInt 1]))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Imbricked records`` () =
    test
        "let { a = { b = b } } = { a = { b = 2 } } in b"
        (POk (eLet (eRecord ["a", eRecord ["b", EVar "b"]],
                    eRecord ["a", eRecord ["b", EInt 2]],
                    EVar "b")))
        (IOk "int")
        (EOk (VInt 2))

[<Fact>]
let ``Variant pattern`` () =
    test
        "let (:a a) = (:a 1) in a"
        (POk (eLet (eVariant ("a", EVar "a"), eVariant ("a", EInt 1), EVar "a")))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Bad variant pattern`` () =
    test
        "let (:b b) = (:a 1) in b"
        (POk (eLet (eVariant ("b", EVar "b"), eVariant ("a", EInt 1), EVar "b")))
        (IFail (i RowTypeExpected))
        (EFail (e (BadVariantPattern ("b", "a"))))

[<Fact>]
let ``Variant pattern in lambda`` () =
    test
        "let f = fun (:a a) -> a in f (:a 1)"
        (POk (eLet (EVar "f", eFun (eVariant ("a", EVar "a"), EVar "a"), eCall (EVar "f", eVariant ("a", EInt 1)))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Bad variant pattern in lambda`` () =
    test
        "let f = fun (:b b) -> b in f (:a 1)"
        (POk (eLet (EVar "f", eFun (eVariant ("b", EVar "b"), EVar "b"), eCall (EVar "f", eVariant ("a", EInt 1)))))
        ISkip
        (EFail (e (BadVariantPattern ("b", "a"))))

[<Fact>]
let ``Record pattern in match`` () =
    test
        "match :a { a = 1 } { :a { a = a } -> a }"
        (POk (eCase (eVariant ("a", eRecord ["a", EInt 1]), [eVariant ("a", eRecord ["a", EVar "a"]), EVar "a", None], None)))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Variant pattern in match`` () =
    test
        "match :a (:b 2) { :a (:b b) -> b }"
        (POk (eCase (eVariant ("a", eVariant ("b", EInt 2)), [eVariant ("a", eVariant ("b", EVar "b")), EVar "b", None], None)))
        (IOk "int")
        (EOk (VInt 2))

[<Fact>]
let ``Function sugar in let`` () =
    test
        "let f a b = a + b in f 1 2"
        (POk (eLet (EVar "f", eFun (EVar "a", eFun (EVar "b", eBinOp (EVar "a", Plus, EVar "b"))), eCall (eCall (EVar "f", EInt 1), EInt 2))))
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Function multiple args`` () =
    test
        "let f = fun a b -> a + b in f 1 2"
        (POk (eLet (EVar "f", eFun (EVar "a", eFun (EVar "b", eBinOp (EVar "a", Plus, EVar "b"))), eCall (eCall (EVar "f", EInt 1), EInt 2))))
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Binop a record field`` () =
    test
        "let r = { x = 0 } in r.x + 1"
        (POk (eLet (EVar "r", eRecord ["x", EInt 0], eBinOp (eRecordSelect (EVar "r", "x"), Plus, EInt 1))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Record match sugar`` () =
    test
        "let f {x,y} = x + y in f { x = 1, y = 2 }"
        (POk (eLet (EVar "f", eFun (eRecord ["x", EVar "x"; "y", EVar "y"], eBinOp (EVar "x", Plus, EVar "y")), eCall (EVar "f", eRecord ["x", EInt 1; "y", EInt 2]))))
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Record match to construct`` () =
    test
        "let x = 1 in let y = 2 in {x,y}"
        (POk (eLet (EVar "x", EInt 1, eLet (EVar "y", EInt 2, eRecord ["x", EVar "x"; "y", EVar "y"]))))
        (IOk "{x : int, y : int}")
        (EOk (VRecord (["x", VInt 1; "y", VInt 2] |> Map.ofList)))

[<Fact>]
let ``Record restriction is infered on extension`` () =
    test
        "fun r -> { x = 0 | r }"
        (POk (eFun (EVar "r", eRecordWith (EVar "r", ["x", EInt 0]))))
        (IOk "forall r. (r\\x) => {r} -> {x : int | r}")
        ESkip

[<Fact>]
let ``Record restriction is infered on selection`` () =
    test
        "fun r -> r.x"
        (POk (eFun (EVar "r", eRecordSelect (EVar "r", "x"))))
        (IOk "forall a r. (r\\x) => {x : a | r} -> a")
        ESkip

[<Fact>]
let ``Record restriction is infered on restriction`` () =
    test
        "fun r -> r\\x"
        (POk (eFun (EVar "r", eRecordRestrict (EVar "r", "x"))))
        (IOk "forall a r => {x : a | r} -> {r}")
        ESkip

[<Fact>]
let ``Variant restriction on literal`` () =
    test
        ":a 0"
        (POk (eVariant ("a", EInt 0)))
        (IOk "forall r. (r\\a) => <a : int | r>")
        (EOk (VVariant ("a", VInt 0)))

[<Fact>]
let ``Variant restriction on closed match`` () =
    test
        "fun r -> match r { :x x -> 0 }"
        (POk (eFun (EVar "r", eCase (EVar "r", [eVariant ("x", EVar "x"), EInt 0, None], None))))
        (IOk "forall a => <x : a> -> int")
        ESkip

[<Fact>]
let ``Variant restriction on open match`` () =
    test
        "fun r -> match r { :x x -> 0 | otherwise -> 1 }"
        (POk (eFun (EVar "r", eCase (EVar "r", [eVariant ("x", EVar "x"), EInt 0, None], Some ("otherwise", EInt 1)))))
        (IOk "forall a r. (r\\x) => <x : a | r> -> int")
        ESkip

[<Fact>]
let ``If variant restriction`` () =
    test
        "if true then :a 0 else :b 1"
        (POk (eIfThenElse (EBool true, eVariant ("a", EInt 0), eVariant ("b", EInt 1))))
        (IOk "forall r. (r\\a\\b) => <a : int, b : int | r>")
        (EOk (VVariant ("a", VInt 0)))

[<Fact>]
let ``Record restriction for multiple fields`` () =
    test
        "fun r -> { x = 0, y = 0 | r }"
        (POk (eFun (EVar "r", eRecordWith (EVar "r", ["y", EInt 0; "x", EInt 0]))))
        (IOk "forall r. (r\\x\\y) => {r} -> {x : int, y : int | r}")
        ESkip

[<Fact>]
let ``Record arg sugar bug`` () =
    test
        "let f {x,y} = x + y in 
         let x = 1 in 
         let y = 2 in 
         f {x,y}"
        PSkip
        (IOk "int")
        (EOk (VInt 3))

[<Fact>]
let ``Same field in record twice is invalid`` () =
    test
        "{x = 0, x = 1}"
        (POk (eRecord ["x", EInt 1; "x", EInt 0]))
        (IFail (i (RowConstraintFail "x")))
        ESkip

[<Fact>]
let ``If expressions can just use a boolean variable`` () =
    test
        "let f bool = if bool then 1 else 0 in f true"
        (POk (eLet (EVar "f", eFun (EVar "bool", eIfThenElse (EVar "bool", EInt 1, EInt 0)), eCall (EVar "f", EBool true))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Record equality works`` () =
    test
        "{ x = 0 } = { x = 0 }"
        (POk (eBinOp (eRecord ["x", EInt 0], Equal, eRecord ["x", EInt 0])))
        (IOk "bool")
        (EOk (VBool true))

// Shitty that I need parenthesis here
[<Fact>]
let ``Variant equality works`` () =
    test
        "(:a 0) = (:a 0)"
        (POk (eBinOp (eVariant ("a", EInt 0), Equal, eVariant ("a", EInt 0))))
        (IOk "bool")
        (EOk (VBool true))

[<Fact>]
let ``Record update`` () =
    test
        "let a = { a = 0 } in { a := 1 | a }.a"
        (POk (eLet (EVar "a", eRecord ["a", EInt 0], eRecordSelect (eRecordWith (eRecordRestrict (EVar "a", "a"), ["a", EInt 1]), "a"))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Match in function bug`` () =
    test
        "let f def v = match v { :just value -> value, :none {} -> def }"
        PSkip
        ISkip
        ESkip

[<Fact>]
let ``Variant match with pattern guard`` () =
    test
        "match :a 1 { :a a when a = 0 -> 0, :a a -> a }"
        (POk (eCase (eVariant ("a", EInt 1), [eVariant ("a", EVar "a"), EInt 0, Some (eBinOp (EVar "a", Equal, EInt 0)); eVariant ("a", EVar "a"), EVar "a", None], None)))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Pattern match on record with guard`` () =
    let a = (eRecord ["a", EVar "a"; "b", EVar "b"], EVar "b", Some (eBinOp (EVar "a", Equal, EInt 1)))
    let b = (eRecord ["a", EVar "a"; "b", EVar "b"], EVar "a", None)
    test
        "match { a = 0, b = 1 } { { a = a, b = b } when a = 1 -> b, { a = a, b = b } -> a }"
        (POk (eCase (eRecord ["a", EInt 0; "b", EInt 1], [a; b], None)))
        (IOk "int")
        (EOk (VInt 0))
        
[<Fact>]
let ``Pattern match on int`` () =
    test
        "match 1 { a when a = 0 -> 0, a when a = 2 -> 2 | otherwise -> otherwise }"
        (POk (eCase (EInt 1, [EVar "a", EInt 0, Some (eBinOp (EVar "a", Equal, EInt 0)); EVar "a", EInt 2, Some (eBinOp (EVar "a", Equal, EInt 2))], Some ("otherwise", EVar "otherwise"))))
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Var pattern matching var switch is not a problem`` () =
    let a = (eRecord ["a", EVar "a"; "b", EVar "b"], EVar "a", None)
    let b = (eRecord ["a", EVar "b"; "b", EVar "a"], EVar "b", None)
    test
        "match { a = 0, b = false } { { a = a, b = b } -> a, { a = b, b = a } -> b }"
        (POk (eCase (eRecord ["a", EInt 0; "b", EBool false], [a; b], None)))
        (IOk "int")
        (EOk (VInt 0))

[<Fact>]
let ``Variant pattern match var reuse bug`` () =
    test
        "let f v = match v { :a a when a = 0 -> a, :b a when a = false -> 0 | otherwise -> 0 }"
        PSkip
        (IOk "forall r. (r\\a\\b) => <a : int, b : bool | r> -> int")
        ESkip

[<Fact>]
let ``Unary negative work on int`` () =
    test
        "let a = 1 in -a"
        (POk (eLet (EVar "a", EInt 1, eUnOp (Negative, EVar "a"))))
        (IOk "int")
        (EOk (VInt -1))

[<Fact>]
let ``Unary negative work on float`` () =
    test
        "let a = 1.0 in -a"
        (POk (eLet (EVar "a", EFloat 1.0, eUnOp (Negative, EVar "a"))))
        (IOk "float")
        (EOk (VFloat -1.0))

[<Fact>]
let ``Parse inner functions`` () =
    test
        "let map f i = f i in map"
        PSkip
        (IOk "forall a b => (a -> b) -> a -> b")
        ESkip

[<Fact>]
let ``Fix works`` () =
    test
        "let yfact fact n = if n > 0 then n * fact(n-1) else 1 in let fact = fix yfact in fact 5"
        PSkip
        (IOk "int")
        (EOk (VInt 120))

[<Fact>]
let ``Fix multiarg`` () =
    test
        "let ydiff diff a b = if a < b then diff b a else a in let diff = fix ydiff in diff 3 10"
        PSkip
        (IOk "int")
        (EOk (VInt 10))

[<Fact>]
let ``Rec sugar`` () =
    test
        "let rec fact n = if n > 0 then n * fact(n-1) else 1 in fact 5"
        PSkip
        (IOk "int")
        (EOk (VInt 120))

[<Fact>]
let ``Empty list`` () =
    test
        "[]"
        (POk EListEmpty)
        (IOk "forall a => [a]")
        (EOk (VList []))

[<Fact>]
let ``Cons list`` () =
    test
        "1 :: []"
        (POk (eList [EInt 1]))
        (IOk "[int]")
        (EOk (VList [VInt 1]))

[<Fact>]
let ``Multiple cons list`` () =
    test
        "1 :: 2 :: 3 :: []"
        (POk (eList [EInt 1; EInt 2; EInt 3]))
        (IOk "[int]")
        (EOk (VList [VInt 1; VInt 2; VInt 3]))

[<Fact>]
let ``List init`` () =
    test
        "[1, 2, 3]"
        (POk (eList [EInt 1; EInt 2; EInt 3]))
        (IOk "[int]")
        (EOk (VList [VInt 1; VInt 2; VInt 3]))

[<Fact>]
let ``Pattern match sugar for record`` () =
    test
        "match { a = 1 } { { a = 2 } -> 2 | otherwise -> 1 }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Pattern match sugar for variant`` () =
    test
        "match :a 1 { :a 2 -> 2 | otherwise -> 1 }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Pattern match for list`` () =
    test
        "match [1] { [] -> 0, (x :: xs) -> x }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Sum`` () =
    test
        "let rec sum state xs = match xs { [] -> state, x :: xs -> sum (x + state) xs } in sum 10 [1,2,3]"
        PSkip
        (IOk "int")
        (EOk (VInt 16))

[<Fact>]
let ``Bool match`` () =
    test
        "match true { false -> 0, true -> 1 }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Int match`` () =
    test
        "match 1 { 0 -> 0, 1 -> 1 }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``Float match`` () =
    test
        "match 1.0 { 0.0 -> 0, 1.0 -> 1 }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))

[<Fact>]
let ``String match`` () =
    test
        "match \"1\" { \"0\" -> 0, \"1\" -> 1 }"
        PSkip
        (IOk "int")
        (EOk (VInt 1))
