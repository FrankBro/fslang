module ParserUtil

open FParsec
open FParsec.CharParsers

open Expr

type Parser<'t> = Parser<'t, unit>

let locate file p =
    pipe3 getPosition p getPosition (fun p1 value p2 ->
        {
            Filename = file
            Start = { Line = int p1.Line; Column = int p1.Column }
            End = { Line = int p2.Line; Column = int p2.Column }
            Value = value
        }
    )


let (<!>) (p: Parser<_>) label : Parser<_> =
    fun stream ->
        printfn "%A: Entering %s" stream.Position label
        let reply = p stream
        printfn "%A: Leaving %s (%A)" stream.Position label reply.Status
        reply

let ws = spaces
let ws1 = spaces1
let str s = pstring s
let strWs s = str s .>> ws
let strWs1 s = str s .>> ws1

let inline readOrThrow (parser: Parser<'a>) input : 'a =
    match runParserOnString parser () "" input with
    | ParserResult.Success (result, state, pos) -> result
    | ParserResult.Failure (se, e, state) -> 
        failwith "Parser error" 
