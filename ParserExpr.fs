module ParserExpr

open System 

open FParsec
open FParsec.CharParsers
open FParsec.Primitives

open Error
open Expr
open Infer
open ParserType
open ParserUtil
open Util 

let opp = new OperatorPrecedenceParser<Expr, unit, unit>()
let parseExpr = opp.ExpressionParser
let parseExprWs = parseExpr .>> ws

let patopp = new OperatorPrecedenceParser<Pattern, unit, unit>()
let parsePattern = patopp.ExpressionParser
let parsePatternWs = parsePattern .>> ws

let reserved = [ "let"; "in"; "fun"; "match"; "if"; "then"; "else"; "true"; "false"; "when"; "fix"; "rec"; "open"; "print"; "error" ]

let makeIdent first =
    first .>>. many (lower <|> pchar '_' <|> digit) |>> (List.Cons >> Array.ofList >> String)
    >>= (fun s ->
        if reserved |> List.exists ((=) s) then 
            fail "reserved"
        else
            preturn s
    )
    

let internalIdent: Parser<string> = makeIdent (pchar '_')

let externalIdent: Parser<string> = makeIdent lower

let ident = attempt internalIdent <|> externalIdent 
let identWs = ident .>> ws

let parseBool : Parser<Expr> =
    (stringReturn "true" (EBool true))
    <|> (stringReturn "false" (EBool false))

let parseInt : Parser<Expr> = 
    many1 digit |>> (Array.ofList >> String >> int >> EInt)

let parseFloat : Parser<Expr> = 
    let pa = many1 digit |>> (Array.ofList >> String)
    let pb = str "." >>. many digit |>> (Array.ofList >> String)
    pipe2 pa pb (fun whole decimal -> 
        whole + "." + decimal |> float
        |> EFloat
    )

let stringLiteral =
    let escape =  anyOf "\"\\/bfnrt"
                  |>> function
                      | 'b' -> "\b"
                      | 'f' -> "\u000C"
                      | 'n' -> "\n"
                      | 'r' -> "\r"
                      | 't' -> "\t"
                      | c   -> string c // every other char is mapped to itself

    let unicodeEscape =
        /// converts a hex char ([0-9a-fA-F]) to its integer number (0-15)
        let hex2int c = (int c &&& 15) + (int c >>> 6)*9

        str "u" >>. pipe4 hex hex hex hex (fun h3 h2 h1 h0 ->
            (hex2int h3)*4096 + (hex2int h2)*256 + (hex2int h1)*16 + hex2int h0
            |> char |> string
        )

    let escapedCharSnippet = str "\\" >>. (escape <|> unicodeEscape)
    let normalCharSnippet  = manySatisfy (fun c -> c <> '"' && c <> '\\')

    between (str "\"") (str "\"")
            (stringsSepBy normalCharSnippet escapedCharSnippet)

let parseString : Parser<Expr> = stringLiteral |>> EString
    
let parseFun : Parser<Expr> =
    let p1 = strWs1 "fun" >>. many1 parsePatternWs
    let p2 = strWs "->" >>. parseExprWs
    pipe2 p1 p2 (fun patterns body ->
        (patterns, body)
        ||> List.foldBack (fun pattern state ->
            EFun (pattern, state)
        )
    )

let parseVar = 
    identWs |>> EVar

let parseParen element = 
    between (strWs "(") (strWs ")") element

let parseLet = 
    let p1 = strWs1 "let" >>. many1 parsePatternWs
    let p2 = strWs "=" >>. parseExprWs
    let p3 = opt (strWs1 "in" >>. parseExprWs)
    pipe3 p1 p2 p3 (fun patterns value oBody -> 
        let pattern, value =
            match patterns with
            | [pattern] -> pattern, value
            | EVar name :: rest ->
                let wrappedValue =
                    (rest, value)
                    ||> List.foldBack (fun pattern state ->
                        EFun (pattern, state)
                    )
                EVar name, wrappedValue
            | _ -> raise (parserError InvalidFunctionDeclaration)
        let body =
            oBody
            |> Option.defaultWith (fun () ->
                match patterns with
                | [] -> raise (parserError InvalidFunctionDeclaration)
                | pattern :: _ -> pattern
            )
        ELet (pattern, value, body)
    )

let parseLetRec = 
    let p1 = strWs1 "let rec" >>. many1 parsePatternWs
    let p2 = strWs "=" >>. parseExprWs
    let p3 = opt (strWs1 "in" >>. parseExprWs)
    pipe3 p1 p2 p3 (fun patterns value oBody -> 
        let name, value =
            match patterns with
            | [pattern] -> raise (parserError InvalidLetRec)
            | EVar name :: rest ->
                let wrappedValue =
                    (rest, value)
                    ||> List.foldBack (fun pattern state ->
                        EFun (pattern, state)
                    )
                name, wrappedValue
            | _ -> raise (parserError InvalidFunctionDeclaration)
        let body =
            oBody
            |> Option.defaultWith (fun () ->
                match patterns with
                | [] -> raise (parserError InvalidFunctionDeclaration)
                | pattern :: _ -> pattern
            )
        ELet (EVar ("_" + name), EFun (EVar name, value), ELet (EVar name, EFix ("_" + name), body))
    )

let parseVariant =
    strWs ":" >>. identWs .>>. parseExprWs
    |>> EVariant

let parseMatchNormalCase : Parser<Pattern * Expr * Guard option> =
    let pa = parsePatternWs
    let pb = opt (strWs "when" >>. parseExprWs)
    let pc = strWs "->" >>. parseExprWs
    pipe3 pa pb pc (fun pattern guard expr -> (pattern, expr, guard))

let parseMatchDefaultCase : Parser<string * Expr> =
    let pa = identWs
    let pb = strWs "->" >>. parseExprWs
    pipe2 pa pb (fun var expr -> (var, expr))

let parseMatch =
    let p1 = strWs "match" >>. parseExprWs
    let p2 = strWs "{" >>. (sepBy parseMatchNormalCase (strWs ",")) 
    let p3 = opt (strWs "|" >>. parseMatchDefaultCase) .>> strWs "}"
    pipe3 p1 p2 p3 (fun expr normals oDefault -> 
        ECase(expr, normals, oDefault)
    )

let parseRecordEmpty : Parser<Expr> = 
    strWs "{" .>> strWs "}"
    |>> fun _ -> ERecordEmpty

let exprRecordExtend labelExprList record =
    (record, labelExprList)
    ||> List.fold (fun record (label, expr) -> ERecordExtend (label, expr, record))

let parseRecordLabel content : Parser<string * Expr> =
    attempt (identWs .>> strWs "=" .>>. content)
    <|> (identWs |>> (fun label -> label, EVar label))

type RecordAction =
    | Set 
    | Update 

let parseRecordLabelOrUpdate : Parser<string * Expr * RecordAction> =
    (attempt (identWs .>> strWs ":=" .>>. parseExprWs) |>> (fun (label, expr) -> label, expr, Update))
    <|> (parseRecordLabel parseExprWs |>> (fun (label, expr) -> label, expr, Set))

let parseRecordLabels content : Parser<(string * Expr) list> =
    sepBy1 (parseRecordLabel content) (strWs ",")

let parseRecordLabelsOrUpdate =
    sepBy1 (parseRecordLabelOrUpdate) (strWs ",")

let parseRecordExtendPattern =
    let p1 = strWs "{" >>. (parseRecordLabels parsePatternWs .>> ws)
    let p2 = strWs "|" >>. parseExprWs .>> strWs "}"
    pipe2 p1 p2 exprRecordExtend

let parseRecordExtendOrUpdate =
    let p1 = strWs "{" >>. (parseRecordLabelsOrUpdate .>> ws)
    let p2 = strWs "|" >>. parseExprWs .>> strWs "}"
    pipe2 p1 p2 (fun labelsOrUpdate record ->
        let labels =
            labelsOrUpdate
            |> List.map (fun (label, expr, _) -> label, expr)
        let toRemove =
            labelsOrUpdate
            |> List.choose (fun (label, _, action) ->
                match action with
                | Set -> None
                | Update -> Some label
            )
        let restrictedRecord =
            (record, toRemove)
            ||> List.fold (fun record label ->
                ERecordRestrict (record, label)
            )
        exprRecordExtend labels restrictedRecord
    )

let parseRecordInit content =
    strWs "{" >>. (parseRecordLabels content .>> ws) .>> strWs "}"
    |>> fun x -> exprRecordExtend x ERecordEmpty

let parseRecordSelect =
    parseExprWs .>>. (strWs "." >>. identWs)
    |>> ERecordSelect

let parseIfThenElse =
    let p1 = strWs1 "if" >>. parseExprWs
    let p2 = strWs1 "then" >>. parseExprWs
    let p3 = strWs1 "else" >>. parseExprWs
    pipe3 p1 p2 p3 (fun ifExpr thenExpr elseExpr -> EIfThenElse (ifExpr, thenExpr, elseExpr))

let parseFix =
    strWs1 "fix" >>. identWs |>> EFix

let parseListEmpty =
    strWs "[]" |>> fun _ -> EListEmpty

let parseListLiteral content = 
    strWs "[" >>. sepBy1 content (strWs ",") .>> strWs "]"
    |>> fun list ->
        (list, EListEmpty)
        ||> List.foldBack (fun x state ->
            EListCons (x, state)
        )

let parseType content =
    strWs "(" >>. content .>> strWs ":" .>>. parseTyWs .>> strWs ")"
    |>> EType

let parsePatternAll =
    choice [
        attempt (parseType parsePatternWs)
        attempt parseListEmpty
        parseListLiteral parsePatternWs
        parseParen parsePatternWs
        attempt parseBool
        attempt parseFloat
        attempt parseInt
        attempt parseString
        parseVariant
        attempt parseVar
        attempt parseRecordEmpty
        attempt parseRecordExtendPattern 
        attempt (parseRecordInit parsePatternWs)
    ]

patopp.AddOperator(InfixOperator("::", ws, 5, Associativity.Right, fun a b -> EListCons (a, b)))

patopp.TermParser <- parsePatternAll

let parseOpen =
    strWs "open" >>. stringLiteral
    |>> EOpen

let parsePrint =
    strWs "print" >>. parseExprWs
    |>> EPrint

let parseError =
    strWs "error" >>. stringLiteral
    |>> EError

let parseNotCallOrRecordSelect =
    choice [
        attempt (parseType parseExprWs)
        attempt parseOpen
        attempt parseListEmpty
        parseListLiteral parseExprWs
        parseParen parseExprWs
        attempt parseLetRec
        attempt parseFix
        parseBool
        attempt parseFloat
        attempt parseInt
        attempt parseString
        parseFun
        parseLet
        attempt parseVar
        attempt parseVariant
        parseMatch
        attempt parseRecordEmpty
        attempt parseRecordExtendOrUpdate 
        attempt (parseRecordInit parseExprWs)
        attempt parseIfThenElse
        attempt parsePrint
        attempt parseError
    ]

let parseExprOrCall =
    many1 (parseNotCallOrRecordSelect .>> ws)
    >>= fun result ->
        match result with
        | [one] -> preturn one
        | _ -> 
            let rec loop state exprs =
                match state, exprs with
                | None, fn :: arg :: exprs -> loop (Some (ECall (fn, arg))) exprs
                | None, _ -> raise (parserError FunctionCallNoArg)
                | Some fn, arg :: exprs -> loop (Some (ECall (fn, arg))) exprs
                | Some expr, [] -> expr
            let calls = loop None result
            preturn calls

opp.AddOperator(InfixOperator(".", ws, 9, Associativity.Left, fun a b -> 
    match b with 
    | EVar name -> ERecordSelect (a, name)
    | _ -> raise (parserError InvalidRecordSelect)
))
opp.AddOperator(InfixOperator("\\", ws, 8, Associativity.Left, fun a b -> 
    match b with 
    | EVar name -> ERecordRestrict (a, name)
    | _ -> raise (parserError InvalidRecordRestrict)
))

let notArrow : Parser<unit> = notFollowedBy (str ">") >>. ws

opp.AddOperator(PrefixOperator("-", notArrow, 8, true, fun a -> EUnOp (Negative, a)))

opp.AddOperator(InfixOperator("*", ws, 7, Associativity.Left, fun a b -> EBinOp (a, Multiply, b)))
opp.AddOperator(InfixOperator("/", ws, 7, Associativity.Left, fun a b -> EBinOp (a, Divide, b)))


opp.AddOperator(InfixOperator("+", ws, 6, Associativity.Left, fun a b -> EBinOp (a, Plus, b)))
opp.AddOperator(InfixOperator("-", notArrow, 6, Associativity.Left, fun a b -> EBinOp (a, Minus, b)))

opp.AddOperator(InfixOperator("::", ws, 5, Associativity.Right, fun a b -> EListCons (a, b)))
opp.AddOperator(InfixOperator("<", ws, 5, Associativity.Left, fun a b -> EBinOp (a, Lesser, b)))
opp.AddOperator(InfixOperator("<=", ws, 5, Associativity.Left, fun a b -> EBinOp (a, LesserEqual, b)))
opp.AddOperator(InfixOperator(">", ws, 5, Associativity.Left, fun a b -> EBinOp (a, Greater, b)))
opp.AddOperator(InfixOperator(">=", ws, 5, Associativity.Left, fun a b -> EBinOp (a, GreaterEqual, b)))

opp.AddOperator(InfixOperator("=", ws, 4, Associativity.Left, fun a b -> EBinOp (a, Equal, b)))
opp.AddOperator(InfixOperator("<>", ws, 4, Associativity.Left, fun a b -> EBinOp (a, NotEqual, b)))

opp.AddOperator(InfixOperator("&&", ws, 3, Associativity.Left, fun a b -> EBinOp (a, And, b)))

opp.AddOperator(InfixOperator("||", ws, 2, Associativity.Left, fun a b -> EBinOp (a, Or, b)))

opp.TermParser <- parseExprOrCall

let inline readExpr input = readOrThrow (parseExpr .>> eof) input
let inline readExprList input : Expr list =
    let parser = (sepEndBy parseExpr ws) .>> eof
    readOrThrow parser input
