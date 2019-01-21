module Infer

open Error
open Expr
open Util

let currentId = ref 0

let nextId () =
    let id = !currentId
    currentId := id + 1
    id

let resetId () = currentId := 0

let newVar level = TVar (ref (Unbound(nextId (), level)))
let newRowVar level constraints = TVar (ref (UnboundRow(nextId (), level, constraints)))
let newGenVar () = TVar (ref (Generic(nextId ())))
let newGenRowVar constraints = TVar (ref (GenericRow(nextId (), constraints)))

let occursCheckAdjustLevels tvarId tvarLevel ty =
    let rec f = function
        | TVar {contents = Link ty} -> f ty
        | TVar {contents = Generic _ } 
        | TVar {contents = GenericRow _ } -> 
            ()
            // why did this have to fail before introducing pattern matching?
            //failwithf "occursCheckAdjustLevels with Generic"
        | TVar ({contents = Unbound (otherId, otherLevel)} as otherTvar) ->
            if otherId = tvarId then
                raise (inferError RecursiveTypes)
            else
                if otherLevel > tvarLevel then
                    otherTvar := Unbound(otherId, tvarLevel)
                else
                    ()
        | TVar ({contents = UnboundRow (otherId, otherLevel, constraints)} as otherTvar) ->
            if otherId = tvarId then
                raise (inferError RecursiveTypes)
            else
                if otherLevel > tvarLevel then
                    otherTvar := UnboundRow(otherId, tvarLevel, constraints)
                else
                    ()
        | TApp (ty, tyArgList) ->
            f ty
            List.iter f tyArgList
        | TArrow (paramTy, returnTy) ->
            f paramTy
            f returnTy
        | TRecord row -> f row
        | TVariant row -> f row
        | TRowExtend (label, fieldTy, row) ->
            f fieldTy
            f row
        | TList ty -> f ty
        | TConst _ | TBool | TInt | TFloat | TString | TRowEmpty -> ()
    f ty

let injectConstraints isVariant constraints1 ty =
    let rec f isVariant ty =
        match ty with
        | TBool | TInt | TFloat | TString | TConst _ -> ()
        | TList ty -> f isVariant ty
        | TVar {contents = Link ty} -> f false ty
        | TArrow (a, b) -> 
            f false a
            f false b
        | TApp (x, xs) ->
            f false x
            List.iter (f false) xs
        | TVar {contents = Unbound _}
        | TVar {contents = Generic _} -> ()
        | TVar ({contents = UnboundRow (id, level, constraints2)} as tvar) ->
            let intersect = Set.intersect constraints1 constraints2
            if not isVariant && not (Set.isEmpty intersect) then
                let label = Set.minElement intersect
                raise (inferError (InferError.RowConstraintFail label))
            tvar := UnboundRow (id, level, Set.union constraints1 constraints2)
        | TVar ({contents = GenericRow (id, constraints2)} as tvar) ->
            let intersect = Set.intersect constraints1 constraints2
            if not isVariant && not (Set.isEmpty intersect) then
                let label = Set.minElement intersect
                raise (inferError (InferError.RowConstraintFail label))
            tvar := GenericRow (id, Set.union constraints1 constraints2)
        | TRecord ty -> f false ty
        | TVariant ty -> f true ty
        | TRowEmpty -> ()
        | TRowExtend (label, _, rest) ->
            if not isVariant && Set.contains label constraints1 then
                raise (inferError (InferError.RowConstraintFail label))
            f isVariant rest
            
    f isVariant ty

let rec unify ty1 ty2 =
    if ty1 = ty2 then () else
    let rec f isVariant ty1 ty2 =
        match ty1, ty2 with
        | TBool, TBool | TInt, TInt | TFloat, TFloat -> ()
        | TApp (ty1, tyArgList1), TApp (ty2, tyArgList2) ->
            f isVariant ty1 ty2
            List.iter2 (f isVariant) tyArgList1 tyArgList2
        | TArrow (paramTy1, returnTy1), TArrow (paramTy2, returnTy2) ->
            f isVariant paramTy1 paramTy2
            f isVariant returnTy1 returnTy2
        | TList ty1, TList ty2 -> f isVariant ty1 ty2
        | TVar {contents = Link ty1}, ty2
        | ty1, TVar {contents = Link ty2} -> f isVariant ty1 ty2
        | TVar {contents = Unbound(id1, _)}, TVar {contents = Unbound(id2, _)} 
        | TVar {contents = UnboundRow(id1, _, _)}, TVar {contents = UnboundRow(id2, _, _)} when id1 = id2 ->
            // There is only a single instance of a particular type variable
            failwithf "unify with the same type variable" 
        | TVar ({contents = UnboundRow(id, level, constraints)} as tvar), ty
        | ty, TVar ({contents = UnboundRow(id, level, constraints)} as tvar) ->
            injectConstraints isVariant constraints ty 
            occursCheckAdjustLevels id level ty
            tvar := Link ty

        | TVar ({contents = Unbound(id, level)} as tvar), ty
        | ty, TVar ({contents = Unbound(id, level)} as tvar) ->
            occursCheckAdjustLevels id level ty
            tvar := Link ty
        | TRecord row1, TRecord row2 -> f false row1 row2
        | TVariant row1, TVariant row2 -> f true row1 row2
        | TRowEmpty, TRowEmpty -> ()
        | TRowExtend (label1, fieldTy1, restRow1), (TRowExtend (_, _, restRow2) as row2) -> 
            let restRow1TVarRefOption =
                match restRow1 with
                | TVar ({contents = Unbound _} as tvarRef) -> Some tvarRef
                | _ -> None
            let restRow2 = rewriteRow row2 label1 fieldTy1
            match restRow1TVarRefOption with
            | Some {contents = Link _} -> raise (inferError RecursiveRowTypes)
            | _ -> ()
            f isVariant restRow1 restRow2
        | _, _ -> 
            raise (inferError (UnifyFail (ty1, ty2)))
    f false ty1 ty2

and rewriteRow (row2: Ty) label1 fieldTy1 =
    match row2 with
    | TRowEmpty -> raise (genericError (FieldNotFound label1))
    | TRowExtend (label2, fieldTy2, restRow2) when label2 = label1 ->
        unify fieldTy1 fieldTy2
        restRow2
    | TRowExtend (label2, fieldTy2, restRow2) ->
        TRowExtend (label2, fieldTy2, rewriteRow restRow2 label1 fieldTy1)
    | TVar {contents = Link row2 } -> rewriteRow row2 label1 fieldTy1
    | TVar ({contents = UnboundRow (id, level, constraints)} as tvar) ->
        let restRow2 = newRowVar level constraints
        let ty2 = TRowExtend (label1, fieldTy1, restRow2)
        tvar := Link ty2
        restRow2
    | TVar ({contents = Unbound (id, level)} as tvar) ->
        let restRow2 = newRowVar level Set.empty
        let ty2 = TRowExtend (label1, fieldTy1, restRow2)
        tvar := Link ty2
        restRow2
    | _ -> raise (inferError RowTypeExpected)

let rec generalizeTy level = function
    | TVar {contents = Unbound(id, otherLevel)} when otherLevel > level ->  
        TVar (ref (Generic id))
    | TVar {contents = UnboundRow(id, otherLevel, constraints)} when otherLevel > level ->  
        TVar (ref (GenericRow (id, constraints)))
    | TApp (ty, tyArgList) ->
        TApp (generalizeTy level ty, List.map (generalizeTy level) tyArgList)
    | TArrow (paramTy, returnTy) ->
        TArrow (generalizeTy level paramTy, generalizeTy level returnTy)
    | TVar {contents = Link ty} -> generalizeTy level ty
    | TRecord row -> TRecord (generalizeTy level row)
    | TVariant row -> TVariant (generalizeTy level row)
    | TRowExtend (label, fieldTy, row) ->
        TRowExtend (label, generalizeTy level fieldTy, generalizeTy level row)
    | TList ty -> TList (generalizeTy level ty)
    | TVar {contents = Generic _ }
    | TVar {contents = GenericRow _ }
    | TVar {contents = Unbound _ }
    | TVar {contents = UnboundRow _ }
    | TConst _ | TBool | TInt | TFloat | TString
    | TRowEmpty as ty -> ty

let generalize ty =
    generalizeTy (-1) ty

let instantiate level ty =
    let mutable idVarMap = Map.empty
    let rec f ty =
        match ty with
        | TConst _ | TBool | TInt | TFloat | TString -> ty
        | TList ty -> TList (f ty)
        | TVar {contents = Link ty} -> f ty
        | TVar {contents = Generic id} ->
            idVarMap
            |> Map.tryFind id
            |> Option.defaultWith (fun () ->
                let var = newVar level
                idVarMap <- Map.add id var idVarMap
                var
            )
        | TVar {contents = GenericRow (id, constraints)} ->
            idVarMap
            |> Map.tryFind id
            |> Option.defaultWith (fun () ->
                let var = newRowVar level constraints
                idVarMap <- Map.add id var idVarMap
                var
            )
        | TVar {contents = Unbound _} 
        | TVar {contents = UnboundRow _} -> ty
        | TApp (ty, tyArgList) ->
            TApp (f ty, List.map f tyArgList)
        | TArrow (paramTy, returnTy) ->
            TArrow (f paramTy, f returnTy)
        | TRecord row -> TRecord (f row)
        | TVariant row -> TVariant (f row)
        | TRowEmpty -> ty
        | TRowExtend (label, fieldTy, row) ->
            TRowExtend (label, f fieldTy, f row)
    f ty

let rec matchFunTy ty =
    match ty with
    | TArrow (paramTy, returnTy) -> paramTy, returnTy
    | TVar {contents = Link ty} -> matchFunTy ty
    | TVar ({contents = Unbound(id, level)} as tvar) ->
        let paramTy = newVar level
        let returnTy = newVar level
        tvar := Link (TArrow(paramTy, returnTy))
        paramTy, returnTy
    | TVar ({contents = UnboundRow(id, level, constraints)} as tvar) -> raise (inferError (FunctionExpected ty))
    | _ -> raise (inferError (FunctionExpected ty))

let rec inferExpr files env level = function
    | EError _ -> newVar level
    | EPrint e -> TRecord TRowEmpty
    | EType (e, t) ->
        let infered = inferExpr files env level e.Value
        unify infered t
        infered
    | EOpen filename -> Map.find filename files
    | EListEmpty -> TList (newVar level)
    | EListCons (x, xs) -> 
        let xTy = TList (inferExpr files env level x.Value)
        let xsTy = inferExpr files env level xs.Value
        unify xTy xsTy
        xTy
    | EFix name -> 
        let ty = 
            env
            |> Map.tryFind name 
            |> Option.defaultWith (fun () ->
                raise (genericError (VariableNotFound name))
            )
        let rec split ty =
            match ty with
            | TVar {contents = Link ty} -> split ty
            | TArrow (recur, rest) -> recur, rest
            | _ -> raise (genericError (InvalidFix name))
        let recur, rest = split ty
        rest
    | EBool _ -> TBool
    | EInt _ -> TInt
    | EFloat _ -> TFloat
    | EString _ -> TString
    | EVar name ->
        env
        |> Map.tryFind name
        |> Option.map (instantiate level)
        |> Option.defaultWith (fun () ->
            raise (genericError (VariableNotFound name))
        )
    | ELet (pattern, valueExpr, bodyExpr) ->
        let varTy = inferExpr files env (level + 1) valueExpr.Value
        let generalizedTy = generalizeTy level varTy
        let patternTy, bodyEnv = inferPattern files env level pattern
        unify patternTy generalizedTy
        inferExpr files bodyEnv level bodyExpr.Value
    | ECall (fnExpr, argExpr) ->
        let paramTy, returnTy =
            matchFunTy (inferExpr files env level fnExpr.Value)
        let argTy = inferExpr files env level argExpr.Value
        unify paramTy argTy
        returnTy
    | EIfThenElse (ifExpr, thenExpr, elseExpr) ->
        let a = inferExpr files env (level + 1) ifExpr.Value
        let b = inferExpr files env (level + 1) thenExpr.Value
        let c = inferExpr files env (level + 1) elseExpr.Value
        unify a TBool
        match a with
        | TBool | TVar {contents = Link TBool} -> ()
        | _ ->
            raise (genericError IfValueNotBoolean)
        unify b c
        c
    | EBinOp (a, op, b) ->
        let a = inferExpr files env (level + 1) a.Value
        let b = inferExpr files env (level + 1) b.Value
        unify a b
        match op with
        | Equal | NotEqual | Greater 
        | GreaterEqual | Lesser | LesserEqual -> TBool
        | _ -> b
    | EUnOp (op, a) ->
        let a = inferExpr files env (level + 1) a.Value
        match op with
        | Negative -> a
    | EFun (pattern, bodyExpr) ->
        let paramTy = newVar level
        let patternTy, fnEnv = inferPattern files env level pattern
        unify patternTy paramTy
        let returnTy = inferExpr files fnEnv level bodyExpr.Value
        TArrow (paramTy, returnTy)
    | ERecordEmpty -> TRecord TRowEmpty
    | ERecordSelect (recordExpr, label) ->
        let restRowTy = newRowVar level (Set.singleton label)
        let fieldTy = newVar level
        let paramTy = TRecord (TRowExtend(label, fieldTy, restRowTy))
        let returnTy = fieldTy
        unify paramTy (inferExpr files env level recordExpr.Value)
        returnTy
    | ERecordRestrict (recordExpr, label) ->
        let restRowTy = newRowVar level Set.empty // Used to be Set.singleton label
        let fieldTy = newVar level
        let paramTy = TRecord (TRowExtend(label, fieldTy, restRowTy))
        let returnTy = TRecord restRowTy
        unify paramTy (inferExpr files env level recordExpr.Value)
        returnTy
    | ERecordExtend (label, expr, recordExpr) ->
        let restRowTy = newRowVar level (Set.singleton label)
        let fieldTy = newVar level
        let param1Ty = fieldTy
        let param2Ty = TRecord restRowTy
        let returnTy = TRecord (TRowExtend (label, fieldTy, restRowTy))
        unify param1Ty (inferExpr files env level expr.Value)
        unify param2Ty (inferExpr files env level recordExpr.Value)
        returnTy
    | EVariant (label, expr) ->
        let restRowTy = newRowVar level (Set.singleton label)
        let variantTy = newVar level
        let paramTy = variantTy in
        let returnTy = TVariant (TRowExtend (label, variantTy, restRowTy))
        unify paramTy (inferExpr files env level expr.Value)
        returnTy
    | ECase (expr, cases, oDefault) ->
        match tryMakeVariantCases cases with
        | Some cases ->
            let defTy, returnTy =
                match oDefault with
                | None -> 
                    let returnTy = newVar level
                    TRowEmpty, returnTy
                | Some (name, defaultExpr) ->
                    let constraints =
                        cases
                        |> List.map (fun (name, _, _, _) -> name)
                        |> set
                    let defaultVariantTy = newRowVar level constraints
                    let valueTy = TVariant defaultVariantTy
                    let env = Map.add name valueTy env
                    let returnTy = inferExpr files env level defaultExpr.Value
                    defaultVariantTy, returnTy
            let exprTy = inferExpr files env level expr.Value
            let casesRow = inferVariantCases files env level returnTy defTy cases
            unify exprTy (TVariant casesRow)
            returnTy
        | None ->
            let exprTy = inferExpr files env level expr.Value
            let returnTy =
                match oDefault with
                | None -> newVar level
                | Some (name, defaultExpr) ->
                    let valueTy = newVar level
                    let env = Map.add name valueTy env
                    inferExpr files env level defaultExpr.Value
            let casesExprReturn =
                cases
                |> List.iter (fun (pattern, expr, oGuard) ->
                    let patternTy, env = inferPattern files env level pattern
                    oGuard
                    |> Option.iter (fun guard ->
                        let a = inferExpr files env level guard.Value
                        unify a TBool
                    )
                    unify patternTy exprTy
                    let localReturnTy = inferExpr files env level expr.Value
                    unify localReturnTy returnTy
                )
            returnTy

and inferVariantCases files env level returnTy restRowTy cases =
    match cases with
    | [] -> restRowTy
    | (label, pattern, expr, oGuard) :: otherCases ->
        let variantTy = newVar level
        let patternTy, caseEnv = inferPattern files env level pattern
        oGuard
        |> Option.iter (fun guard ->
            let a = inferExpr files caseEnv level guard.Value
            unify a TBool
        )
        unify patternTy variantTy
        unify returnTy (inferExpr files caseEnv level expr.Value)
        let otherCasesRow = inferVariantCases files env level returnTy restRowTy otherCases
        TRowExtend (label, variantTy, otherCasesRow)

and inferPattern files (env: Map<Name, Ty>) (level: int) pattern =
    let rec loop env pattern =
        match pattern with
        | EType (e, t) ->
            let infered, env = loop env e.Value
            unify infered t
            infered, env
        | EListEmpty -> TList (newVar level), env
        | EListCons (x, xs) -> 
            let singleTy, env = loop env x.Value
            let xTy = TList singleTy
            let multipleTy, env = loop env xs.Value
            let xsTy = multipleTy
            unify xTy xsTy
            xTy, env
        | EBool _ -> TBool, env
        | EInt _ -> TInt, env
        | EFloat _ -> TFloat, env
        | EString _ -> TString, env
        | EVar name ->
            let var = newVar level
            let env = Map.add name var env
            (var, env)
        | ERecordExtend (label, expr, rest) ->
            let fieldTy = newVar level
            let restRowTy = newRowVar level (Set.singleton label)
            let param1Ty = fieldTy
            let param2Ty = TRecord restRowTy
            let returnTy = TRecord (TRowExtend (label, fieldTy, restRowTy))
            let infer1Ty, env = inferPattern files env level expr
            unify param1Ty infer1Ty
            let env =
                match rest.Value with
                | ERecordEmpty -> env
                | _ ->
                    let infer2Ty, env = inferPattern files env level rest
                    unify param2Ty infer2Ty
                    env
            returnTy, env
        | ERecordEmpty -> 
            TRecord TRowEmpty, env
        | EVariant (label, expr) ->
            let restRowTy = newRowVar level (Set.singleton label)
            let variantTy = newVar level
            let paramTy = variantTy
            let returnTy = TVariant (TRowExtend (label, variantTy, restRowTy))
            let inferTy, env = inferPattern files env level expr
            unify paramTy inferTy
            (returnTy, env)
        | _ ->
            raise (genericError (InvalidPattern pattern))
    loop env pattern.Value

let infer files expr =
    inferExpr files Map.empty 0 expr
    |> generalize
