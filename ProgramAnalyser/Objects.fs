module ProgramAnalyser.Objects

open ProgramAnalyser
open ProgramAnalyser.Global
open Utils
open NormPolynomial

type Variable = Variable of string
    with
    override x.ToString () =
        match x with
        | Variable x -> x

type ArithOperator =
    | OpAdd
    | OpMul
    | OpMinus
    | OpDiv
    override x.ToString () =
        match x with
        | OpAdd -> "+"
        | OpMul -> "*"
        | OpMinus -> "-"
        | OpDiv -> "/"

type Comparator =
    | CmpLe
    | CmpGe
    | CmpLt
    | CmpGt
    | CmpEq
    | CmpNeq
    member x.Reverse =
        match x with
        | CmpLe -> CmpGe
        | CmpGe -> CmpLe
        | CmpLt -> CmpGt
        | CmpGt -> CmpLt
        | CmpEq -> CmpEq
        | CmpNeq -> CmpNeq
    member x.Negate =
        match x with
        | CmpLe -> CmpGt
        | CmpGe -> CmpLt
        | CmpLt -> CmpGe
        | CmpGt -> CmpLe
        | CmpEq -> CmpNeq
        | CmpNeq -> CmpEq
    override this.ToString() =
        match this with
        | CmpLe -> "<="
        | CmpGe -> ">="
        | CmpLt -> "<"
        | CmpGt -> ">"
        | CmpEq -> "="
        | CmpNeq -> "distinct"
    interface ILispPrintable with
        member op.LispPrint() =
            match op with
            | CmpLe -> "<="
            | CmpGe -> ">="
            | CmpLt -> "<"
            | CmpGt -> ">"
            | CmpEq -> "="
            | CmpNeq -> "distinct"

type IVarSubstitutable<'a, 'b> =
    abstract member SubstituteVar : Map<Variable, 'a> -> 'b
type IVariableCollectable =
    abstract member CollectVars : unit -> Set<Variable>

let substVars<'a, 'b when 'b :> IVarSubstitutable<'a, 'b>> (x : 'b) map : 'b = x.SubstituteVar map

let collectVars (x : #IVariableCollectable) = x.CollectVars ()

/// Specialness:
///     Op (-, [x]) => -x
///     Op (-, [x1; x2; ...; xn]) => x1 - x2 - ... - xn
type ArithExpr =
    | AVar of Variable
    | AConst of Numeric
    | AOperation of ArithOperator * ArithExpr list
    interface ILispPrintable with
        member this.LispPrint() =
            let rec lispPrintArithExpr aExpr =
                let printList op lst =
                    List.map lispPrintArithExpr lst
                    |> List.filter (fun (x : string) -> x.Length > 0)
                    |> function
                       | [] -> ""
                       | lst -> $"""({op} {String.concat " " lst})"""
                in
                match aExpr with
                | AVar var -> toString var
                | AConst num -> lispPrint num
                | AOperation (_, []) -> failwith "Invalid expression: Empty Operand."
                | AOperation (OpMinus, lst) -> printList "-" lst
                | AOperation (OpAdd, lst) -> printList "+" lst
                | AOperation (OpMul, lst) -> printList "*" lst
                | AOperation (OpDiv, lst) -> printList "/" lst
            in
            lispPrintArithExpr this
    member x.EraseMinus =
        match x with
        | AOperation (_, []) -> failwith "Invalid expression."
        // -x -> (-1)*x
        | AOperation (OpMinus, [x]) ->
            AOperation (OpMul, [AConst $ Numeric (-1); x])
        | AOperation (OpMinus, x :: ys) ->
            let ys = List.map (fun y -> AOperation (OpMul, [AConst $ Numeric (-1); y])) ys in
            AOperation (OpAdd, x :: ys)
        | AOperation (op, lst) -> AOperation (op, flip List.map lst $ fun x -> x.EraseMinus)
        | AVar _ | AConst _ -> x
    static member ToExprEnv (aExpr : ArithExpr) : ExprEnv<Variable> =
        match aExpr with
        | AVar var -> EEVar var
        | AConst num -> EEConst num
        | AOperation (OpAdd, lst) -> EEPlus $ List.map ArithExpr.ToExprEnv lst
        | AOperation (OpMul, lst) -> EEMul $ List.map ArithExpr.ToExprEnv lst
        | AOperation (OpMinus, _) -> toExprEnv aExpr.EraseMinus
        | AOperation (OpDiv, _)   -> failwith "Normalisation should not contain division."
    static member FromNormalisedExpr (NormalisedExpr map) : ArithExpr =
        let rec addCountUnit count unit lst =
            if count = 0u then lst else addCountUnit (count - 1u) unit (unit :: lst)
        in
        Map.toList map
        |> List.map (BiMap.fstMap $ Map.fold (fun lst var count -> addCountUnit count var lst) [])
        |> List.map (fun (vars, c) -> AOperation (OpMul, AConst c :: List.map AVar vars))
        |> function
           | [] -> AConst NUMERIC_ZERO
           | toSum -> AOperation (OpAdd, toSum)
    member x.SubsVar map =
        match x with
        | AVar var -> Option.defaultValue x $ Map.tryFind var map
        | AConst _ -> x
        | AOperation (op, lst) -> AOperation (op, flip List.map lst $ fun x -> x.SubsVar map)
    interface IVarSubstitutable<ArithExpr, ArithExpr> with
        member this.SubstituteVar map = this.SubsVar map
    interface IVariableCollectable with
        member this.CollectVars () =
            let rec collectArithExprVars (aExpr : ArithExpr) =
                match aExpr with
                | AConst _ -> Set.empty
                | AVar var -> Set.add var Set.empty
                | AOperation (_, lst) -> Set.unionMany $ List.map collectArithExprVars lst
            in
            collectArithExprVars this
    /// simplify the whole structure of the formula, may return None if the current expression
    /// is an operation on an empty list or is recursively dependent to such expressions 
    member x.Simplify () =
        match x with
        | AVar _ | AConst _ -> Some x
        | AOperation (_, []) -> None
        | AOperation (op, lst) ->
            flip List.map lst (fun x -> x.Simplify () |> Option.toList)
            |> List.concat
            |> function
               | [] -> None
               | lst -> Some $ AOperation (op, lst)
    override x.ToString () =
        let addMiddle str middle next =
            match (str, next) with
            | ("", next) -> next
            | (str, "") -> str
            | _ -> str + middle + next
        in
        match x with
        | AVar v -> toString v
        | AConst c ->
            if c < NUMERIC_ZERO then "(" + c.ToString "float" + ")"
            else c.ToString "float"
        // in some special cases, take only the internal stuff
        | AOperation (_, []) -> "()"
        | AOperation (OpMinus, [x]) ->
            match x with
            | AVar _ | AConst _ -> $"-{x}"
            | _ -> $"-({x})"
        | AOperation (_, [x]) -> $"(({toString x}))"
        | AOperation (OpAdd, lst) ->
            let printX x =
                match x with
                | AOperation (OpMinus, [_]) -> $"({x})"
                | _ -> toString x
            in
            // take out the head -- as if the head is negative, then, no need to add parenthesis
            let hd, tl = decomposeList lst in
            List.fold (fun str x -> addMiddle str "+" $ printX x) (toString hd) tl
        | AOperation (OpMul, lst) ->
            let printStuff x =
                match x with
                | AOperation (OpAdd, lst) | AOperation (OpMinus, lst) when lst.Length >= 2 -> $"({x})"
                | AOperation (OpMinus, [_]) -> $"({x})"
                | _ -> toString x
            in
            List.fold (fun str x -> addMiddle str "*" $ printStuff x) "" lst
        | AOperation (OpDiv, lst) ->
            let printStuff x =
                match x with
                | AOperation (_, lst) when lst.Length >= 2 -> $"({x})"
                | AOperation (OpMinus, [_]) -> $"({x})"
                | _ -> toString x
            in
            List.fold (fun str x -> addMiddle str "/" $ printStuff x) "" lst
        | AOperation (OpMinus, lst) ->
            let printY y =
                match y with
                | AOperation (OpAdd, lst) | AOperation (OpMinus, lst)
                    when lst.Length >= 2 -> $"({y})"
                | AOperation (OpMinus, [_]) -> $"({y})"
                | _ -> toString y
            in
            match lst with
            | x :: ys -> List.fold (fun x y -> addMiddle x "-" $ printY y) (toString x) ys
            | [] -> ""
    
type BoolExpr =
    | BTrue
    | BFalse
    | BAnd of BoolExpr * BoolExpr  // only `and` is supported
    | BCompare of Comparator * ArithExpr * ArithExpr
    interface IVariableCollectable with
        member this.CollectVars () =
            let rec collectBoolExprVars (bExpr : BoolExpr) =
                match bExpr with
                | BAnd (b1, b2) -> Set.union (collectBoolExprVars b1) (collectBoolExprVars b2)
                | BCompare (_, a1, a2) -> Set.union (collectVars a1) (collectVars a2)
                | BTrue -> Set.empty
                | BFalse -> Set.empty
            in
            collectBoolExprVars this
    member x.SubsVars map =
        match x with
        | BTrue -> BTrue
        | BFalse -> BFalse
        | BAnd (e1, e2) -> BAnd (e1.SubsVars map, e2.SubsVars map)
        | BCompare (cmp, a1, a2) -> BCompare (cmp, a1.SubsVar map, a2.SubsVar map)
    interface IVarSubstitutable<ArithExpr, BoolExpr> with
        member this.SubstituteVar map = this.SubsVars map
    override x.ToString () =
        match x with
        | BTrue -> "true"
        | BFalse -> "false"
        | BAnd (e1, e2) -> toString e1 + " && " + toString e2
        | BCompare (cmp, e1, e2) ->
            toString e1 + $" {cmp} " + toString e2
    
let substituteBoolVars (bExpr : BoolExpr) map =
    bExpr.SubsVars map
    
    

