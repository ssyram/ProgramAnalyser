module ProgramAnalyser.ParserSupport

open ProgramAnalyser.Global
open Objects
open Utils

type Statement =
    | STSkip
    | STBreak
    | STAssn of Variable * ArithExpr
    | STInLoopScore of ArithExpr
    | STIfBool of (BoolExpr * Statement list) list
    | STIfProb of p:ArithExpr * t:Statement list * f:Statement list
    
type DistType =
    | DContinuousUniform
    | DBeta
    | DNormal
    override x.ToString () =
        match x with
        | DContinuousUniform -> "CU"
        | DBeta -> "beta"
        | DNormal -> "normal"
    static member Parse (name : string) =
        match name with
        | "uniform" -> DContinuousUniform
        | "beta" -> DBeta
        | "normal" -> DNormal
        | _ -> failwith "Unknown Name."
    
type DistArg =
    | DANumber of Numeric 
    | DAExp of Numeric * int
    member x.ToNumeric =
        match x with
        | DANumber x -> x
        | DAExp (e, n) -> pown e n
    
type Distribution = Distribution of DistType * Numeric list

let mkDistribution name args =
    let distTy = DistType.Parse name in
    match distTy, args with
    | DNormal, [ x; y ] ->
        let y =
            match y with
            | DAExp (e, 2) -> e
            | DAExp (e, n) -> Numeric (System.Math.Pow (e.getDouble (), (float n / 2.)))
            | DANumber e -> Numeric (System.Math.Pow (e.getDouble (), (float 1 / 2.)))
        in
        Distribution (DNormal, [ x.ToNumeric; y ])
    | dist, [ x; y ] ->
        Distribution (dist, [ x.ToNumeric; y.ToNumeric ])
    | dist, _ ->
        failwith $"Invalid distribution args, distribution: {dist} expected 2 arguments."
    
let getDistDomainRange (Distribution (distType, args)) =
    match distType, args with
    | DContinuousUniform, [x; y] -> (x, y)
    | DBeta, [_; _] -> (NUMERIC_ZERO, NUMERIC_ONE)
    | _ -> failwith "Unsupported distribution to get domain range or invalid arguments."

type EndLoopScore =
    | ScoreDist of Distribution * ArithExpr
    | ScoreArith of ArithExpr

type ProgVarType = PVTInt | PVTReal

type RangeVal =
    | RValNumeric of Numeric
    | RValInf
    | RValNegInf

type Decl =
    | DeclProgVar of pvType:ProgVarType * name:string * rangeLow:RangeVal * rangeHigh:RangeVal * init:ArithExpr
    | DeclRandVar of name:string * dist:Distribution

type Program = {
    decls: Decl list
    invariant:BoolExpr
    loopGuard:BoolExpr
    loopBody:Statement list
    outLoopStatements: Statement list
}

let validateProgram program =
    // currently, the only check is that the outLoopStatments should not contain `break`
    let rec checkNoBreak (st : Statement) =
        match st with
        | STBreak -> false
        | STSkip -> true
        | STAssn (_, _) -> true
        | STInLoopScore _ -> true
        | STIfBool lst ->
            List.forall (fun (_, stLst) -> List.forall checkNoBreak stLst) lst
        | STIfProb (_, lT, lF) ->
            List.forall checkNoBreak lT && List.forall checkNoBreak lF
    in
    if not (List.forall checkNoBreak program.outLoopStatements) then
        failwith "The out loop statements should not contain `break`."
    else ()

let mkProgram 
        decls 
        invariant 
        loopGuard 
        loopBody 
        outLoopStatements : Program =
    let program =
        {   decls = decls
            invariant = invariant
            loopGuard = loopGuard
            loopBody = loopBody
            outLoopStatements = outLoopStatements }
    in
    validateProgram program;
    program

let mkPvDecl typStr name rangeLow rangeHigh initExpr =
    let pvType =
        match typStr with
        | "int" -> PVTInt
        | "real" -> PVTReal
        | _ -> failwith $"Unknown program variable type: {typStr}."
    in
    DeclProgVar (pvType, name, rangeLow, rangeHigh, initExpr)
let mkRvDecl randVarStr name dist =
    if randVarStr <> "random" then
        failwith $"Unknown random variable declaration: {randVarStr}."
    else
        DeclRandVar (name, dist)
let mkRangeInf str =
    if str = "inf" then RValInf
    else failwith $"Invalid range value: {str}, expected 'inf'."
let mkRangeNegInf str =
    if str = "inf" then RValNegInf
    else failwith $"Invalid range value: {str}, expected '-inf'."

let shapeOptionalIfScoreStatement bExpr sT sF =
    match sT, sF with
    | 1, 0 -> Some bExpr
    | _ -> failwith "Invalid format: the last `if` of score can only accept format score(1) and score(0)."

type RandomVarList = RandomVarList of (Variable * Distribution) list
    
let collectEndScoreLoopVars endScoreLoop =
    match endScoreLoop with
    | ScoreArith aExpr | ScoreDist (_, aExpr) -> collectVars aExpr

/// collect the variables that are read
let rec collectStatementUsedVars (st : Statement) =
    match st with
    | STAssn (var, expr) ->
        // remove the LHS from the RHS variables
        // read in updating itself is not counted as used
        Set.remove var $ collectVars expr
    | STSkip -> Set.empty
    | STBreak -> Set.empty
    | STIfBool lst ->
        let mapper (bExpr, stLst) =
            List.map collectStatementUsedVars stLst
            |> Set.unionMany
            |> Set.union (collectVars bExpr)
        in
        Set.unionMany $ List.map mapper lst
    | STInLoopScore a -> collectVars a
    | STIfProb (prob, stLst, stLst') ->
        List.append stLst stLst'
        |> List.map collectStatementUsedVars
        |> Set.unionMany
        |> Set.union (collectVars prob)

let collectDeclUsedVars (decl : Decl) =
    match decl with
    | DeclProgVar (_, _, _, _, initExpr) -> collectVars initExpr
    | DeclRandVar (_, dist) -> Set.empty

/// collect all the variables that are read in the program
let collectUsedVarsFromProgram (program : Program) =
    Set.unionMany [
//        Set.unionMany $ List.map collectStatementUsedVars program.assnLst
        Set.unionMany $ List.map collectVars [ program.invariant; program.loopGuard ]
        // Set.add program.retVar Set.empty
        Set.unionMany $ List.map collectStatementUsedVars program.loopBody;
        Set.unionMany $ List.map collectDeclUsedVars program.decls;
        Set.unionMany $ List.map collectStatementUsedVars program.outLoopStatements
    ]

/// remove the purely updated variables while not being read variables from a statement
/// that is, to remove all the update of the unused variables
let rec removeUnusedVarsFromStatement usedVars (st : Statement) =
    match st with
    | STAssn (var, _) -> if Set.contains var usedVars then Some st else None
    | STSkip | STInLoopScore _ | STBreak -> Some st
    | STIfBool lst ->
        List.map (BiMap.sndMap (removeUnusedVarsFromStatementList usedVars)) lst
        |> STIfBool
        |> Some
    | STIfProb (prob, lT, lF) ->
        Some $ STIfProb (prob,
                         removeUnusedVarsFromStatementList usedVars lT,
                         removeUnusedVarsFromStatementList usedVars lF)
/// remove the purely updated variables -- remove their update statements
and removeUnusedVarsFromStatementList usedVars stLst =
    List.concat $ List.map (removeUnusedVarsFromStatement usedVars >> Option.toList) stLst

let private collectNonInvariantVars program =
    Set.unionMany [
        Set.unionMany $ List.map collectVars [ program.loopGuard ]
        Set.unionMany $ List.map collectStatementUsedVars program.loopBody
        Set.unionMany $ List.map collectDeclUsedVars program.decls
        Set.unionMany $ List.map collectStatementUsedVars program.outLoopStatements
    ]
let rec private removeNonMentionedVars bExpr mentionVars =
    let recur bExpr = removeNonMentionedVars bExpr mentionVars in
    let allMentioned (a : ArithExpr) =
        collectVars a
        |> Set.toList
        |> List.forall (fun x -> Set.contains x mentionVars)
    in
    match bExpr with
    | BTrue | BFalse -> Some bExpr
    | BAnd (e1, e2) ->
        match recur e1, recur e2 with
        | None, e2 -> e2
        | e1, None -> e1
        | Some e1, Some e2 -> Some $ BAnd (e1, e2)
    | BCompare (_, a1, a2) ->
        if not (allMentioned a1 && allMentioned a2) then None
        else Some bExpr
let private programRemoveNoUseInvariantVars program =
    let nonInvVars = collectNonInvariantVars program in
    let preLoopGuardWithoutNonInvVars =
        Option.defaultValue BTrue $ removeNonMentionedVars program.invariant nonInvVars
    in
    { program
        with invariant = preLoopGuardWithoutNonInvVars }

/// remove the unused variables and its updates
/// including those only mentioned within pre-loop guard (invariant)
let simplifyProgram (program : Program) =
    let rec loopTilNoVarRemoved program =
        let usedVars = collectUsedVarsFromProgram program in
        let newLoopBody = removeUnusedVarsFromStatementList usedVars program.loopBody in
        let newEndLoopBody = removeUnusedVarsFromStatementList usedVars program.outLoopStatements in
        if newEndLoopBody = program.outLoopStatements &&
           newLoopBody = program.loopBody then program
        else loopTilNoVarRemoved {
                 program with
                    outLoopStatements = newEndLoopBody;
                    loopBody = newLoopBody
             }
    in
    loopTilNoVarRemoved program
    |> programRemoveNoUseInvariantVars

