module ProgramAnalyser.ParserSupport

open ProgramAnalyser.Global
open Objects
open Utils

(*
[
    p1: {
        G1: [
            p11: T1,
            1 - p11: T2,
        ]
        not G1: T3,
    },
    p2: {
        G2: T4,
        not G2: [
            p21: T5,
            1 - p21: T6,
        ]
    },
    1 - p1 - p2: {
        G3: T7,
        G3': T8,
        not G3 && not G3': [
            p31: T9,
            1- p32: {
                T10,
                T11,
            }
        ]
    },
]
*)

type Statement =
    | STSkip
    | STBreak
    | STAssn of Variable * ArithExpr
    | STInLoopScore of ArithExpr
    | STIfBool of BoolExpr * Statement list * Statement list
    | STIfProb of p:ArithExpr * t:Statement list * f:Statement list
    with
    interface IVariableCollectable with
        member this.CollectVars () =
            match this with
            | STAssn (var, expr) -> Set.add var $ collectVars expr
            | STSkip | STBreak -> Set.empty
            | STInLoopScore expr -> collectVars expr
            | STIfBool (b, t, f) ->
                Set.unionMany [
                    collectVars b;
                    Set.unionMany $ List.map collectVars t;
                    Set.unionMany $ List.map collectVars f
                ]
            | STIfProb (prob, lT, lF) ->
                Set.unionMany $ List.map collectVars (lT @ lF)
                |> Set.union (collectVars prob)
    
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
    with
    override x.ToString () =
        match x with
        | PVTInt -> "int"
        | PVTReal -> "real"

type IDeclVarCollectable =
    abstract member CollectDeclVars : unit -> Set<Variable>

/// collect the declared variables
let collectDeclVars (x : #IDeclVarCollectable) =
    x.CollectDeclVars ()

type Decl =
    | DeclProgVar of pvType:ProgVarType * name:string * rangeLow:RealInf * rangeHigh:RealInf * init:ArithExpr
    | DeclRandVar of name:string * dist:Distribution * rangeLow:RealInf * rangeHigh:RealInf
with
    interface IVariableCollectable with
        member this.CollectVars () =
            match this with
            | DeclProgVar (_, var, _, _, initExpr) ->
                Set.add (Variable var) $ collectVars initExpr
            | DeclRandVar _ -> Set.empty
    interface IDeclVarCollectable with
        member this.CollectDeclVars () =
            match this with
            | DeclProgVar (_, var, _, _, _) -> Set.singleton (Variable var)
            | DeclRandVar (var, _,_,_) -> Set.singleton (Variable var)

type Program = {
    decls: Decl list
    invariant:BoolExpr
    loopGuard:BoolExpr
    loopBody:Statement list
    outLoopStatements: Statement list
} with
    interface IVariableCollectable with
        member this.CollectVars () =
            Set.unionMany [
                collectVars this.invariant;
                collectVars this.loopGuard;
                Set.unionMany $ List.map collectVars this.loopBody;
                Set.unionMany $ List.map collectVars this.outLoopStatements;
                Set.unionMany $ List.map collectVars this.decls
            ]
    interface IDeclVarCollectable with
        member this.CollectDeclVars () =
            Set.unionMany $ List.map collectDeclVars this.decls

// ---------------------------------------- Program Validation ----------------------------------------

module private ProgramValidation = begin
    /// the outLoopStatments should not contain `break`
    let checkOutLoopNoBreak (program : Program) =
        let rec checkNoBreak (st : Statement) =
            match st with
            | STBreak -> false
            | STSkip -> true
            | STAssn (_, _) -> true
            | STInLoopScore _ -> true
            | STIfBool (_,lT, lF: Statement list) ->
                List.forall checkNoBreak lT && List.forall checkNoBreak lF
            | STIfProb (_, lT, lF: Statement list) ->
                List.forall checkNoBreak lT && List.forall checkNoBreak lF
        in
        if not (List.forall checkNoBreak program.outLoopStatements) then
            failwith "The out loop statements should not contain `break`."
        else program
    /// check if all the variables in the program are declared
    let checkVarsDeclared (program : Program) =
        let declaredVars = collectDeclVars program in
        let usedVars = collectVars program in
        let outstandingVars = Set.difference usedVars declaredVars in
        if not (Set.isEmpty outstandingVars) then
            failwith $"There are variables used in the program that are not declared: {Set.toList outstandingVars}."
        else program
    let checkVarNamesNoConflict (program : Program) =
        let mutable exploredVars = Set.empty in
        let errIfDuplicated (decl : Decl) =
            let vars = collectDeclVars decl in
            let conflictVars = Set.intersect exploredVars vars in
            if not (Set.isEmpty conflictVars) then
                failwith $"There variable {Set.toList conflictVars} is declared multiple times."
            else
                exploredVars <- Set.union exploredVars vars in
        List.iter errIfDuplicated program.decls;
        program
    /// check whether the variables declared are safe to be integers as declared
    let checkIntVars (program : Program) =
        let varTypes = 
            program.decls
            |> List.choose (function
                | DeclProgVar (pvType, name, _, _, _) -> Some (Variable name, pvType)
                | DeclRandVar (name,_,_,_) -> Some (Variable name, PVTReal)) // random variables are always real
            |> Map.ofList
        in
        let joinTyp (typ1 : ProgVarType) (typ2 : ProgVarType) =
            match typ1, typ2 with
            | PVTInt, PVTInt -> PVTInt
            | _ -> PVTReal in
        let rec arithExprTypes (expr : ArithExpr) =
            match expr with
            | AVar v -> Set.singleton v, Map.find v varTypes
            | AConst c -> Set.empty, if c.IsInt then PVTInt else PVTReal
            | AOperation (_, args) ->
                let folder (set, typ) (set', typ') = Set.union set set', joinTyp typ typ' in
                List.fold folder (Set.empty, PVTInt) (List.map arithExprTypes args) in
        let checkArithExpr (expr : ArithExpr) =
            let usedVars, typ = arithExprTypes expr in
            if typ = PVTInt then typ else
            // otherwise, the whole type is real, so all the variables should be real
            Set.toList usedVars
            |> List.iter (fun v ->
                if Map.find v varTypes = PVTInt then
                    failwith $"Variable {v} is wrongly declared as integer, as it is used in a real-value expression {expr}.");
            typ
        in
        let rec checkBoolExpr (bExpr : BoolExpr) =
            match bExpr with
            | BTrue | BFalse -> ()
            | BAnd (e1, e2) -> checkBoolExpr e1; checkBoolExpr e2
            | BCompare (_, a1, a2) -> ignore $ checkArithExpr a1; ignore $ checkArithExpr a2
        in
        let rec checkStmt (st : Statement) =
            match st with
            | STAssn (v, expr) ->
                let eTy = checkArithExpr expr in
                match Map.find v varTypes, eTy with
                | PVTInt, PVTInt | PVTReal, PVTReal | PVTReal, PVTInt -> ()
                | PVTInt, PVTReal ->
                    failwith $"Variable {v} is declared as integer, but assigned a real value expression {expr}."
            | STSkip | STBreak -> ()
            | STInLoopScore expr -> ignore $ checkArithExpr expr
            | STIfBool (b, t, f) ->
                checkBoolExpr b;
                List.iter checkStmt t;
                List.iter checkStmt f
            | STIfProb (prob, lT, lF) ->
                ignore $ checkArithExpr prob;
                List.iter checkStmt lT;
                List.iter checkStmt lF
        in
        let checkDecl (decl : Decl) =
            match decl with
            | DeclProgVar (_, name, _, _, initExpr) -> checkStmt (STAssn (Variable name, initExpr))
            | DeclRandVar _ -> () // random variables do not have type checking
        List.iter checkDecl program.decls;
        List.iter checkStmt program.loopBody;
        List.iter checkStmt program.outLoopStatements;
        List.iter checkBoolExpr [ program.invariant; program.loopGuard ];
        program
end

let private validateProgram program =
    program
    |> ProgramValidation.checkOutLoopNoBreak
    |> ProgramValidation.checkVarsDeclared
    |> ProgramValidation.checkVarNamesNoConflict
    |> ProgramValidation.checkIntVars
    |> ignore
    


// ---------------------------------------- Program Constructors ----------------------------------------

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
let mkRvDecl randVarStr name maybeRange dist =
    let lower, upper =
        match maybeRange with
        | None -> RINegInf, RIPosInf
        | Some (low, high) -> low, high
    in
    if randVarStr <> "random" then
        failwith $"Unknown random variable declaration: {randVarStr}."
    else
        DeclRandVar (name, dist, lower, upper)
let mkRangeInf str =
    if str = "inf" then RIPosInf
    else failwith $"Invalid range value: {str}, expected 'inf'."
let mkRangeNegInf str =
    if str = "inf" then RINegInf
    else failwith $"Invalid range value: -{str}, expected '-inf'."

let shapeOptionalIfScoreStatement bExpr sT sF =
    match sT, sF with
    | 1, 0 -> Some bExpr
    | _ -> failwith "Invalid format: the last `if` of score can only accept format score(1) and score(0)."

type RandomVarList = RandomVarList of (Variable * Distribution) list
    

/// collect the variables that are read
let rec collectStatementUsedVars (st : Statement) =
    let tripleCollect c l r =
        List.append l r
        |> List.map collectStatementUsedVars
        |> Set.unionMany
        |> Set.union (collectVars c)
    in
    match st with
    | STAssn (var, expr) ->
        // remove the LHS from the RHS variables
        // read in updating itself is not counted as used
        Set.remove var $ collectVars expr
    | STSkip -> Set.empty
    | STBreak -> Set.empty
    | STIfBool (b,t,f) -> tripleCollect b t f
    | STInLoopScore a -> collectVars a
    | STIfProb (prob, stLst, stLst') -> tripleCollect prob stLst stLst'

let collectDeclUsedVars (decl : Decl) =
    match decl with
    | DeclProgVar (_, _, _, _, initExpr) -> collectVars initExpr
    | DeclRandVar _ -> Set.empty

let programVarsOfProgram program =
    let mapper = function
    | DeclProgVar (pvType, name, lower, upper, _) ->
        Some (Variable name, (pvType, lower, upper))
    | DeclRandVar _ -> None
    in
    List.choose mapper program.decls
    |> Map.ofList
let randVarsOfProgram program =
    let mapper = function
    | DeclRandVar (name, dist, lower, upper) ->
        Some (Variable name, (dist, lower, upper))
    | DeclProgVar _ -> None
    in
    List.choose mapper program.decls
    |> Map.ofList

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
    | STIfBool (b,t,f) ->
        Some $ STIfBool (b,
                         removeUnusedVarsFromStatementList usedVars t,
                         removeUnusedVarsFromStatementList usedVars f)
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

