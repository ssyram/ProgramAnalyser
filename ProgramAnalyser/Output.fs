module ProgramAnalyser.Output

open System
open System.Collections.Generic
open Global
open Microsoft.FSharp.Reflection
open ProgramAnalyser.Analysis
open ProgramAnalyser.Logic
open ProgramAnalyser.Objects
open ProgramAnalyser.ParserSupport
open ProgramAnalyser.Utils
open Polynomial

type ProgramTerminationType =
    | PTTTermination
    | PTTDirect
    | PTTConcentration
    override x.ToString () =
        FSharpValue.GetUnionFields(x, typeof<ProgramTerminationType>)
        |> function
           | (info, _) -> info.Name[3..].ToLower ()  // remove PTT and then print in the lower case
            
/// from the list, generate the output information
let fromListGenOutput lst =
    String.concat "\n" $ List.filter (fun x -> x.Length > 0) lst
    
let getBothVars program randVars =
    let oriRvMap = Map.ofSeq randVars in
    let folder (set, map) var =
        match Map.tryFind var oriRvMap with
        | Some dist -> (set, Map.add var dist map)
        | None      -> (Set.add var set, map)
    in
    collectUsedVarsFromProgram program
    |> Set.toList
    |> List.fold folder (Set.empty, Map.empty)

let rec private hasDiv aExpr =
    match aExpr with
    | AConst _ | AVar _ -> false
    | AOperation (OpDiv, _) -> true
    | AOperation (_, lst) -> List.exists hasDiv lst

type RealInf =
    | RINum of Numeric
    | RINegInf
    | RIPosInf
    override x.ToString () =
        match x with
        | RINum n -> n.ToString ()
        | RINegInf -> "-inf"
        | RIPosInf -> "inf"
    member x.ToString para =
        match x with
        | RINum n -> n.ToString para
        | _ -> x.ToString ()

let rec private simpArithExprForPrint arithExpr =
    if not $ hasDiv arithExpr then
        normaliseArithExpr arithExpr
    else
        match arithExpr with
        | AOperation (op, lst) -> AOperation (op, List.map simpArithExprForPrint lst)
        | _ -> IMPOSSIBLE ()

type ProgramAnalysisInput = {
    programName : string
    program : Program
    randomVars : (Variable * Distribution) list
    toTruncate : bool
    terminationType : ProgramTerminationType
    randVarRanges : Map<Variable, Numeric * Numeric>
    endLoopScoreAccuracy : string option
}

let getPreAssnProgVars program =
    let getVar = function | STAssn (v, _) -> v | _ -> IMPOSSIBLE () in
    program.assnLst
    |> List.map getVar

// do not warn the initial indentation issue within `Impl`
#nowarn "58"
module private Impl = begin

    /// <summary>
    /// Represents the possible types of programs.
    /// </summary>
    type ProgramType =
        | ScoreRecursive
        | NonScoreRecursive
        override x.ToString () =
            match x with
            | ScoreRecursive -> "score_recursive"
            | NonScoreRecursive -> "non_score_recursive"

    ///<summary>
    /// Represents information about an output program.
    ///</summary>
    type OutInfo = {
        programName : string
        programType : ProgramType
        programVars : Variable list
        randomVars : (Variable * Distribution) list
    }

    let BREAK_MARK = "$BREAK$"

    let (@) x y = x + "@" + y

    /// this is to output so GeConj is generated and should never be used for further computation
    type TruncationPathInfo =
        TruncationPathInfo of
            updates:(Variable * ArithExpr) list *
            // cond:GeConj *
            randVars:Variable list
        with
        member x.PrintWithGuard guard =
            match x with
            | TruncationPathInfo (updates, randVars) ->
                let mapper (var, expr) = $"{var}:={expr}" in
                [
                    String.concat "@" $ List.map mapper updates
                    match randVars with
                    | []  -> toString guard
                    | lst -> toString guard + " " @ String.concat " " (List.map toString lst)
                ]
                |> String.concat "\n"
        override x.ToString () = x.PrintWithGuard "GUARD"
                
    type AssignmentPath =
        /// if there is a `break` at last, the update is before the `break` statement
        /// if there is no `break` statement, the update is all the statements
        AssignmentPath of guard:BoolExpr * updates:(Variable * ArithExpr) list * toBreak:bool

    type StingItem =
        | SINormal of Location
        /// [(loc, [var])]
        | SIAbnormalSingleLoc of Location * Variable list
        | SIAbnormalMultiLocs of
        /// [(loc, [(var, (lower, upper))])]
            (Location * (Variable * ArithExpr * ArithExpr) list) list

    type Sting =
        Sting of
            // DEBUG: not to use GeConj, in order to reduce conversion loss
            guard:ConjCmps *
            pathInfo:StingItem list
        
    let geConjToGeConj (GeConj lst) = GeConj lst
        
    let concatGeConj (GeConj l1) (GeConj l2) = GeConj (l1 ++ l2)

    //let rec getAllProbExprFromCondPath (ConditionalPath (_, _, next)) =
    //    List.collect getAllProbExprFromProbPath next
    //and getAllProbExprFromProbPath (ProbPath (prob, _, next)) =
    //    prob :: List.collect getAllProbExprFromCondPath next
    //let getAllProbExprFromPathList pLst =
    //    match pLst with
    //    | PLCond conds -> List.collect getAllProbExprFromCondPath conds
    //    | PLProb probs -> List.collect getAllProbExprFromProbPath probs

    let rec getProbExprListFromSingleStmt st =
        match st with
        | STSkip | STAssn _ | STBreak | STInLoopScore _ -> []
        | STIfBool lst ->
            List.map snd lst
            |> List.collect getProbExprList
        | STIfProb (prob, stT, stF) ->
            prob ::
            AOperation (OpMinus, [AConst NUMERIC_ONE; prob]) ::
            getProbExprList stT ++
            getProbExprList stF
    and getProbExprList lst =
        List.collect getProbExprListFromSingleStmt lst

    let addNewPreLoopGuardConditions program =
        let getAdditionalRequirement aExpr =
            combineConst aExpr
            |> function
            | AConst _ -> None
            | aExpr -> Some (CmpGe, aExpr, AConst NUMERIC_ZERO)
        in
        let combineWithOriginal (ConjCmps lst') =
            boolExprToProposition program.invariant
            |> propToValidConjCmpList true
            |> function
            | [ (ConjCmps lst) ] -> ConjCmps $ lst ++ lst'
            | _ -> IMPOSSIBLE ()
        in
        let newInvariant =
            getProbExprList program.loopBody
            |> List.choose getAdditionalRequirement
            |> ConjCmps
            |> combineWithOriginal
            |> normaliseConjCmps
            |> collectTightRanges
            |> function
            | None -> BFalse
            | Some ranges ->
                genBoundsConjCompsFromItemBoundMap ranges
                |> List.map BCompare
                |> function
                | [] -> BTrue
                | lst -> List.reduce (curry BAnd) lst
        in
        // debugPrint $"New Invariant: \"{newPreLoopGuard}\",\nCompared to the old: \"{program.preLoopGuard}\"."
        { program with invariant = newInvariant }

    let toFullName partialName =
        match partialName with
        | "pd-beta-v1" -> "pedestrian-beta-v1"
        | "pd-beta-v2" -> "pedestrian-beta-v2"
        | "pd-beta-v3" -> "pedestrian-beta-v3"
        | "pd-beta-v4" -> "pedestrian-beta-v4"
        | "pdld"       -> "pedestrian-LD"
        | "pd"         -> "pedestrian"
        | "pdmb-v5"    -> "pedestrian-multiple-branches-v5"
        | "add-uni-Q1" -> "add-uniform-unbounded-Q1"
        | "add-uni-Q2" -> "add-uniform-unbounded-Q2"
        | "cav-ex-5-Q1" -> "cav-example-5-Q1"
        | "cav-ex-5-Q2" -> "cav-example-5-Q2"
        | "cav-ex-7-Q1" -> "cav-example-7-Q1"
        | "cav-ex-7-Q2" -> "cav-example-7-loop"
        | _otherwise   -> partialName
    
    let enumerateEdges analysisPaths =
        let initialEdges =
            List.concat $
            match analysisPaths with
            | PLCond condPaths -> List.map collectEdgeStmtFromCondPath condPaths
            | PLProb probPaths -> List.map collectEdgeStmtFromProbPath probPaths
        in
        let clearAfterBreak (Edge (guard, p, lst)) =
            let folder (toAcc, foundBreak) es =
                if foundBreak then (toAcc, true)
                else match es with
                     | ESBreak -> (ESBreak :: toAcc, true)
                     | _ -> (es :: toAcc, false)
            in
            // note that this fold is from left and the final result is reversed
            List.fold folder ([], false) lst
            |> fst
            |> List.rev  // reverse the folding result
            |> fun lst -> Edge (guard, p, lst)
        in
        List.map clearAfterBreak initialEdges
        
    let edgeToAssnPath (Edge (guard, _, lst)) =
        let folder (assnLst, toBreak as pair) es =
            if toBreak then pair
            else match es with
                 | ESAssign (var, expr) -> ((var, expr) :: assnLst, toBreak)
                 | ESScore  _           -> pair
                 | ESBreak              -> (assnLst, true)
        in
        List.fold folder ([], false) lst
        |> BiMap.fstMap List.rev
        |> fun (lst, toBreak) -> AssignmentPath (guard, lst, toBreak)
    
    let enumAllAssnPaths program =
        computePaths program.loopBody
        |> enumerateEdges
        |> List.map edgeToAssnPath
    
    
    
    
    
    
    
    
    
    
    
    
    
    /// to create a local context that captures the local information within a type
    type OutputAnalysis(input : ProgramAnalysisInput) =
        
        // extract the input and initialise the variables to be used below
        let programName = input.programName
        /// the simplified program
        /// use this rather than the above one
        let program = input.program
        /// the truly used program variables and random variables
        let _programVars, randomVars =
            let oriRvMap = Map.ofSeq input.randomVars in
            let folder (set, map) var =
                match Map.tryFind var oriRvMap with
                | Some dist -> (set, Map.add var dist map)
                | None      -> (Set.add var set, map)
            in
            collectUsedVarsFromProgram program
            |> Set.toList
            |> List.fold folder (Set.empty, Map.empty)
        let randomVarsSet = Set.ofSeq $ Map.keys randomVars
        /// the filtered random variables -- only those used in the loop body
        let randVarRanges =
            Map.filter (fun var _ -> randomVarsSet.Contains var) input.randVarRanges
        let toTruncate = input.toTruncate
        let terminationType = input.terminationType
        let endLoopScoreAccuracy = input.endLoopScoreAccuracy
        let analysisPaths = computePaths program.loopBody
        // DEBUG: add this part to automatically generate other implicit conditions
        let program = addNewPreLoopGuardConditions program
        
        
        
        let rec hasScoreList stLst =
            List.exists hasScore stLst
        and hasScore st =
            match st with
            | STInLoopScore aExpr ->
                match NormPolynomial.normalise aExpr with
                | AConst c when c = NUMERIC_ONE -> false
                | _ -> true
            | STSkip | STAssn _ | STBreak -> false
            | STIfBool lst -> List.exists (snd >> hasScoreList) lst
            | STIfProb (_, stT, stF) -> hasScoreList stT || hasScoreList stF
        
        let program_name = toFullName programName
        let program_type =
            toString $
            if hasScoreList program.loopBody then ScoreRecursive
            else NonScoreRecursive
            
        let loopInvariant = boolExprToProposition program.invariant
        
        // let loopInv =
        //     match propToValidGeConj LossConfirm loopInvariant with
        //     | [ x ] -> x
        //     | _     -> IMPOSSIBLE ()
            
        let list_of_pre_assn_program_vars =
            getPreAssnProgVars program
            // Set.toSeq programVars
            |> Seq.map toString
            |> String.concat " "
            
        let number_of_random_variables = toString $ Map.count randomVars
        
        let printDistDecl (Distribution (distTy, arg)) =
            let arg = flip List.map arg $ fun x -> x.ToString "float" in
            match distTy, arg with
            | DContinuousUniform, [x; y] -> $"CU@{x} {y}"
            | DBeta, [x; y] -> $"beta#{x} {y}@0 1"
            | _ -> failwith "Unknown way to declare distribution."
        
        let random_variable_type_declarations () =
            Map.toSeq randomVars
            |> Seq.map (fun (var, dist) -> $"{var}" @ printDistDecl dist)
            |> String.concat "\n"
            
        let sting = "sting"
        
        let truncation_or_not =
            if toTruncate then "truncation"
            else "non-truncation"
        
        /// the loop guard is just the loop guard -- the invariant is taken out
        let loopGuard = boolExprToProposition program.loopGuard
        
        let propToSingleConjCmpList prop =
            let lst = decomposePropToValidExclusiveConjCmps prop in
            match lst with
            | [] -> ConjCmps []
            | [ x ] -> x
            | _ -> failwith "Expected Only ONE ConjCmpList."
        
    //    let loopConjCmpList = propToSingleConjCmpList loopGuard
    //    
    //    let loopGeConj = simplifyGeConj $ conjCmpsToGeConj LossConfirm loopConjCmpList
        
        let loopAndInvConjCmpList = propToSingleConjCmpList $ And [ loopGuard; loopInvariant ]
        
        // let loopAndInvGeConj = simplifyGeConj $ conjCmpsToGeConj LossConfirm loopAndInvConjCmpList
        
        let termination_type = toString terminationType
        
        let truncation_sting_guard =
            // confirmed by Peixin, not to add LoopInvariant here.
            // And [ loopGuard; loopInvariant ]
            loopGuard
            |> propToSingleConjCmpList
            |> conjCmpsToGeConj LossConfirm
            |> simplifyGeConj
            |> toString
        
        /// Collects all updates pairs in a given list of statements
        let collectUpdates lst =
            flip List.choose lst $ function
                | ESAssign (var, toUpdate) -> Some (var, toUpdate)
                | ESScore _ | ESBreak      -> None
        
        let rec allBranchesCond (ConditionalPath (_, sts, next)) =
            let sts = collectUpdates sts in
            match next with
            | [] -> [ sts ]
            | _  ->
                List.collect allBranchesProb next
                |> List.map (List.append sts)
        and allBranchesProb (ProbPath (_, sts, next)) =
            let sts = collectUpdates sts in
            match next with
            | [] -> [ sts ]
            | _  ->
                List.collect allBranchesCond next
                |> List.map (List.append sts)
        
        let allUpdateBranches pathList =
            match pathList with
            | PLCond lst -> List.collect allBranchesCond lst
            | PLProb lst -> List.collect allBranchesProb lst
        
        /// number_of_paths
        /// {
        ///     update_paths
        ///     condition ` @` involved_random_vars
        /// }+
        ///
        /// condition is given by `LoopGuard & InvGuard & PathGuard`
        /// Hence for probability paths, just `LoopGuard & InvGuard` without PathGuard
        let truncation_paths_information () =
            let generatePathsInfo () =
                let getInvolvedRandVarsFromUpdates updates =
                    List.map snd updates
                    |> List.map collectVars
                    |> Set.unionMany
                    |> Set.intersect randomVarsSet
                in
                let truncInfo : TruncationPathInfo list =
                    let mapper updates =
                        TruncationPathInfo (
                            updates,
                            Set.toList $ getInvolvedRandVarsFromUpdates updates)
                    in
                    allUpdateBranches analysisPaths
                    |> List.map mapper
                in
                let number_of_paths = toString $ List.length truncInfo in
                let printTrunc (trunc : TruncationPathInfo) =
                    propToValidGeConj LossConfirm loopGuard
                    |> function
                    | [ x ] -> trunc.PrintWithGuard $ simplifyGeConj x
                    | _     -> IMPOSSIBLE ()
                in
                let truncate_paths_info () = fromListGenOutput $ List.map printTrunc truncInfo in
                [
                    number_of_paths
                    truncate_paths_info ()
                    sting
                    truncation_sting_guard
                ]
                |> fromListGenOutput
            in
            generatePathsInfo ()
        
        /// an edge either ends with a `break` or does not contain any `break` statement
        let enumeratedEdges = enumerateEdges analysisPaths
            
        let enumeratedAssnPaths =
            List.map edgeToAssnPath enumeratedEdges
        
        /// Required Assumption: Only ONE end loop score variable
        let endLoopScoreVariable =
            match program.mayEndScore with
            | None | Some (ScoreArith _) -> None
            | Some (ScoreDist (_, expr)) ->
                match Set.toList $ collectVars expr with
                | [ x ] -> Some x
                | _ -> failwith "Related update variable should be exactly 1."
        let mutable hasFinalUpdate = Option.isSome endLoopScoreVariable
        let mutable isDependent = false
        
        /// TODO: Resolve Assumption:
        ///     there is only one out way path
        let mutable outPathIdx = -1
        
        let end_score_information () =
            match program.mayEndScore with
            | None -> "non-endscoring"
            | Some endLoopScore ->
                let type_of_end_score_parameter =
                    match endLoopScore with
                    | ScoreArith _ -> "polynomial"
                    | ScoreDist  _ -> "non-polynomial"
                in
                let body_of_score_parameter =
                    match endLoopScore with
                    | ScoreArith aExpr -> toString aExpr
                    | ScoreDist (dist, arithExpr) ->
                        match dist with
                        | Distribution (DBeta, [x; y]) -> $"beta@{x} {y}@{arithExpr}"
                        | Distribution (DNormal, [x; y]) ->
                            if Option.isNone endLoopScoreAccuracy then
                                failwith "When scoring `normal` distribution, accuracy should be given.";
                            let ret =
                                let x, y = x.ToString "float", y.ToString "float" in
                                $"normal@{x} {y}@{arithExpr}" + "@acc=" + endLoopScoreAccuracy.Value
                            in
                            match program.mayIfScoreCond, endLoopScoreVariable with
                            | None, _ | _, None -> ret
                            | Some cond, Some var ->
                                // should see if this condition is *about the variable in `expr`*
                                // if it is, then, using the preLoopGuard to judge whether this holds
                                let wholeCond =
                                    And $ [
                                        boolExprToProposition cond
                                        boolExprToProposition program.invariant
                                    ]
                                in
                                let range =
                                    propToSingleConjCmpList wholeCond
                                    |> collectTightRanges
                                    |> function
                                    | None ->
                                        let msg =
                                            "The required condition is never satisfiable."
                                        in
                                        failwith $"{msg}"
                                    | Some hashMap ->
                                        HashMap.tryFind (AVar var) hashMap
                                in
                                match range with
                                | Some
                                    (Range
                                        (LowerBound (BVFinite (l, _)),
                                         UpperBound (BVFinite (u, _)))) ->
                                    let l, u = l.ToString "float", u.ToString "float" in
                                    ret @ $"min={l} max={u}"
                                | _ -> ret
                        | _ ->
                            failwith "Unknown distribution or invalid distribution parameters."
                in
                let final_update_information =
                    match endLoopScore with
                    | ScoreArith _ -> ""
                    | ScoreDist  _ ->
                        /// the involved target variable
                        let targetVar = endLoopScoreVariable.Value in
                        // the update formula of the exit variable
                        let targetFormula =
                            let toPick (idx, AssignmentPath (pathGuard, lst, toBreak)) =
                                let tryFindExpr lst =
                                    // during the find, should also log the out-way path index
                                    outPathIdx <- idx;
                                    let toPick (var, expr) =
                                        if var = targetVar then Some expr
                                        else None
                                    in
                                    List.tryPick toPick lst
                                in
                                if toBreak then Some $ tryFindExpr lst else
                                // check SAT of g_l /\ wp(~g_l)
                                /// wp(~g_l)
                                let execLoopGuard = assnPathWp lst $ Not loopGuard in
                                let queryCtx = mkQueryCtx () in
                                let randVarRanges =
                                    Map.map (fun _ (a, b) -> (AConst a, AConst b)) randVarRanges
                                in
                                let queryCtx = { queryCtx with varRange = randVarRanges } in
                                // find out the one that is going to exit --
                                // based on the assumption, there is ONLY ONE way out
                                if checkSAT queryCtx [
                                    loopGuard
                                    loopInvariant
                                    execLoopGuard
                                    boolExprToProposition pathGuard
                                ] then
                                    Some $ tryFindExpr lst
                                else None
                            in
                            match List.tryPick toPick $ List.indexed enumeratedAssnPaths with
                            | None ->
                                // This means there is no break or possible path to get out
                                failwith "Infinite Looping"
                            | Some x ->
                                // This value may be `None` (Some None), which means no update during out
                                x
                        in
                        let noFinalUpdate () =
                            hasFinalUpdate <- false;
                            toString targetVar
                        in
                        match targetFormula with
                        | None -> noFinalUpdate ()
                        | Some formula ->
                            let involvedRandomVars =
                                collectVars formula
                                |> Set.intersect randomVarsSet
                            in
                            if Set.isEmpty involvedRandomVars then noFinalUpdate ()
                            else let varsStr =
                                     Set.toSeq involvedRandomVars
                                     |> Seq.map toString
                                     |> String.concat " "
                                 in
                                 isDependent <- true;
                                 $"{formula}@{varsStr}@dependent"
                in
                [
                    "endscoring"
                    "1@-1"
                    type_of_end_score_parameter
                    body_of_score_parameter
                    final_update_information
                ]
                |> fromListGenOutput
        
        /// `normal`
        /// |
        /// `abnormal`
        /// number_of_vars
        /// {random_var_decl}*
        let outputStingItem item =
            match item with
            | SINormal _ -> "normal"
            | SIAbnormalSingleLoc (LZero, _) -> "normal"  // for `0` location, just print normal
            | SIAbnormalSingleLoc (_, vars) ->
                if vars = [] then failwith "This should be of type `Normal`."
                let number_of_vars = toString $ List.length vars in
                let rand_vars_decl () =
                    List.map (fun var -> toString var @ "expectation") vars
                    |> String.concat "\n"
                in
                [
                    "abnormal"
                    number_of_vars
                    rand_vars_decl ()
                ]
                |> fromListGenOutput
            | SIAbnormalMultiLocs lst ->
                let declareRandVars (loc, vars) =
                    let number_of_vars = toString $ List.length vars in
                    let printVarWithMaybeBounds (var, lower, upper) =
                        let lower = simpArithExprForPrint lower in
                        let upper = simpArithExprForPrint upper in
                        let boundStr =
                            match (lower, upper) with
                            | (AConst lower, AConst upper) when
                                Some (lower, upper) = Map.tryFind var randVarRanges -> ""
                            | _ -> $"@{lower} {upper}"
                        in
                        $"{var}@expectation" + boundStr +
                        if isDependent && loc = LNegOne then
                            Set.union (collectVars lower) (collectVars upper)
                            |> Set.toList
                            |> List.map toString
                            |> String.concat " "
                            |> fun x ->
                                if x = "" then failwith "Dependent while unrelated to random variables";
                                $"@{x}"
                        else ""
                    in
                    let rand_vars_decl () =
                        List.map printVarWithMaybeBounds vars
                        |> fromListGenOutput
                    in
                    [
                        "abnormal"
                        number_of_vars
                        rand_vars_decl ()
                    ]
                    |> fromListGenOutput
                in
                List.map declareRandVars lst
                |> fromListGenOutput
        
        let getInvolvedRandomVarsFromAssnLst (seq : seq<Variable * ArithExpr>) =
            Seq.map (snd >> collectVars) seq
            |> Set.unionMany
            |> Set.intersect randomVarsSet
            |> Set.toList
        
        let outputSting (Sting (guard, nextLocs)) =
            let sting_guard =
                conjCmpsToGeConj LossConfirm guard
                // |> concatGeConj loopInv
                |> simplifyGeConj
                |> toString
            in
            let next_loc_declarations =
                let getLocations =
                    function
                    | SINormal   loc -> toString loc
                    | SIAbnormalSingleLoc (loc, _) -> toString loc
                    | SIAbnormalMultiLocs lst -> List.map (fst >> toString) lst |> String.concat " "
                in
                let locs = 
                    List.map getLocations nextLocs
                    |> String.concat "#"
                in
                "next_locs=" + locs
            in
            let corresponding_every_loc_information () =
                List.map outputStingItem nextLocs
                |> fromListGenOutput
            in
            [
                "sting"
                sting_guard
                next_loc_declarations
                corresponding_every_loc_information ()
            ]
            |> List.filter (fun x -> x.Length > 0)
            |> String.concat "\n"
        
        let formNoVarRangeStingItem preInfo nextLoc =
            match preInfo with
            | [] -> SINormal nextLoc
            | varsInfo -> SIAbnormalSingleLoc (nextLoc, varsInfo)
        
        let concatConjCmpList (ConjCmps l1) (ConjCmps l2) = ConjCmps $ l1 ++ l2
        
        /// in this case, one will need to consider computing the actual range of the score variable
        /// and the division for these paths are:
        /// - `-1` {#1}* for the central range to divide
        /// - `0` {#1}* for other ranges
        /// TODO: Resolve Assumption:
        ///     only one central probability path to get out
        /// AND must get out -- there is no range of the random variable to change
        /// AND no modification to the score variable in the central path, no matter via random variable or not
        /// AND the computed range is compatible with the conditions -- there is no additional check for SAT
        /// With the assumption:
        ///     The central path is fixed to be `outPathIdx`.
        let stingsOfParaEstimatePatternProbPaths () =
            // find the central range
            // divide the range to be several parts -- [(isCentral, rangeProp)]
            // rangeProp should be compatible with the loop guard
            // for those (true, prop), generate the sting item:
            // sting
            // range_prop
            // next_locs={1#}* `-1` {#1}*
            //            ...  tIdx  ...
            // path_info: normal or not -- which is fixed for each edge
            // for those (false, prop), generate the sting item:
            // sting
            // range_prop
            // next_locs={1#}* `0` {#1}*
            // path_info: normal or not -- which is fixed for each edge (except the target information)
            let centralIdx = outPathIdx in
            /// the sting items regardless of the central prop
            let pathInfoNegOne, pathInfoZero =
                let mapper (idx, (AssignmentPath (_,updates, _))) =
                    let preStingInfo = getInvolvedRandomVarsFromAssnLst updates in
                    if idx = centralIdx then
                        (formNoVarRangeStingItem preStingInfo LNegOne,
                         formNoVarRangeStingItem preStingInfo LZero)
                    else
                        (formNoVarRangeStingItem preStingInfo LOne,
                         formNoVarRangeStingItem preStingInfo LOne)
                in
                List.indexed enumeratedAssnPaths
                |> List.map mapper
                |> List.unzip
            in
            let scoreVar = endLoopScoreVariable.Value in
            /// [(isCentral, prop)]
            let centralPropInfo : (bool * ConjCmps) list =
                let endScoreDist =
                    match program.mayEndScore.Value with
                    | ScoreDist (dist, _) -> dist
                    | _ -> IMPOSSIBLE ()
                in
                let accuracy = Double.Parse endLoopScoreAccuracy.Value in
                match endScoreDist with
                | Distribution (DNormal, [x; y]) ->
                    let lower, upper = findNormalPdfIntRange (x.getDouble ()) (y.getDouble ()) accuracy in
                    [
                        (true, ConjCmps [
                            (CmpLe, AVar scoreVar, AConst $ Numeric upper)
                            (CmpGe, AVar scoreVar, AConst $ Numeric lower)
                        ])
                        (false, ConjCmps [ (CmpGt, AVar scoreVar, AConst $ Numeric upper) ])
                        (false, ConjCmps [ (CmpLt, AVar scoreVar, AConst $ Numeric lower) ])
                    ]
                | _ -> failwith "Unsupported distribution or invalid arguments."
            in
            let centralPropInfo =
                flip List.map centralPropInfo $
                    fun (isCentral, prop) ->
                        (isCentral, concatConjCmpList prop loopAndInvConjCmpList)
            in
            let genSting (isCentral, prop) =
                Sting (prop, if isCentral then pathInfoNegOne else pathInfoZero)
            in
            List.map genSting centralPropInfo
        
        let assnLstToNoVarRangeSting assnLst loc =
            formNoVarRangeStingItem (getInvolvedRandomVarsFromAssnLst assnLst) loc
        
        let enumNonBreakPathInfo singleAssnPath additionalFixedGuard =
            let mapper =
                function
                | NLSingle (loc, guard) -> (guard, assnLstToNoVarRangeSting singleAssnPath loc)
                | NLJoin (guard, concreteRange) -> (guard, SIAbnormalMultiLocs concreteRange)
            in
            let fixedGuard =
                match additionalFixedGuard with
                | Some fg -> And [ fg; loopInvariant ]
                | None -> loopInvariant
            in
            // TODO: Resolve Assumption:
            //      Always take the shortcut
            //      Generally, should check whether it is pure addition
            List.map mapper $ pathDivisionAnalysis {
                path = singleAssnPath
                fixedGuard = fixedGuard
                loopGuard = loopGuard
                mayEndIfScoreGuard = Option.map boolExprToProposition program.mayIfScoreCond
                randVarRanges = randVarRanges
                takeZeroShortcut = true }
        
        let enumPossiblePathInfo
                fixGuard
                (AssignmentPath (_,updates, toBreak)) : (ConjCmps * StingItem) list =
            if toBreak then
                match program.mayIfScoreCond with
                | Some ifGuard ->
                    // judge 0/-10 or 0/-1
                    /// the out location -- -1 or -10
                    let outLoc = match program.mayEndScore with
                                 | Some _ -> LNegOne
                                 | None -> LNegTen in
                    // TODO: Resolve Assumption:
                    //      No modification or will not affect the IfScore guard during this path
                    // SO here does not judge whether after the execution, the condition will hold or not
                    let ifGuard = boolExprToProposition ifGuard in
                    // in the following two sets of guards, one should just use `loopGuard` as part of condition
                    // this is because no other path condition is given
                    // to the ZERO location
                    let zeroGuards = propToValidConjCmpList true $ And [ Not ifGuard; loopGuard ] in
                    // to the IF location -- `outLoc` -- the NON-ZERO out location
                    let outGuard = propToValidConjCmpList true $ And [ ifGuard; loopGuard ] in
                    let involvedRandVars = getInvolvedRandomVarsFromAssnLst updates in
                    let outItems =
                        formNoVarRangeStingItem involvedRandVars outLoc
                        |> fun item -> List.map (fun outGuard -> (outGuard, item)) outGuard
                    in
                    let zeroItems =
                        formNoVarRangeStingItem involvedRandVars LZero
                        |> fun item -> List.map (fun zeroGuard -> (zeroGuard, item)) zeroGuards
                    in
                    outItems ++ zeroItems
                | None ->
                    // must go to `-1`
                    [ (loopAndInvConjCmpList, assnLstToNoVarRangeSting updates LNegOne) ]
            else
                enumNonBreakPathInfo updates fixGuard
        
        let combineInfoLstOfPaths pathInfoLst =
            let rec combineInfoLstOfPaths accGuard accItems rest =
                match rest with
                | lst :: rest ->
                    List.concat $ flip List.map lst (fun (guard, item) ->
                        combineInfoLstOfPaths (concatConjCmpList accGuard guard) (item :: accItems) rest)
                | [] ->
                    [
                        if checkConjCmpListSAT accGuard then
                            // the path info is from right to left, hence should be reversed
                            let pathInfo = List.rev accItems in
                            Sting (accGuard, pathInfo)
                    ]
            in
            combineInfoLstOfPaths (ConjCmps []) [] pathInfoLst
        
        /// in this case, one will need to use the IfEndScore range as the `0` for all paths:
        /// So, we will need two analysis -- when `-1` and when `0`
        /// When `-1`, it means the part within the IfEndScore range
        ///     So, given the below assumptions, one only need to analyse the variable to make them within
        ///     the place, which is: just analyse 
        /// When `0`, then all other parts must also be `0`, just print them
        /// 
        /// TODO: Resolve Assumption:
        ///     only one central probability path to get out
        /// AND must get out -- there is no range of the random variable to change
        /// AND no modification to the score variable in the central path, no matter via random variable or not
        /// AND also the shortcut can be taken -- ONCE moved out of ifRange, it can never be satisfied again
        let stingsOfGrowingWalkPatternProbPaths () =
            // algorithm:
            // divide the two into two parts: the trivial part is the Zero part
            // the other part is the NegOne part -- for this part, just analyse other paths
            // as usual, we will need the other stings, while at the right place, we will need to insert
            // the target out path (`-1`) into the right place after the analysis is DONE
            // we perform the usual analysis for other parts of the paths
            let pureIfRange = boolExprToProposition program.mayIfScoreCond.Value in
            // multiple possibility
            // loopGuard /\ ~ifGuard
            let outsideIfRanges = propToValidConjCmpList true $ And [ Not pureIfRange; loopGuard ] in
            // for outside ranges, one just need to add `0` items
            let outsideIfRanges =
                List.map (concatConjCmpList loopAndInvConjCmpList) outsideIfRanges
                |> List.filter checkConjCmpListSAT
            in
            let centralIdx = outPathIdx in
            
            // the all `0` stings for the outside ranges
            let outsideStings =
                let produceZeroStings guard =
                    Sting (guard, List.map (constFunc $ SINormal LZero) enumeratedAssnPaths)
                in
                List.map produceZeroStings outsideIfRanges in
            
            // generate the central `-1` item
            let (AssignmentPath (_,centralPath, _)) = List.item centralIdx enumeratedAssnPaths in
            let centralNegOneStingItem =
                getInvolvedRandomVarsFromAssnLst centralPath
                |> flip formNoVarRangeStingItem LNegOne in
            
            /// the new loopGuard with also the IfRange for the other items
            let otherAssnPaths = List.removeAt centralIdx enumeratedAssnPaths in
            let stingsWithoutCentralPath =
                List.map (fun (AssignmentPath (_,updates, _)) -> updates) otherAssnPaths
                |> List.map (flip enumNonBreakPathInfo $ Some pureIfRange)
                |> combineInfoLstOfPaths in
            
            let fullInRangeStings =
                let addCentralItem (Sting (guard, items)) =
                    Sting (guard, List.insertAt centralIdx centralNegOneStingItem items)
                in
                List.map addCentralItem stingsWithoutCentralPath in
                
            // concatenate both `in` and `out`
            fullInRangeStings ++ outsideStings
        
        
            
        
        /// enumerate all the paths and then try to let all the SAT parts work together
        /// - l1#l2#...#ln when the final condition holds together
        let stingsOfUsualPatternProbPaths () =
            List.map (enumPossiblePathInfo None) enumeratedAssnPaths
            |> combineInfoLstOfPaths
        
        /// a general form to declare every given single branches
        let declareEverySingleBranchInformation branches =
            branches
            |> List.map (fun (Edge (_,_,lst)) ->
                let toBreak, lst =
                    swap $ until (function ESBreak -> false | _ -> true) lst in
                let doesNotMention var =
                    function
                    | ESAssign (thisVar, _) -> var <> thisVar
                    | _ -> true
                in
                let lst =
                    // if it is `toBreak` and has a score variable, and this variable is not mentioned
                    // add an additional var:=var statement at the end
                    if toBreak &&
                       Option.isSome endLoopScoreVariable &&
                       List.forall (doesNotMention endLoopScoreVariable.Value) lst then
                        let var = endLoopScoreVariable.Value in
                        lst ++ [ ESAssign (var, AVar var) ]
                    else lst
                in
                $"{List.length lst}" ::
                List.map (function
                    | ESAssign (var, expr) -> $"assignment#{var}:={expr}"
                    | ESScore  expr        ->
                        "score#" + (match expr with
                                    | AConst _  -> "constant"
                                    | _         -> "polynomial") @ expr.ToString ()
                    | ESBreak              -> "") lst
                |> fromListGenOutput)
            |> fromListGenOutput
        
        let outputDivisionInformation stings =
            let number_of_stings = toString $ List.length stings in
            number_of_stings ::
            List.map outputSting stings
            |> fromListGenOutput
            
        
        let analyseProbBranches () =
            let probs =
                match analysisPaths with
                | PLCond _     -> IMPOSSIBLE ()
                | PLProb probs -> probs
            in
            // assume that this is the pure combination of probability branches
            // no further if (bool) branches possible
            let declare_branches_types =
                "probs=" +
                (String.concat " " $ List.map (fun (ProbPath (prob, _, _)) ->
                    toString $ normaliseArithExpr prob) probs)
            in
            // patterns:
            // 1. If it is `break` and involves the target variable `v` to declare:
            //    `1`
            //    assignment#v:=v
            // 2. Otherwise:
            //    number_of_statements
            //    {statements}*
            let declare_every_single_branch_information () =
                declareEverySingleBranchInformation enumeratedEdges
            in
            /// There are 3 patterns to match in this part:
            /// 1. With EndScore while NO IfEndScore and NO final update formula information found
            ///    in this case, one will need to consider computing the actual range of the score variable
            ///    and the division for these paths are:
            ///    - `-1` {#1}* for the central range to divide
            ///    - `0` {#1}* for other ranges
            /// 2. With EndScore yet NO final update formula information and WITH IfEndScore
            ///    in this case, one will need to use the IfEndScore range as the `0` for all paths:
            ///    - `-1` {#1}* for the part with the IfEndScore range
            ///    - `0` {#1}* for the parts outside of the IfEndScore range
            /// 3. The usual part --
            ///    enumerate all the paths and then try to let all the SAT parts work together
            ///    - l1#l2#...#ln when the final condition holds together
            let division_information () =
    //            let withEndScore = Option.isSome program.mayEndScore in
                let withIfEndScore = Option.isSome program.mayIfScoreCond in
                let withFinalRandVarUpdate = hasFinalUpdate in
                let hasEndVariable = Option.isSome endLoopScoreVariable in
                let stings =
                    if hasEndVariable && not withIfEndScore && not withFinalRandVarUpdate then
                        stingsOfParaEstimatePatternProbPaths ()
                    elif hasEndVariable && not withFinalRandVarUpdate && withIfEndScore then
                        stingsOfGrowingWalkPatternProbPaths ()
                    else
                        stingsOfUsualPatternProbPaths ()
                in
                outputDivisionInformation stings
            in
            [
                // probs=...
                declare_branches_types
                // number_of_actual_statements
                // {statements}+
                declare_every_single_branch_information ()
                // division information
                // sting_number
                // every_sting_information
                division_information ()
            ]
            |> fromListGenOutput
        
        /// Format:
        /// number_of_sub_branches
        /// {segment}+
        /// for each segment, print in the style:
        /// prob={probs}*
        /// declare_segment_branches_information
        /// division_information
        let analyseConditionalProbBranches () =
            let segmentDecl (segmentGuard, ess, segment) =
                let edges =
                     List.map (fuseStmtListToProbPath ess) segment
                     |> List.map collectEdgeStmtFromProbPath
                     |> List.concat
                in
                let declare_branch_type =
                    "probs=" +
                    String.concat " " (List.map (fun (ProbPath (prob, _, _)) ->
                        toString $ normaliseArithExpr prob) segment)
                in
                let declare_segment_branches_information () =
                    declareEverySingleBranchInformation edges
                in
                let assnLst = List.map edgeToAssnPath edges in
                let division_information () =
    //                let toChoose (Sting (guard, lst)) =
    //                    let guard =
    //                        let (ConjCmps lst) = concatConjCmpList guard segmentGuard in
    //                        ConjCmps $ List.distinct lst
    //                    in
    //                    if not $ checkConjCmpListSAT guard then None
    //                    else Some $ Sting (guard, lst)
    //                in
                    List.map (enumPossiblePathInfo $ Some segmentGuard) assnLst
                    |> combineInfoLstOfPaths
                    |> outputDivisionInformation
                in
                [
                    declare_branch_type
                    declare_segment_branches_information ()
                    division_information ()
                ]
                |> fromListGenOutput
            in
            let conds =
                match analysisPaths with
                | PLCond conds -> conds
                | _ -> IMPOSSIBLE ()
            in
            let number_of_sub_branches = toString $ List.length conds in
            conds
            |> List.map (fun (ConditionalPath (guard, ess, nextParts)) ->
                (boolExprToProposition guard,
                 ess,
                 nextParts))
            |> List.map segmentDecl
            |> curry List.Cons number_of_sub_branches
            |> fromListGenOutput
        
        /// conditional branches
        /// conditional={1}+
        /// every_single_branch_declaration
        /// number_of_stings  // must equal to branch_amount
        /// stings
        let analyseConditionalBranches () =
            let conds =
                match analysisPaths with
                | PLCond conds -> conds
                | _ -> IMPOSSIBLE ()
            in
            let toSting (ConditionalPath (cGuard, ess, _)) =
                let guard = boolExprToProposition cGuard in
                if not $ checkSAT (mkQueryCtx ()) [ guard ] then None else
                let (AssignmentPath (_,assnLst, _)) = edgeToAssnPath (Edge (cGuard, AConst NUMERIC_ONE, ess)) in
                let ret x = Some (Edge (cGuard, AConst NUMERIC_ONE, ess), x) in
                let anaRes = pathDivisionAnalysis {
                        path = assnLst
                        fixedGuard = And [ guard; loopInvariant ]
                        loopGuard = loopGuard
                        mayEndIfScoreGuard = Option.map boolExprToProposition program.mayIfScoreCond
                        randVarRanges = randVarRanges
                        takeZeroShortcut = true
                    }
                in
                match anaRes with
                | [ x ] ->
                    match x with
                    | NLSingle (loc, locGuard) ->
                        ret $ Sting (locGuard, [ assnLstToNoVarRangeSting assnLst loc ])
                    | NLJoin (totalGuard, concreteRange) ->
                        ret $ Sting (totalGuard, [ SIAbnormalMultiLocs concreteRange ])
                | [] -> IMPOSSIBLE ()  // should have a special mark -- this should not happen
                | _ -> failwith "Division for if (bool) type paths supports at most ONE type."
            in
            // may filter the not possible edges -- those with guard not possible to be executed
            let validEdges, stings = List.unzip $ List.choose toSting conds in
            let branch_types_decl = "conditional=" + String.concat " " (List.map (fun _ -> "1") validEdges) in
            let declare_every_single_branch () = declareEverySingleBranchInformation validEdges in
            let number_of_stings = toString $ List.length stings in
            let stings () = fromListGenOutput $ List.map outputSting stings in
            [
                branch_types_decl
                declare_every_single_branch ()
                number_of_stings
                stings ()
            ]
            |> fromListGenOutput
        
        let branches_division_information () =
            match analysisPaths with
            | PLCond conds ->
                // Required Assumption:
                //      Either all elements are having internal prob branch
                //      Or all elements do NOT have internal prob branch
                // depends on whether the inside stuff is prob
                let (ConditionalPath (_, _, nextParts)) = conds[0] in
                match nextParts with
                // if it is, combine locally the probabilities
                | _ :: _  -> analyseConditionalProbBranches ()
                // if it is not, report every single divided result
                | []      -> analyseConditionalBranches ()
            | PLProb _ ->
                // combine the information of single analysis
                analyseProbBranches ()
        
        member public x.GenerateOutput () =
            [
                program_name @ program_type
                list_of_pre_assn_program_vars
                number_of_random_variables
                random_variable_type_declarations ()
                truncation_or_not @ termination_type
                if toTruncate then truncation_paths_information ()
                end_score_information ()
                "locations@2"
                "loc=1"
                branches_division_information ()
                "out"
            ]
            |> fromListGenOutput



    /// for something like: x = x + 1, x = x + 2
    /// combine to x = x + 3
    /// More generally, every variable is assigned for only once, with the RHS variables being the
    /// ones BEFORE EXECUTING THE PATH
    /// that is, for the RESULTING assignments:
    /// x1 = P1
    /// x2 = P2
    /// even if P2 contains x1, it should refer to the one BEFORE P1 is assigned to x1
    /// Hence, the return value is a map for each variable, with NO ORDER
    let combineAssns (AssignmentPath (_, updates, _)) =
        let aggrUpdates updateMap (v, expr) =
            Map.add v (substVars expr updateMap) updateMap in
        List.fold aggrUpdates Map.empty updates
        |> Map.map (fun _ -> normaliseArithExpr)

    type SimSign =
        | SSPos
        | SSNeg
        | SSZero
        | SSNonFixed
        member x.SignNum =
            match x with
            | SSPos -> Some 1
            | SSNeg -> Some (-1)
            | SSZero -> Some 0
            | SSNonFixed -> None
        static member FromSigNum sn =
            match sn with
            | -1 -> SSNeg
            | 1 -> SSPos
            | 0 -> SSZero
            | _ -> SSNonFixed
    
    type Monotonicity =
        /// x = x + 1
        | MInc
        /// x = x - 1
        | MDec
        /// x = x
        | MUnchanged
        /// x = 1
        | MReset
        /// x = x + 1 | x = x - 1
        | MNonFixed
    
    type InvariantGeneration (program : Program, rvRanges : Map<Variable, Numeric * Numeric>) =
        let isTab3 = Flags.TABLE = 3
        let allAssnPathInfo =
            enumAllAssnPaths program
            |> List.map combineAssns
        let preLoopAssn =
            let exInfo = function STAssn (v, e) -> (v, normaliseArithExpr e) | _ -> IMPOSSIBLE () in
            List.map exInfo program.assnLst
            |> Map.ofList
        let preAssnIsRv var =
            match Map.find var preLoopAssn with
            | AVar _ -> true
            | _ -> false
        let preAssnIsConst var =
            match Map.find var preLoopAssn with
            | AConst _ -> true
            | _ -> false
        /// all variables appearing in all conditional guards
        let condVars =
            let endLoopIfVars = Option.defaultValue Set.empty $ Option.map collectVars program.mayIfScoreCond in
            let rec condVars (st : Statement) : Set<Variable> =
                match st with
                | STIfBool lst ->
                    let mapper (g, lst) =
                        List.map condVars lst
                        |> Set.unionMany
                        |> Set.union (collectVars g) in
                    Set.unionMany $ List.map mapper lst
                | STIfProb (pExpr, t, f) ->
                    let lst = List.map condVars t ++ List.map condVars f in
                    Set.unionMany lst
                    |> Set.union (collectVars pExpr)
                | STAssn _ | STBreak | STSkip | STInLoopScore _ ->
                    Set.empty in
            List.map condVars program.loopBody
            |> Set.unionMany
            |> Set.union (collectVars program.loopGuard)
            |> Set.union endLoopIfVars
        /// all variables appearing in all score statements
        let scoreVars =
            let endScoreVars =
                match program.mayEndScore with
                | None -> Set.empty
                | Some (ScoreArith e) -> collectVars e
                | Some (ScoreDist (_, e)) -> collectVars e
            in
            let rec scoreVars st =
                match st with
                | STIfBool lst ->
                    let mapper (_, lst) = Set.unionMany $ List.map scoreVars lst in
                    Set.unionMany $ List.map mapper lst
                | STIfProb (_, t, f) ->
                    Set.unionMany (List.map scoreVars t ++ List.map scoreVars f)
                | STInLoopScore sExpr -> collectVars sExpr
                | STAssn _ | STBreak | STSkip -> Set.empty
            in
            List.map scoreVars program.loopBody
            |> Set.unionMany
            |> Set.union endScoreVars
        let inLoopGuard var = Set.contains var $ collectVars program.loopGuard
        let inAnyCond var = Set.contains var condVars
        let inAnyScore var = Set.contains var scoreVars
        let shouldIgnoreVar var =
            if preAssnIsRv var then
                inLoopGuard var || not (inAnyCond var)
            elif preAssnIsConst var then
                if isTab3 then false
                else not (inAnyCond var) && not (inAnyScore var)
            else
                failwith
                    $"Pre-loop assignment for variable {var} is neither random variable nor constant."
        let topoSort depOn (vertices : _ list) =
            let visited = HashSet<_>() in
            let rec dfs acc v =
                let folder acc v' = if depOn v v' then dfs acc v' else acc in
                if not $ visited.Add v then acc
                else v :: List.fold folder acc vertices
            in
            List.rev $ List.fold dfs [] vertices
        let colDep pVarSet =
            let folder accDep pathAssnMap =
                let addToAccDep accDep (v, expr) =
                    let oriSet = Option.defaultValue Set.empty $ Map.tryFind v accDep in
                    collectVars expr
                    |> Set.intersect pVarSet
                    |> Set.union oriSet
                    |> flip (Map.add v) accDep
                in
                Map.toList pathAssnMap
                |> List.fold addToAccDep accDep
            in
            List.fold folder Map.empty allAssnPathInfo
        let reorderByDependency (pVars : Variable list) =
            let pVarSet = Set.ofList pVars in
            let dependencies = colDep pVarSet in
            let depOn x y = match Map.tryFind x dependencies with
                            | Some s -> Set.contains y s
                            | None -> false in
            topoSort depOn pVars
        let constSign c =
            if c > NUMERIC_ZERO then SSPos
            elif c < NUMERIC_ZERO then SSNeg
            else SSZero
        let varSign signs v =
            match Map.tryFind v signs with
            | Some s -> s
            | None -> failwith $"variable \"{v}\" has no sign."
        let unionSignVal x y =
            match x, y with
            | SSZero, _ -> y
            | _, SSZero -> x
            | SSNeg, SSNeg -> SSNeg
            | SSPos, SSPos -> SSPos
            | _ -> SSNonFixed
        let rec exprSign signs expr =
            let mergeAdd x y = unionSignVal x y in
            let mergeMul (x : SimSign) (y : SimSign) =
                let x = Option.defaultValue 11 $ x.SignNum in
                let y = Option.defaultValue 11 $ y.SignNum in
                SimSign.FromSigNum (x * y) in
            let negSign x =
                match x with
                | SSPos -> SSNeg
                | SSNeg -> SSPos
                | _ -> x
            match expr with
            | AConst c -> constSign c
            | AVar v -> varSign signs v
            | AOperation (op, lst) ->
                let lst = List.map (exprSign signs) lst in
                match op, lst with
                | OpAdd, lst -> List.fold mergeAdd SSZero lst
                | OpMul, lst -> List.fold mergeMul SSPos lst
                | OpMinus, [x] -> negSign x
                | OpMinus, (hd :: lst) ->
                    List.fold mergeAdd SSZero lst
                    |> negSign
                    |> mergeAdd hd
                | OpDiv, lst -> List.fold mergeMul SSPos lst
                | OpMinus, [] -> failwith "EMPTY EXPRESSION."
        let allLoopAssns var =
            let relatedAssns var pathAssnInfo =
                Map.toList pathAssnInfo
                |> List.filter (fst >> fun v' -> v' = var) in
            List.map (relatedAssns var) allAssnPathInfo
            |> List.concat
            |> List.map snd
        let varSigns =
            let rvSigns =
                let getSign (lower, upper) =
                    if upper < NUMERIC_ZERO then SSNeg
                    elif lower > NUMERIC_ZERO then SSPos
                    elif upper = NUMERIC_ZERO && lower < NUMERIC_ZERO then SSNeg
                    elif lower = NUMERIC_ZERO && upper > NUMERIC_ZERO then SSPos
                    elif lower = NUMERIC_ZERO && upper = NUMERIC_ZERO then SSZero
                    else SSNonFixed
                in
                Map.toList rvRanges
                |> List.map (BiMap.sndMap getSign) in
            let genSign accSign var =
                let pickInitVal st =
                    match st with
                    | STAssn (v, expr) -> if v = var then Some $ exprSign accSign expr else None
                    | _ -> IMPOSSIBLE () in
                let initVal =
                    match List.tryPick pickInitVal program.assnLst with
                    | Some sign -> sign
                    | None -> failwith $"No initial value is given to variable \"{var}\"."
                in
                /// the temporary value should use the first value as the temporary hint
                let tmpAccSign = Map.add var initVal accSign in
                allLoopAssns var
                |> List.map (exprSign tmpAccSign)
                |> List.fold unionSignVal SSZero
                |> flip (Map.add var) accSign in
            getPreAssnProgVars program
            |> reorderByDependency
            // |> (fun x -> debugPrint $"{x}"; x)
            |> List.fold genSign (Map.ofSeq rvSigns)
        let toNormalisedXFormulaList var expr =
            arithExprToNormalisedPolynomial expr
            |> polynomialToXFormula var
            |> Map.toList
            |> List.sortBy fst
        let getLocalMonotonicity var expr =
            match toNormalisedXFormulaList var expr with
            | [] -> failwith "Empty Expression."
            | [ (0u, _) ] -> MReset
            | [ (1u, Polynomial [ (num, []) ] ) ] ->
                match Map.find var varSigns with
                | SSPos ->
                    if num < NUMERIC_ZERO then MNonFixed
                    elif num = NUMERIC_ZERO then MReset
                    elif num < NUMERIC_ONE then MDec
                    elif num = NUMERIC_ONE then MUnchanged
                    else MInc
                | SSNeg ->
                    if num < NUMERIC_ZERO then MNonFixed
                    elif num = NUMERIC_ZERO then MReset
                    elif num < NUMERIC_ONE then MInc
                    elif num = NUMERIC_ONE then MUnchanged
                    else MDec
                | SSZero -> MUnchanged
                | SSNonFixed ->
                    if num < NUMERIC_ZERO then MNonFixed
                    elif num = NUMERIC_ZERO then MReset
                    elif num < NUMERIC_ONE then MNonFixed
                    elif num = NUMERIC_ONE then MUnchanged
                    else MNonFixed
            | [ (0u, p0); (1u, p1) ] ->
                let zSign = exprSign varSigns $ polynomialToArithExpr p0 in
                let oSign = exprSign varSigns $ polynomialToArithExpr p1 in
                match oSign, zSign with
                | SSPos, SSPos -> MInc
                | SSPos, SSNeg -> MDec
                | SSPos, SSZero -> failwith "Unknown case."
                | SSPos, SSNonFixed -> MNonFixed
                | SSNeg, _ -> MNonFixed
                | SSZero, _ -> MReset
                | SSNonFixed, _ -> MNonFixed
            | _ -> failwith "Currently Support Only Linear Expression."
        let joinLocMono var =
            let joinMono x y =
                match x, y with
                | MInc, MInc -> MInc
                | MDec, MDec -> MDec
                | MInc, MDec | MDec, MInc -> MNonFixed
                | MUnchanged, v | v, MUnchanged -> v
                | MReset, _ | _, MReset -> failwith "Unknown case."
                | MNonFixed, _ | _, MNonFixed -> MNonFixed in
            allLoopAssns var
            |> List.map (getLocalMonotonicity var)
            |> List.fold joinMono MUnchanged
        let isMonoInc var = MInc = joinLocMono var
        let isMonoDec var = MDec = joinLocMono var
        let noUpdate var = List.isEmpty $ allLoopAssns var
        let lowerBoundByPreLoopAssn var =
            match Map.find var preLoopAssn with
            | AConst c -> BCompare (CmpGe, AVar var, AConst c)
            | AVar rv ->
                match Map.tryFind rv rvRanges with
                | None ->
                    failwith
                        $"The initial non-constant value of variable \"{var}\" is not a random variable."
                | Some (lower, _) -> BCompare (CmpGe, AVar var, AConst lower)
            | _ -> IMPOSSIBLE ()
        let upperBoundByPreLoopAssn var =
            match Map.find var preLoopAssn with
            | AConst c -> BCompare (CmpLe, AVar var, AConst c)
            | AVar rv ->
                match Map.tryFind rv rvRanges with
                | None ->
                    failwith
                        $"The initial non-constant value of variable \"{var}\" is not a random variable."
                | Some (_, upper) -> BCompare (CmpLe, AVar var, AConst upper)
            | _ -> IMPOSSIBLE ()
        let genBasicInvConds var =
            if isMonoInc var then [ lowerBoundByPreLoopAssn var ]
            elif isMonoDec var then [ upperBoundByPreLoopAssn var ]
            elif noUpdate var then
                [ lowerBoundByPreLoopAssn var
                  upperBoundByPreLoopAssn var ]
            // has update while is not monotone
            else []
        /// v = v + c * rv
        let maxRvUpdate v =
            let rvUpdate e =
                match toNormalisedXFormulaList v e with
                | [] -> failwith "EMPTY EXPRESSION."
                | [ (0u, Polynomial [ n0, [ rv ] ]); (1u, Polynomial [ num, [] ]) ] ->
                    if num = NUMERIC_ONE then
                        match Map.tryFind rv rvRanges with
                        | Some (lower, upper) -> Some $ max (n0 * lower) (n0 * upper)
                        | _ -> None
                    else None
                | _ -> None
            allLoopAssns v
            |> List.choose rvUpdate
            |> function
            | [] -> None
            | lst -> Some (List.max lst)
        let genEndLoopIfCond var =
            let binder bExpr =
                match bExpr with
                | BCompare (CmpLe, AVar v, AConst c)
                        | BCompare (CmpGe, AConst c, AVar v) when v = var ->
                    if c.IsInt then
                        let cmpProp maxVal = BCompare (CmpLe, AVar v, AConst $ c + maxVal) in
                        Option.map cmpProp $ maxRvUpdate v
                    else None
                | _ -> None
            Option.bind binder $ program.mayIfScoreCond
        let genVarInvConds var =
            genBasicInvConds var ++ Option.toList (genEndLoopIfCond var)
        member x.GenerateInvariant () =
            getPreAssnProgVars program
            |> List.filter (not << shouldIgnoreVar)
            |> List.collect genVarInvConds
            |> function
            | [] -> BTrue
            | lst -> List.reduce (curry BAnd) lst

end

// let genInvariant program rvRanges =
//     let ignoreVar program isTab3 var =
//         if preAssnIsRv var then
//             inLoopGuard program var || notInAnyCond program var
//         elif preAssnIsConst var then
//             if isTab3 then false
//             else notInAnyCond program var && notInAnyScore program var
//         else
//             failwith
//                 $"Pre-loop assignment for variable {var} is neither random variable nor constant."
//     in
//     let pVars = 
//         getPreAssnProgVars program
//         |> List.filter (not << ignoreVar program (Flags.TABLE = 3))
//         |> reorderByDependency program
//     in
//     |> List.fold (genVarInvConds program) (rvRanges, [])
//     |> snd
//     |> List.fold (curry BAnd) BTrue

let genOutput input =
    let generator = Impl.InvariantGeneration (input.program, input.randVarRanges) in
    let programWithInv = {
        input.program with invariant = generator.GenerateInvariant ()
    } in
    debugPrint $"Generated Program Invariant: \"{programWithInv.invariant}\".";
    let input = { input with program = programWithInv } in
    let analyser = Impl.OutputAnalysis input in
    analyser.GenerateOutput ()

let genAllSp () =
    let all = try getAllDecFiles () with | _ -> [] in
    let folder map (fName : string, content) =
        let addToComp compF =
            let name = fName[..fName.Length-5] in
            let v =
                Map.tryFind name map
                |> Option.defaultValue (None, None)
            in
            Map.add name (compF (fun _ -> Some content) v) map
        in
        if fName.EndsWith "-ipt" then
            addToComp BiMap.fstMap
        elif fName.EndsWith "-cfg" then
            addToComp BiMap.sndMap
        else IMPOSSIBLE ()
    in
    List.fold folder Map.empty all
    |> Map.map (fun name v ->
        match v with
        | (Some ipt, Some cfg) -> (ipt, Some cfg)
        | (None, _) -> failwith $"Name \"{name}\" has no input file."
        | (_, None) -> failwith $"Name \"{name}\" has no config file.")
        

type ConfigCtx =
    {
        cfgProgram : Program
        cfgRandVars : (Variable * Distribution) list
        cfgDegOne : uint
        cfgDegTwo : uint
        cfgDefDivM : uint
        cfgVarDivM : Map<Variable, uint>
        cfgVarRanges : Map<Variable, RealInf * RealInf>
        cfgSolver : string
        cfgTable : uint
    }

let private declVarRanges progVars ctx =
    let declAVar var =
        let (min, max) =
            match Map.tryFind var ctx.cfgVarRanges with
            | Some range -> range
            | None -> BiMap.bothMap RINum Flags.DEFAULT_CONFIG_VAR_RANGE
        in
        toString var + "@" + min.ToString "float" + " " + max.ToString "float"
    in
    List.map declAVar progVars
    |> fromListGenOutput
    
let printDistRange (Distribution (distTy, arg)) =
    let arg = flip List.map arg $ fun x -> x.ToString "float" in
    match distTy, arg with
    | DContinuousUniform, [x; y] -> $"{x} {y}"
    | DBeta, [_; _] -> $"0 1"
    | _ -> failwith "Unknown way to declare distribution."

let private declProgVarInitVal usedVars ctx =
    let randVars = Map.ofSeq ctx.cfgRandVars in
    let analyseExpr var expr =
        match expr with
        | AConst c -> $"constant@{c}"
        | AVar rv ->
            let dist =
                match Map.tryFind rv randVars with
                | Some dist -> dist
                | None ->
                    failwith
                        $"Invalid starting assignment \"{var} = {expr}\" -- neither constant nor random variable."
            in
            let divM =
                Option.defaultValue ctx.cfgDefDivM $ Map.tryFind var ctx.cfgVarDivM
            in
            $"random@{printDistRange dist}@{divM}"
        | _ -> failwith $"Invalid starting assignment \"{var} = {expr}\" -- neither constant nor random variable."
    in
    let analyse var expr = toString var + "@" + analyseExpr var expr in
    let declAnAssn assn =
        match assn with
        | STAssn (var, expr) ->
            if Set.contains var usedVars then analyse var expr
            else ""
        | _ -> IMPOSSIBLE ()
    in
    ctx.cfgProgram.assnLst
    |> List.map declAnAssn
    |> fromListGenOutput

let genConfigOutput input =
    let progVars = getPreAssnProgVars input.cfgProgram in
    [
        toString input.cfgDegOne
        toString input.cfgDegTwo
        "Table@T" + toString input.cfgTable
        "solver@" + toString input.cfgSolver
        "bounded_domain"
        declVarRanges progVars input
        "no_common_invs"
        "initial_inputs"
        declProgVarInitVal (Set.ofList progVars) input
    ]
    |> fromListGenOutput
