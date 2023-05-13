module ProgramAnalyser.Analysis

open Microsoft.FSharp.Collections
open Objects
open ProgramAnalyser.Global
open ProgramAnalyser.Logic
open ProgramAnalyser.Logic.DisjunctiveNormal
open ProgramAnalyser.ParserSupport
open ProgramAnalyser.Polynomial
open ProgramAnalyser.Utils


/// the statements that are to appear on the edge
type EdgeStatement =
    | ESAssign of Variable * ArithExpr
    | ESScore of ArithExpr
    | ESBreak
    override x.ToString () =
        match x with
        | ESAssign (var, expr) -> $"{var}:={expr}"
        | ESScore expr -> $"score({expr})"
        | ESBreak -> "break"

/// the supportive structure to help discover possible paths
type private Node =
    | NEnd
    | NNormal of EdgeStatement * Node
    | NProb of (ArithExpr * Node) list
    | NIf of (BoolExpr * Node) list

let rec private appendNode above below =
    match above with
    | NEnd -> below
    | NNormal (es, node) -> NNormal (es, appendNode node below)
    | NProb lst ->
        NProb $ List.map (BiMap.sndMap (flip appendNode below)) lst
    | NIf lst ->
        NIf $ List.map (BiMap.sndMap (flip appendNode below)) lst

let rec private statementsToTree statements =
    match statements with
    | [] -> NEnd
    | stmt :: lst ->
        let rest = statementsToTree lst in
        match stmt with
        | STSkip -> rest
        | STBreak -> NNormal (ESBreak, rest)
        | STAssn (var, expr) -> NNormal (ESAssign (var, expr), rest)
        | STInLoopScore expr -> NNormal (ESScore expr, rest)
        | STIfBool lst ->
            NIf $ flip List.map lst (fun (cond, statements) ->
                (cond, appendNode (statementsToTree statements) rest))
        | STIfProb (prob, lT, lF) ->
            [ (prob, lT)
              (AOperation (OpMinus, [AConst (Numeric 1); prob]), lF) ]
            |> List.map (fun (prob, statements) ->
                (prob, appendNode (statementsToTree statements) rest))
            |> NProb            

let rec simplyBoolExpr bExpr =
    match bExpr with
    | BAnd (b1, b2) ->
        match (simplyBoolExpr b1, simplyBoolExpr b2) with
        | (b1, BTrue) -> b1
        | (BTrue, b2) -> b2
        | (BFalse, _) -> BFalse
        | (_, BFalse) -> BFalse
        | (b1, b2) -> BAnd (b1, b2)
    | _ -> bExpr

type ConditionalPath =
    | ConditionalPath of
        cond:BoolExpr *
        statements:EdgeStatement list *
        nextParts:ProbPath list
and ProbPath =
    | ProbPath of
        prob:ArithExpr *
        statements:EdgeStatement list *
        nextParts:ConditionalPath list

let rec private collectConditionalPaths node =
    match node with
    | NEnd -> [ ConditionalPath (BTrue, [], []) ]
    | NNormal (es, next) ->
        let addOne some =
            match some with
            | ConditionalPath (guard, ess, nextParts) ->
                ConditionalPath (guard, es :: ess, nextParts)
        in
        List.map addOne $ collectConditionalPaths next
    | NIf lst ->
        let mapper (guard, nextNode) =
            let restPaths = collectConditionalPaths nextNode in
            List.map (fuseGuardToPath guard) restPaths
        in
        List.concat $ List.map mapper lst
    | NProb lst ->
        let probPaths =
            let mapper (prob, node) =
                collectProbPaths node
                |> List.map (fuseProbToPath prob)
            in
            List.concat $ List.map mapper lst
        in
        [ ConditionalPath (BTrue, [], probPaths) ]
and private collectProbPaths node =
    match node with
    | NEnd -> [ ProbPath (AConst NUMERIC_ONE, [], []) ]
    | NNormal(es, node) ->
        let addOne (ProbPath (prob, ess, condPaths)) =
            ProbPath (prob, es :: ess, condPaths)
        in
        List.map addOne $ collectProbPaths node
    | NProb lst ->
        let mapper (prob, node) =
            collectProbPaths node
            |> List.map (fuseProbToPath prob)
        in
        List.concat $ List.map mapper lst
    | NIf lst ->
        let condPaths =
            let mapper (guard, node) =
                collectConditionalPaths node
                |> List.map (fuseGuardToPath guard)
            in
            List.concat $ List.map mapper lst
        in
        [ ProbPath (AConst NUMERIC_ONE, [], condPaths) ]
and private fuseProbToPath prob (ProbPath (oriProb, ess, condPaths)) =
    ProbPath (AOperation (OpMul, [prob; oriProb]), ess, condPaths)
and private fuseGuardToPath guard (ConditionalPath (oriGuard, ess, nextParts)) =
    ConditionalPath (BAnd (guard, oriGuard), ess, nextParts)
    
type Edge = Edge of EdgeStatement list
    
let rec collectEdgeStmtFromCondPath (ConditionalPath (_, ess, nextParts)) =
    match nextParts with
    | [] -> [ Edge ess ]
    | lst -> List.map collectEdgeStmtFromProbPath lst
             |> List.concat
             |> List.map (fun (Edge lst) -> Edge $ ess ++ lst)
and collectEdgeStmtFromProbPath (ProbPath (_, ess, nextParts)) : Edge list =
    match nextParts with
    | [] -> [ Edge ess ]
    | lst -> List.map collectEdgeStmtFromCondPath lst
             |> List.concat
             |> List.map (fun (Edge lst) -> Edge $ ess ++ lst)
    
    
type PathList =
    | PLCond of ConditionalPath list
    | PLProb of ProbPath list
    
/// to make sure no updated variable is further inquired in `if` statement
/// A temporary function to ensure validity of format and hence the soundness of the algorithm
let private checkNoIfForUpdatedVars (node : Node) : bool =
    let rec containsVar toFind aExpr =
        match aExpr with
        | AConst _ -> false
        | AVar (Variable varName) -> Set.contains varName toFind
        | AOperation (_, lst) ->
            List.exists (containsVar toFind) lst
    in
    let rec guardNotContainingUpdatedVars updatedVars guard =
        match guard with
        | BCompare (_, a1, a2) ->
            not (containsVar updatedVars a1) && not (containsVar updatedVars a2)
        | BAnd (g1, g2) ->
            guardNotContainingUpdatedVars updatedVars g1 &&
            guardNotContainingUpdatedVars updatedVars g2
        | BTrue -> true
        | BFalse -> true
    in
    let rec checkNoFurtherIf updatedVars node =
        match node with
        | NEnd -> true
        | NNormal (ESAssign((Variable varName), _), node) ->
            checkNoFurtherIf (Set.add varName updatedVars) node
        | NNormal ((ESScore _), node) ->
            checkNoFurtherIf updatedVars node
        | NNormal (ESBreak, _) -> true  // after `break`, there is no need to check 
        | NProb lst ->
            List.map snd lst
            |> List.forall (checkNoFurtherIf updatedVars)
        | NIf lst ->
            let check (guard, node) =
                guardNotContainingUpdatedVars updatedVars guard &&
                checkNoFurtherIf updatedVars node
            in
            List.forall check lst
    in
    checkNoFurtherIf Set.empty node
    
let fuseStmtListToProbPath ess path =
    match path with
    | ProbPath (prob, ess', nextParts) -> ProbPath (prob, ess ++ ess', nextParts)
    
let checkValidPathList pathList =
    let checkProbPath (ProbPath (_, _, lst)) = List.isEmpty lst in
    let checkCondPath (ConditionalPath (_, _, lst)) = List.forall checkProbPath lst in
    match pathList with
    | PLCond lst -> List.forall checkCondPath lst
    | PLProb lst -> List.forall checkProbPath lst
    
let computePaths statements =
    let node = statementsToTree statements in
    if not $ checkNoIfForUpdatedVars node then
        failwith "The current version supports only update once in a round in the loop.";
    let quasiResult =
        match collectConditionalPaths node with
        | [ (ConditionalPath (BTrue, ess, nextParts)) ] when nextParts.Length > 0 ->
            // if no branch at first
            // it is essentially a list of the ProbPaths
            // add the prepending elements into the ProbPaths
            PLProb $ List.map (fuseStmtListToProbPath ess) nextParts
        | lst ->
            PLCond lst
    in
    if not $ checkValidPathList quasiResult then
        failwith "The current version supports at most 2 level of nesting `if`.";
    quasiResult

//let fuseStmtToPath stmt path =
//    match path with
//    | PConditional (ConditionalPath (guard, sts, next)) ->
//        PConditional (ConditionalPath (guard, stmt :: sts, next))
//    | PProb (ProbPath (prob, sts, next)) ->
//        PProb (ProbPath (prob, stmt :: sts, next))
//    | PUnknown sts -> PUnknown $ stmt :: sts
//
//let fuseListOfStmtToPath toAdd path =
//    match path with
//    | PConditional (ConditionalPath (guard, sts, next)) ->
//        PConditional (ConditionalPath (guard, toAdd ++ sts, next))
//    | PProb (ProbPath (prob, sts, next)) ->
//        PProb (ProbPath (prob, toAdd ++ sts, next))
//    | PUnknown sts -> PUnknown $ toAdd ++ sts
//
///// to append the path p1 before p2
//let rec mergePath p1 p2 : Path =
//    match p1 with
//    | PUnknown sts ->
//        fuseListOfStmtToPath sts p2
//    | PConditional (ConditionalPath (guard, sts, [])) ->
//        match p2 with
//        | PConditional (ConditionalPath (g2, sts', next)) ->
//            PConditional (ConditionalPath (BAnd (guard, g2), sts ++ sts', next))
//        | PProb pPath ->
//            PConditional (ConditionalPath (guard, sts, [pPath]))
//        | PUnknown sts' ->
//            PConditional (ConditionalPath (guard, sts ++ sts', []))
//    | PProb (ProbPath (prob, sts, [])) ->
//        match p2 with
//        | PProb (ProbPath (prob', sts', next)) ->
//            PProb (ProbPath (AOperation (OpMul, [prob; prob']), sts ++ sts', next))
//        | PConditional condPath ->
//            PProb (ProbPath (prob, sts, [condPath]))
//        | PUnknown sts' ->
//            PProb (ProbPath (prob, sts ++ sts', []))
//    // if this part is not the last part, go to the last part to append
//    | PConditional (ConditionalPath (guard, sts, lst)) when not lst.IsEmpty ->
//        match mergePath (PProb probPath) p2 with
//        | PProb pPath -> PConditional (ConditionalPath (guard, sts, Some pPath))
//        | _ -> IMPOSSIBLE ()
//    | PProb (ProbPath (prob, sts, Some condPath)) ->
//        match mergePath (PConditional condPath) p2 with
//        | PConditional condPath -> PProb (ProbPath (prob, sts, Some condPath))
//        | _ -> IMPOSSIBLE ()
//
///// to add the guard is the same as join an empty path with the target guard with the target path
//let fuseGuardToPath guard path =
//    mergePath (PConditional (ConditionalPath (guard, [], None))) path
//
///// to add the probability is the same as join an empty path with the target probability with the target path
//let fuseProbToPath prob path =
//    mergePath (PProb (ProbPath (prob, [], None))) path
//
///// given a list of Parse Statement, returns the actual running paths
//let rec computePaths statements =
//    /// an abstract function to compute the branches
//    let computeBranches branches fuseBranchHeadToPath rest =
//        branches
//        |> List.map (fun (head, content) ->
//            computePaths content
//            |> List.map (fuseBranchHeadToPath head)
//            // monad operation: for each path from local and from rest, join them
//            |> List.map (flip List.map rest << mergePath)  // (fun path -> (List.map (mergePath path) rest))
//            |> List.concat)
//        |> List.concat
//    in
//    match statements with
//    | [] -> [ PUnknown [] ]
//    | statement :: lst ->
//        let rest = computePaths lst in
//        match statement with
//        | STSkip -> rest
//        | STAssn(var, expr) -> List.map (fuseStmtToPath (ESAssign (var, expr))) rest
//        | STInLoopScore expr -> List.map (fuseStmtToPath (ESScore expr)) rest
//        | STIfBool lst ->
//            computeBranches lst fuseGuardToPath rest
//        | STIfProb (prob, contentTrue, contentFalse) ->
//            let branches = [
//                (prob, contentTrue)
//                (AOperation (OpMinus, [AConst (Numeric 1); prob]), contentFalse)
//            ] in
//            computeBranches branches fuseProbToPath rest

/// greater-or-equal conjunction
/// which is of form:
/// e1 >= 0 /\ e2 >= 0 /\ ... /\ en >= 0
/// hence the only thing to store is simply [e1, e2, ..., en]
/// true is [] and false is like [-1] or any arithmetic expression `e` to make e < 0 holds
type GeConj =
    | GeConj of ArithExpr list
    member x.ToProposition () =
        let (GeConj lst) = x in
        let mapper a = Atom (true, Compare (CmpGe, a, AConst NUMERIC_ZERO)) in
        And $ List.map mapper lst
    override x.ToString () =
        let (GeConj lst) = x in
        String.concat " and " $ List.map (fun x -> $"{x}>=0") lst
    interface IVariableCollectable with
        member this.CollectVars () =
            let (GeConj lst) = this in
            Set.unionMany $ List.map collectVars lst
        

/// a confirmation of loss -- add this to hint that there is a loss here
type LossConfirm = LossConfirm

/// MAY HAVE ACCURACY LOSS
/// SHOULD CONFIRM THE LOSS HERE
let cmpToArithExprList (LossConfirm) (op, a1, a2) =
    match op with
    | CmpEq -> [ AOperation (OpMinus, [a1; a2])
                 AOperation (OpMinus, [a2; a1]) ]
    | CmpNeq -> failwith "Neq is not expressible in out prop."
    | CmpGe -> [ AOperation (OpMinus, [a1; a2]) ]
    | CmpGt -> [ AOperation (OpMinus, [a1; a2]) ]
    | CmpLe -> [ AOperation (OpMinus, [a2; a1]) ]
    | CmpLt -> [ AOperation (OpMinus, [a2; a1]) ]

/// pure conversion, no optimisation
let dnfPropToGeConj confirm dnf =
    match dnf with
    | DNFTrue      -> [ GeConj [] ]
    | DNFFalse     -> [ GeConj [AConst $ Numeric (-1)] ]
    | DNFProps set ->
        Set.toList set
        |> List.map (fun andLst ->
            Set.toList andLst
            |> List.map (cmpToArithExprList confirm)
            |> List.concat
            |> GeConj)
    
let conjCmpsToGeConj confirm (ConjCmps lst) =
    List.map (cmpToArithExprList confirm) lst
    |> List.concat
    |> GeConj
    
let disjToGeConjs confirm (DisjConjCmps lst) =
    List.map (conjCmpsToGeConj confirm) lst

let genBoundsConjCompsFromItemBoundMap itemBoundMap =
    let mapper (lhs, Range (lower, upper)) =
        [
            if unwrap lower <> BVInfty then
                // obj >/>= lower
                let (lower, hasEq) = (unwrap lower).ExtractFiniteInfo in
                ((if hasEq then CmpGe else CmpGt),
                 lhs,
                 AConst lower)
            
            if unwrap upper <> BVInfty then
                // obj </<= upper
                let (upper, hasEq) = (unwrap upper).ExtractFiniteInfo in
                ((if hasEq then CmpLe else CmpLt),
                 lhs,
                 AConst upper)
        ]
    Seq.map mapper itemBoundMap
    |> Seq.concat
    |> List.ofSeq
    
#nowarn "58"
module Decomposition = begin

let private simplifyConsistent (revMap : _ []) lst =
    List.map (BiMap.sndMap (Array.get revMap)) lst
    |> List.map backToCmp
    |> ConjCmps
    |> collectTightRanges
    |> Option.map genBoundsConjCompsFromItemBoundMap

let decomposePropToExclusiveConjCmps (proposition : Proposition<Compare>) =
    let map = AutoIdxMap<StdCmp> () in
    let mapper (isPos, cmp) =
        let cmp = if isPos then cmp else negateCompare cmp in
        match compareToStdCmps cmp with
        | [ x ], _ -> Atom (true, map.LookUp x)
        | [ x; y ], true ->
            And [
                Atom (true, map.LookUp x)
                Atom (true, map.LookUp y)
            ]
        | [ x; y ], false ->
            Or [
                Atom (true, map.LookUp x)
                Atom (true, map.LookUp y)
            ]
        | _ -> IMPOSSIBLE ()
    in
    let toResolve = Proposition<_>.MapAtom proposition mapper in
    let revMap =
        Seq.map swap map.GetRaw
        |> Array.ofSeq
        |> Array.sortBy fst
        |> Array.map snd
    in
    toNnf toResolve
    |> propToNnfProp
    |> nnfPropToDNF
    |> function
    | DNFTrue -> trueDisj
    | DNFFalse -> falseDisj
    | DNFProps set ->
        toMutuallyExclusive set
        |> Set.map Set.toList
        |> Set.toList
        |> List.choose (simplifyConsistent revMap)
        |> List.map ConjCmps
        |> DisjConjCmps

//type ValWithInfty =
//    | NegInfty
//    | Number of Numeric * hasEq:bool
//    | PosInfty
//
///// (c <= obj) < (c < obj)
//let lowerLe (l1 : ValWithInfty) l2 =
//    match l1, l2 with
//    | Number (c1, t1), Number (c2, t2) when c1 = c2 -> t2 <= t1  // REVERSE
//    | _ -> l1 <= l2
//let upperLe u1 u2 = u1 <= u2
///// whether there is a period, so if they are the same, Le holds ONLY when
//let isNonVoidPeriod l u =
//    match l, u with
//    | Number (c1, t1), Number (c2, t2) when c1 = c2 -> t1 && t2
//    | _ -> l <= u
///// if there is a gap -- if there is a possible value between the two
///// up: upper bound of the previous (lower) range
///// ln: lower bound of the next (higher) range
//let hasGapBetween up ln =
//    match up, ln with
//    | Number (c1, t1), Number (c2, t2) when c1 = c2 -> not t1 && not t2
//    | _ -> up < ln
//
//let private convertLowerBound l =
//    match l with
//    | None -> NegInfty
//    | Some (v, hasEq) -> Number (v, hasEq)
//let private convertUpperBound u =
//    match u with
//    | None -> PosInfty
//    | Some (v, hasEq) -> Number (v, hasEq)
//let private convertRange (l, u) =
//    (convertLowerBound l, convertUpperBound u)
//let private backToRange (vl, vu) =
//    match vl, vu with
//    | PosInfty, _ | _, NegInfty -> failwith "INTERNAL ERROR: impossible range."
//    | NegInfty, PosInfty -> (None, None)
//    | NegInfty, Number (c, hasEq) -> (None, Some (c, hasEq))
//    | Number (c, than), PosInfty -> (Some (c, than), None)
//    | Number (l, t_l), Number (u, t_u) -> (Some (l, t_l), Some (u, t_u))

let private hasGapBetween (UpperBound up) (LowerBound ln) =
    match up, ln with
    | BVFinite (c1, t1), BVFinite (c2, t2) when c1 = c2 -> not t1 && not t2
    | _ -> up < ln


let mergeRange (Range (l1, _) as r1) (Range (l2, _) as r2) =
    let Range (l1, u1), Range (l2, u2) =
        if l1 <= l2 then (r1, r2) else (r2, r1) in
    if hasGapBetween u1 l2 then None
    elif u2 <= u1 then Some $ Range (l1, u1)
    else Some $ Range (l1, u2)
    
/// try match the ranges
/// returns: the matched rangeMap
let private matchRanges
        (range1 : HashMap<_,_>)
        (range2 : HashMap<_,_>) : HashMap<_,_> option =
    let len1, len2 = HashMap.size range1, HashMap.size range2 in
    let isDifferentFrom el (key, v) =
        match HashMap.tryFind key el with
        | Some v' -> if v = v' then None
                     else Some (key, v, v')
        | None -> None
    in
    // bs: base, el: else
    /// if all the elements in `bs` are in and have the same value as in `el`
    let (>-) bs el =
        Seq.tryPick (isDifferentFrom el) bs
        |> Option.isNone
    in
    match abs $ len1 - len2 with
    | 0 ->
        // they have the same key set length
        // so, just find the one with difference
        match Seq.tryPick (isDifferentFrom range2) range1 with
        | None -> Some range1
        | Some (key, v1, v2) ->
            match mergeRange v1 v2 with
            | Some newRange ->
                // if the two can be merged, update them in both `range1` and `range2`
                HashMap.add key newRange range1;
                HashMap.add key newRange range2;
                // then, now they should be the same, otherwise, they cannot be merged
                if range1 >- range2 then Some range1 else None
            | None -> None
    | 1 ->
        // there is exactly ONE element that is outStanding
        // so, elements inside should all be the same for the shorter rangeMap in the longer
        // and then, just erase this element is OK -- so, just return the shorter rangeMap
        // if there is difference in the elements in the shorter, it means they cannot match
        let shorter, longer = if len1 <= len2 then range1, range2 else range2, range1 in
        // check whether elements in `shorter` are all contained and the same as in `longer`
        if shorter >- longer then Some shorter else None
    | _ -> None  // otherwise, they cannot match -- the difference between elements must > 1

/// two are mergeable iff:
/// every term has the same range with at most one with different ranges 
let tryMergeTwo conj1 conj2 =
    let range1 = (collectTightRanges conj1).Value in
    let range2 = (collectTightRanges conj2).Value in
    matchRanges range1 range2
    |> Option.map (genBoundsConjCompsFromItemBoundMap >> ConjCmps)

/// unify the term ranges as more as possible
/// for example, (t - h > 1 /\ t - h < 2) \/ (t - h = 1) will be unified as (t - h >= 1 /\ t - h < 2)
/// the key is to:
/// 1. collect the (normalised) term range information
/// 2. if all ranges of the variables can be merged, then merge the two
///
/// For a list of items, the algorithms goes by:
/// take out the head, merge as more as possible the rest of the list
/// for the merged head, there will be no more element possible to merge in the rest
/// for the rest of the list that are not possible to merge the first, perform the above
/// until the rest of the list that cannot merge with all of the previous merged elements is empty
/// Finally, loop until the result has only one element or does not reduce any more
let tryMerge canMergeTwo lst =
    if List.length lst <= 1 then lst else
    let rec mergeOneByOne merged lst =
        match lst with
        | [] -> merged, []
        | hd :: lst -> match tryMergeTwo merged hd with
                       | Some merged when canMergeTwo merged ->
                           mergeOneByOne merged lst
                       | _ -> let merged, lst = mergeOneByOne merged lst in
                              merged, hd :: lst
    in
    let rec recMerge lst =
        match lst with
        | [] -> []
        | hd :: lst -> let result, lst = mergeOneByOne hd lst in
                       result :: recMerge lst
    in
    // loop until recMerge does not reduce any more
    let rec loop lst =
        match lst with
        | [] -> IMPOSSIBLE ()
        | [ _ ] -> lst
        | lst -> let nextLst = recMerge lst in
                 if nextLst.Length < lst.Length then loop nextLst else nextLst
    in
    loop lst

end
#warnon "58"
    
let conjCmpsToCompareProp (ConjCmps lst) =
    match List.map (Compare >> atomise) lst with
    | [] -> True
    | [ x ] -> x
    | lst -> And lst

let mkQueryCtx () =
    { allVars = None
      varRange = Map.empty
      specialVarTypes = Map.empty
      atomParse = nodeToCompareProp }
    
let tryMergeWithConditions canMerge conjCmps =
    Decomposition.tryMerge canMerge conjCmps
    
let inline tryMergeConjCmps conjCmps =
    tryMergeWithConditions (constFunc true) conjCmps
    
let decomposePropToValidExclusiveConjCmps (proposition : Proposition<Compare>) =
    Decomposition.decomposePropToExclusiveConjCmps proposition
    |> unwrap
    |> List.filter (fun cmps ->
        checkSAT (mkQueryCtx ()) [ conjCmpsToCompareProp cmps ])
    // DEBUG: such unification may lead to error
//    // finally, try to unify as much as possible the final result
//    |> Decomposition.tryMerge
    
//let inline decomposePropToValidExclusiveConjCmps prop =
//    decomposePropToValidExclusiveConjCmps_full true prop

type Location =
    | LOne
    | LNegOne
    | LZero
    | LNegTen
    override x.ToString () =
        match x with
        | LOne -> "1"
        | LNegOne -> "-1"
        | LZero -> "0"
        | LNegTen -> "-10"

/// should collect the conjunction of comparison list --
/// ONE STEP before the GeConj, in order to preserve the original form as well as also trivial to
/// convert to GeConj
type NextLocInfo =
    | NLSingle of Location * ConjCmps
    | NLJoin of totalGuard:ConjCmps *
                //            [ trueLoc , [ randVar ,   lower   ,   upper  ] ]
                concreteRange:(Location * (Variable * ArithExpr * ArithExpr) list) list

let assnWeakestPrecondition assnPair prop =
    substPropositionVars prop $ uncurry Map.add assnPair Map.empty

/// compute the weakest precondition for an assignment list
let assnPathWp path prop =
    List.foldBack assnWeakestPrecondition path prop

//let rec simplifyArithExpr aExpr =
//    match aExpr with
//    | AVar _ | AConst _ -> aExpr
//    | AOperation (op, lst) ->
//        match List.map simplifyArithExpr lst with
//        | [] -> AOperation (op, [])
//        | [ x ] ->
//            match op with
//            | OpMinus ->
//                match x with
//                | AConst c -> AConst (-c)
//                | _ -> AOperation (OpMinus, [ x ])
//            | _ -> x
//        | lst ->
//            let combine initC cOp =
//                let backFolder v (c, acc) =
//                    match v with
//                    | AConst c' -> (cOp c c', acc)
//                    | _ -> (c, v :: acc)
//                in
//                let c, acc = List.foldBack backFolder lst (initC, []) in
//                if c = initC then acc
//                else AConst c :: acc
//            in
//            match op with
//            | OpAdd ->
//                match combine NUMERIC_ZERO (+) with
//                | [] -> AOperation (OpAdd, [])
//                | [ x ] -> x
//                | lst ->
//                    let collectMinus
//            | OpMul ->
//                match combine NUMERIC_ONE (*) with
//                | [] -> AOperation (OpMul, [])
//                | [ x ] -> x
//                | lst -> AOperation (OpMul, lst)
//            | OpMinus ->
//                let head, rest = List.head lst, List.tail lst in
//                AOperation (OpMinus, head :: combine NUMERIC_ZERO (+))
//            | OpDiv ->
//                let head, rest = List.head lst, List.tail lst in
//                AOperation (OpDiv, head :: combine NUMERIC_ONE (*))
                

/// simplification method:
///     1) remove the constant items, if has constantly negative value, return None
///     2) c + P /\ c' + P -> c'' + P, where c'' = min c c'
/// if P is empty, then it will find the smaller negative value, which is also OK
let simplifyGeConj (GeConj lst) =
    /// c + P -> (P, c)
    let extractConst (Polynomial poly) =
        match poly with
        | (c, []) :: poly -> (Polynomial poly, c)
        | _ -> (Polynomial poly, NUMERIC_ZERO)
    in
    /// (P, c) -> c + P
    let recoverConst (Polynomial poly, c) =
        if c = NUMERIC_ZERO then Polynomial poly
        else Polynomial $ (c, []) :: poly
    in
    let collectInternal collMap poly =
        let poly, c = extractConst poly in
        match Map.tryFind poly collMap with
        | Some c' -> Map.add poly (min c c') collMap
        | None    -> Map.add poly c collMap
    in
    // perform normalisation, make P unique and const be in the front
    let normLst = List.map arithExprToNormalisedPolynomial lst in
    let rec removeConstAndFindIfHasNegative lst =
        match lst with
        | [] -> []
        | (Polynomial [ (c, []) ]) :: lst when c >= NUMERIC_ZERO ->
            removeConstAndFindIfHasNegative lst
        | hd :: lst ->
            hd :: removeConstAndFindIfHasNegative lst
    in
    removeConstAndFindIfHasNegative normLst
    // collect information
    |> List.fold collectInternal Map.empty
    // extract collected information
    |> Map.toList
    |> List.map recoverConst
    |> List.map polynomialToArithExpr
    |> GeConj

/// normalise the arithmetic expression to a unique simplified form:
/// c + \sum_i c_i \prod_j v_{i, j}
let normaliseArithExpr (aExpr : ArithExpr) =
    arithExprToNormalisedPolynomial aExpr
    |> polynomialToArithExpr

/// c + \sum_i c_i \prod_j v_{i, j} ->
/// P_n * x^n + P_{n - 1} * x^{n - 1} + ... + P_1 * x + P_0 ->
/// { n |-> P_n }
let polynomialToXFormula targetVar (Polynomial lst) : Map<uint, Polynomial> =
    let collectPn map (c, vars) =
        let collectRestAndXCount (otherVars, xCount) newVar =
            if newVar = targetVar then (otherVars, xCount + 1u)
            else (newVar :: otherVars, xCount)
        in
        let vars, xCount = List.fold collectRestAndXCount ([], 0u) vars in
        let newPoly = Polynomial [(c, vars)] in  // newPoly = c * vars
        Map.change xCount (Some << function
            | Some item -> item + newPoly
            | None      -> newPoly) map
    in
    List.fold collectPn Map.empty lst

/// returns: (possible lower list, possible upper list)
let extractUpperAndLowerBounds targetVar (ConjCmps lst) :
        (ArithExpr * bool) list * (ArithExpr * bool) list =
    /// c * r >/>= d, value = d / c
    let judgeLowerOrUpper hasEq c (value : ArithExpr) (lower, upper) =
        let value = (value, hasEq) in
        // c * x >= d
        match compare c NUMERIC_ZERO with
        // c > 0 -> x >= d / c
        | x when x > 0 -> (value :: lower, upper)
        // c = 0 -> irrelevant to x
        | 0 -> (lower, upper)
        // c < 0 -> x <= d / c
        | x when x < 0 -> (lower, value :: upper)
        | _ -> IMPOSSIBLE ()
    in
    let folder (lower, upper) cmpTriple =
        let (StdCmp (lhs, rhs, mayEq)) =
            Compare cmpTriple
            |> compareToStdCmps
            |> fst
            |> List.exactlyOne
        in
        polynomialToXFormula targetVar lhs
        |> Map.toList
        |> List.sortBy fst
        |> function
        | [] -> failwith "Empty Expression."
        | [ (0u, _) ] -> (lower, upper)  // irrelevant to this variable
        | [ (1u, Polynomial [ (num, []) ] ) ] ->
            // c * r >/>= rhs
            judgeLowerOrUpper mayEq num (AConst (rhs / num)) (lower, upper)
        | [ (0u, p0); (1u, p1) ] ->
            // p1 * r + p0 >/>= rhs
            let (Polynomial lst) = p1 in
            let lst = List.filter (fst >> fun x -> x <> NUMERIC_ZERO) lst in
            match lst with
            | [ (c, lst) ] ->
                // c * vs * r >/>= rhs - p0  (`vs` is `lst`)
                // ==>
                // vs * r ~ (rhs - p0)/c
                let rhs = AOperation (OpMinus, [
                    AConst (rhs / c)
                    polynomialToArithExpr (p0 / c)
                ]) in
                // TODO: Resolve Assumption:
                //      this method is UNSOUND -- the variable inside is not checked
                //      here assume all VARS >= 0
                // divide the variables
                // r ~ (rhs - p0)/c/vs
                let rhs =
                    match lst with
                    | [] -> rhs
                    | _  -> AOperation (OpDiv, rhs :: List.map AVar lst)
                in
                judgeLowerOrUpper mayEq c rhs (lower, upper)
            | [] -> (lower, upper)  // irrelevant to this variable
            | _ -> failwith "Currently Support Only One Item in List."
        | _ -> failwith "Currently Support Only Linear Expression."
    in
    List.fold folder ([], []) lst
    
let checkConjCmpListSAT (ConjCmps lst) =
    let props = List.map (Compare >> atomise) lst in
    checkSAT (mkQueryCtx ()) props
    
/// convert to GeConj and then filter out those invalid `OR` part
let propToValidGeConj confirm prop =
    let lst = decomposePropToValidExclusiveConjCmps prop in
    List.filter checkConjCmpListSAT lst
    |> List.map (conjCmpsToGeConj confirm)
    
/// decompose the proposition to a list of semantically disjunctive clauses
/// which are formally (and also semantically) exclusive
/// also, all of them will pass the SAT check to make sure possibility
let propToValidConjCmpList toMerge prop =
    if not $ checkSAT (mkQueryCtx ()) [ prop ] then [] else
//    let lst =
    decomposePropToValidExclusiveConjCmps prop
    |> if toMerge then tryMergeConjCmps else id
//    in
//    List.filter (fun (ConjCmps lst) ->
//        checkSAT (mkQueryCtx ()) $ List.map (Compare >> atomise) lst) lst
    
//let conjGeConj (GeConj l1) (GeConj l2) = GeConj (l1 ++ l2)

type PathDivisionArgs = {
    path : (Variable * ArithExpr) list
    /// the fixed content when the path is executed
    /// but it may not necessarily hold after the execution
    /// so this part will not take part in the weakestPrecondition computation
    /// for example, the loop invariant is part of this -- although it will not bother the result
    /// even if it is placed into loopGuard
    /// however, the segment guard must be placed here
    fixedGuard : Proposition<Compare>
    loopGuard : Proposition<Compare>
    mayEndIfScoreGuard : Proposition<Compare> option
    randVarRanges : Map<Variable, Numeric * Numeric>
    takeZeroShortcut : bool
}

let rec smoothNegatives prop =
    match prop with
    | True | False | Atom (true, _) -> prop
    | Atom (false, cmp) -> Atom (true, negateCompare cmp)
    | And lst -> And $ List.map smoothNegatives lst
    | Or lst -> Or $ List.map smoothNegatives lst
    | Not _ | Implies _ -> IMPOSSIBLE ()  // after simplification, there should not be such

let simplifyConjCmps conjCmps =
    normaliseConjCmps conjCmps
    |> collectTightRanges
    |> Option.map (genBoundsConjCompsFromItemBoundMap >> ConjCmps)

/// Will Combine the result
let private simplifyCmpProp toMerge prop =
    propToValidConjCmpList toMerge prop
    |> List.map conjCmpsToCompareProp
    |> function
    | [] -> False
    | [ x ] -> x
    | lst -> Or lst
//    let rec smoothNegatives prop =
//        match prop with
//        | True | False | Atom (true, _) -> prop
//        | Atom (false, cmp) -> Atom (true, negateCompare cmp)
//        | And lst -> And $ List.map smoothNegatives lst
//        | Or lst -> Or $ List.map smoothNegatives lst
//        | Not _ | Implies _ -> IMPOSSIBLE ()  // after simplification, there should not be such
//    in
//    simplifyProposition prop
//    |> smoothNegatives

/// A General Division -- no additional assumption required
/// a divided State-Monad-like unit
/// a path of significance in the context is essentially just a list of update statements
/// g_\ell
/// g_s
/// the random variable map with (lower, upper)
type private PathDivisionImpl(input) =
    // basic information as input
    let path = input.path
    // DEBUG: handle the case generally
    let loopGuard = input.loopGuard
    let mayEndIfScoreGuard = input.mayEndIfScoreGuard
    let randVarRanges = input.randVarRanges
    let shortcut = input.takeZeroShortcut
    /// the loop guard must also be in the fixed guard condition --
    /// this is because before the execution, the path must also satisfy the loop guard
    let fixedGuard = And [ input.fixedGuard; loopGuard ]
    
    // pre-computed weakest preconditions
    /// wp(g_l)
    let wpLoopGuard = assnPathWp path loopGuard
    let randVars = Set.ofSeq $ Map.keys randVarRanges
    
    let wp(prop) = assnPathWp path prop
    
    /// g_f /\ wp(g_l)
    /// OR
    /// g_f /\ wp(g_l /\ g_s) if has g_s and shortcut
    let oneLocCondition =
        lazy
        simplifyCmpProp true $
        match mayEndIfScoreGuard with  // if needed and requires shortcut
        | Some endScoreGuard when shortcut ->
            And [ fixedGuard  // g_f
                  wp(And [ loopGuard; endScoreGuard ]) ]  // wp(g_l /\ g_s)
        | _ -> And [ fixedGuard; wpLoopGuard ]  // g_f /\ wp(g_l)
    /// g_f /\ wp(~g_l)
    let negOneLocCondition =
        lazy
        simplifyCmpProp true $
        And [ fixedGuard; wp(Not loopGuard) ]
    /// g_f /\ wp(~g_s) if shortcut
    /// g_f /\ wp(~g_l /\ ~g_s) if NO shortcut
    let zeroLocCondition =
        lazy
        simplifyCmpProp true $
        let endScoreGuard = mayEndIfScoreGuard.Value in
        if shortcut then And [ fixedGuard; wp(Not endScoreGuard) ]
        else And [ fixedGuard; wp(And [
            Not loopGuard
            Not endScoreGuard
        ]) ]
    /// g_f /\ wp(~g_l /\ g_s)
    let negTenLocCondition =
        lazy
        simplifyCmpProp true $
        let endScoreGuard = mayEndIfScoreGuard.Value in
        And [
            fixedGuard
            wp(And [
                Not loopGuard
                endScoreGuard
            ])
        ]

    /// the return value can be consider to be a Seq from map
    /// which means the variable is unique
    let getInvolvedRandVarRanges randVarRanges proposition =
        collectPropositionVars proposition
        |> Set.toList
        |> List.choose (fun var ->
            Map.tryFind var randVarRanges
            |> Option.map (fun (l, u) -> (var, (l, u))))

    let genRandVarRangesProp randVarRanges =
        flip List.map randVarRanges (fun (var, (lower, upper)) ->
            [
                atomise $ Compare (CmpGe, AVar var, AConst lower)
                atomise $ Compare (CmpLe, AVar var, AConst upper)
            ])
        |> List.concat
        |> And
    
    /// given target
    /// automatically fill the information about random variables
    /// Input: `target`
    /// Output: quantifier eliminated result for `forall rvs. Range(rvs) -> target`
    let qeForallTarget target =
        let varRanges = getInvolvedRandVarRanges randVarRanges target in
        match varRanges with
        | [] -> target
        | _  ->
            let ranges = genRandVarRangesProp varRanges in
            // if in this rv range, it is False, then, no need to perform QE further
            if not $ checkSAT (mkQueryCtx ()) [ target; ranges ] then False else
            let forall = Forall (List.map fst varRanges, Implies (ranges, target)) in
            let qeCtx = mkQueryCtx () in
            let ret = quantifierElimination qeCtx [ forall ] in
            if checkSAT (mkQueryCtx ()) [ ret ] then ret else False
    
    // helper functions to generate the stuff
    // convert the requirement to be more general and tackle with module `Logic`
    // for all single cases, one can merge
    let initOneLocGuards = lazy simplifyCmpProp true (qeForallTarget oneLocCondition.Value)
    let initNegOneLocGuards = lazy simplifyCmpProp true (qeForallTarget negOneLocCondition.Value)
    let initZeroLocGuards = lazy simplifyCmpProp true (qeForallTarget zeroLocCondition.Value)
    let initNegTenLocGuards = lazy simplifyCmpProp true (qeForallTarget negTenLocCondition.Value)
    
    /// location guard is the guard that EXCLUSIVELY leads to this location
    let findInitLocGuard loc =
        match loc with
        | LOne -> initOneLocGuards.Value
        | LNegOne -> initNegOneLocGuards.Value
        | LZero -> initZeroLocGuards.Value
        | LNegTen -> initNegTenLocGuards.Value
    
    let findGuardsForLoc loc =
        let initLocGuard = findInitLocGuard loc in
        if not $ checkSAT (mkQueryCtx ()) [ initLocGuard ] then [] else 
        let lst = decomposePropToValidExclusiveConjCmps $ findInitLocGuard loc in
        List.filter (fun (ConjCmps lst) ->
            checkSAT (mkQueryCtx ()) $ List.map (Compare >> atomise) lst) lst
    
    let genSingle loc =
        let guards = findGuardsForLoc loc in
        List.map (fun guard -> NLSingle (loc, guard)) guards
    
//    let analyseGuardRandVarConds conjCmps op =
//        // firstly normalise the guard to get better guard to analyse
//        let op = simplifyGeConj op in
//        // then find all the random variables and then find upper and lower bounds
//        // assume that there is at most ONE found upper and lower bound except the given one
//        Set.intersect (collectVars op) randVars
//        |> Set.toList
//        |> List.map (fun var ->
//            let varRangeProp = genRandVarRangesProp [ (var, Map.find var randVarRanges) ] in
//            let getBound isLower bounds =
//                let folder (cst, sym) newEl =
//                    match combineConst newEl with
//                    | AConst c ->
//                        match cst with
//                        | None -> (Some c, sym)
//                        | Some c' -> (Some (if isLower then max c c' else min c c'), sym)
//                    | a ->
//                        match sym with
//                        | None -> (cst, Some a)
//                        | Some ori ->
//                            let gt = Atom (true, Compare (CmpGt, a, ori)) in
//                            let lt = Atom (true, Compare (CmpLt, a, ori)) in
//                            let canGt =
//                                checkSAT (mkQueryCtx ()) [
//                                    gt
//                                    conjCmpsToCompareProp conjCmps
//                                    varRangeProp
//                                ]
//                            in
//                            let canLt =
//                                checkSAT (mkQueryCtx ()) [
//                                    lt
//                                    conjCmpsToCompareProp conjCmps
//                                    varRangeProp
//                                ]
//                            in
//                            if canGt && canLt then
//                                failwith "Currently support only ONE symbolic bound.";
//                            if canGt then
//                                 if isLower then (cst, Some ori) else (cst, Some a)
//                            else if isLower then (cst, Some a) else (cst, Some ori)
//                in
//                match List.fold folder (None, None) bounds with
//                | (_, Some bound) -> bound
//                | (Some c, _) -> AConst c
//                | (None, None) -> IMPOSSIBLE ()
//            in
//            let dfLower, dfUpper = Map.find var randVarRanges in
//            let lower, upper = extractUpperAndLowerBounds var op in
//            let lower = getBound true (AConst dfLower :: lower) in
//            let upper = getBound false (AConst dfUpper :: upper) in
//            (var, lower, upper))
    
    let analyseGuardRandVarConds conjCmps =
        // firstly normalise the guard to get better guard to analyse
        let conjCmps = simplifyConjCmps conjCmps in
        if Option.isNone conjCmps then [] else
        let conjCmps = Option.get conjCmps in
        // then find all the random variables and then find upper and lower bounds
        // assume that there is at most ONE found upper and lower bound except the given one
        Set.intersect (collectVars conjCmps) randVars
        |> Set.toList
        |> List.map (fun var ->
            (var, extractUpperAndLowerBounds var conjCmps))
    
    let getLocCondition loc =
        match loc with
        | LOne -> oneLocCondition.Value
        | LNegOne -> negOneLocCondition.Value
        | LZero -> zeroLocCondition.Value
        | LNegTen -> negTenLocCondition.Value
    
//    let getRandVarRanges randVars =
//        Seq.map (flip Map.find randVarRanges) randVars
//        |> Seq.zip randVars
//        |> Map.ofSeq
    
//    let collectCmpVars (_, a1, a2) =
//        Set.union
//            (collectArithExprVars a1)
//            (collectArithExprVars a2)
    
//    let getConjCmpsInvolvedRandVars (ConjCmps lst) =
//        List.map collectCmpVars lst
//        |> Set.unionMany
//        |> Set.intersect randVars
        
    let rangeRandVars =
        Map.toList randVarRanges
        |> genRandVarRangesProp
    
    let conjCmpsToProp (ConjCmps lst) =
        match List.map (Compare >> atomise) lst with
        | [] -> True
        | [ x ] -> x
        | lst -> And lst
    
    let rec arithContainsRandVar aExpr =
        match aExpr with
        | AVar v -> randVars.Contains v
        | AConst _ -> false
        | AOperation (_, lst) -> List.exists arithContainsRandVar lst
    
    /// 1. should remove those impossible by the range of rand vars
    /// 2. should remove the meaningless bound-generating items -- those already implied
    ///
    /// Hence, returns: [(full condition, rand var condition)]
    let genValidRandVarConditions basicGuard loc =
        let condition = getLocCondition loc in
        let lst =
            decomposePropToValidExclusiveConjCmps $ And [
                conjCmpsToProp basicGuard
                condition
            ]
        in
        flip List.choose lst $ fun (ConjCmps lst as ccl) ->
            let possible =
                checkSAT (mkQueryCtx ()) [
                    // use all the ranges, should be faster than finding those required
                    // as the number of rand vars is usually small
                    rangeRandVars
                    conjCmpsToProp ccl
                ]
            in
            if not possible then None else
            // take out the boundary conditions to check whether they're implied
            // removed those implied -- will provide meaningless bounds
            /// partition by whether relevant to the random variables
            let parByRel (_, a1, a2) =
                arithContainsRandVar a1 || arithContainsRandVar a2
            in
            let rel, irr = List.partition parByRel lst in
            /// Range(rs) /\ irr
            let rangeAndIrr = And $ rangeRandVars :: List.map (Compare >> atomise) irr in
            let meaningfulRel =
                flip List.filter rel $ fun cmp ->
                    // if SAT, then ~forall x. (Range(rs) /\ irr -> cmp)
                    // so it provides new information, hence meaningful
                    checkSAT (mkQueryCtx ()) [
                        // ~ forall x. (Range(rs) /\ irr -> cmp)
                        // =>
                        // exists x. ~ (Range(rs) /\ irr -> cmp)
                        Not $ Implies (rangeAndIrr, atomise $ Compare cmp)
                    ]
            in
            match meaningfulRel with
            | [] -> None
            | rel -> Some (ConjCmps $ rel ++ irr, ConjCmps rel)  // take it out to benefit finding
    
    let isConst = function AConst _ -> true | _ -> false
    
    let combineConditions (((lower, lEq as l), lCond), ((upper, uEq as u), uCond)) =
        let newCmp = ConjCmps [
                if not (isConst lower || isConst upper) then
                    let comparator =
                        match lEq, uEq with
                        | true, true -> CmpLe
                        | _, _       -> CmpLt
                    in
                    (comparator, lower, upper)
            ] in
        (l, u, newCmp + lCond + uCond)
    
    /// given that r ~ bv1 && r ~ bv2 where if `isLower` then ~ is >/>= otherwise ~ is </<=
    /// returns the list of which to take and also the required condition
    let getConditions isLower ((bv1, eq1 as p1), (bv2, eq2 as p2)) =
        if isLower then
            match eq1, eq2 with
            | true, false ->
                // r >= bv1 && r > bv2
                // so, to take: r >= bv1, it must be: bv1 > bv2
                // and to take: r > bv2, it should be: bv1 <= bv2
                [
                    (p1, ConjCmps [ (CmpGt, bv1, bv2) ])
                    (p2, ConjCmps [ (CmpLe, bv1, bv2) ])
                ]
            | _, _ ->
                [
                    (p1, ConjCmps [ (CmpGe, bv1, bv2) ])
                    (p2, ConjCmps [ (CmpLt, bv1, bv2) ])
                ]
        else
            match eq1, eq2 with
            | false, true ->
                // r < bv1 && r <= bv2
                // so, to take: r <= bv2, it must be: bv1 > bv2
                // and to take: r < bv1, it should be: bv1 <= bv2
                [
                    (p2, ConjCmps [ (CmpGt, bv1, bv2) ])
                    (p1, ConjCmps [ (CmpLe, bv1, bv2) ])
                ]
            | _, _ ->
                [
                    (p2, ConjCmps [ (CmpGe, bv1, bv2) ])
                    (p1, ConjCmps [ (CmpLt, bv1, bv2) ])
                ]
    
    let boundWithConditions isLower dfl bounds =
        match bounds with
        | [] -> [ ((AConst dfl, true), ConjCmps []) ]
        | [ x ] -> [ (x, ConjCmps []) ]
        | lst ->
            enumEveryN 2 lst
            |> List.map (function [ x; y ] -> (x, y) | _ -> IMPOSSIBLE ())
            |> List.collect (getConditions isLower)
    
    /// for this variable, returns the list of lower bound, upper bound and also the condition for this bound
    let getConditionalVarBounds (var, (lowers, uppers)) =
        let dflLower, dflUpper = Map.find var randVarRanges in
        let lowerWithConditions = boundWithConditions true dflLower lowers in
        let upperWithConditions = boundWithConditions false dflUpper uppers in
        List.allPairs
            lowerWithConditions
            upperWithConditions
        |> List.map combineConditions
        |> List.map (fun e -> (var, e))
    
    let combineBetweenVarsConds basicConds varRangesWithConds =
        let repose (var, (lower, upper, cond)) =
            ((var, lower, upper), cond)
        in
        let varRanges, totalCond =
            List.map repose varRangesWithConds
            |> List.unzip
            |> BiMap.sndMap (List.fold (+) (ConjCmps []))
        in
        if checkConjCmpListSAT (basicConds + totalCond) then Some (varRanges, totalCond) else None
    
    let divMultiBoundConditions condRelList =
        let divider (cond, relCond) =
            // DEBUG: revise the guard analysis method -- DO NOT USE CONJ-GE, keep the full guard
//            let relConjGe = conjCmpsToGeConj LossConfirm relCond in
            let varBounds = analyseGuardRandVarConds relCond in
            let condVarBounds = List.map getConditionalVarBounds varBounds in
            listCartesian condVarBounds
            |> List.choose (combineBetweenVarsConds cond)
            // DEBUG: SHOULD NOT ADD ORIGINAL CONDITION
            // the current condition is the guard condition, which is as expected
//            |> List.map (BiMap.sndMap (fun x -> x + cond))
//            |> List.filter (snd >> checkConjCmpListSAT)
        in
        List.collect divider condRelList
    
//    /// the `basicGuard` is for checking whether the information can be satisfied
//    let genLocJoin (ConjCmps _ as cc) locType =
//        if locType = LZero then [] else
//        genRandVarConditions cc locType
////        |> List.filter (fst >> fun (ConjCmps lst) ->
////            checkSAT (mkQueryCtx ()) $
////                List.map (Compare >> atomise) (lst ++ bLst))
//        |> List.map snd
//        |> List.map (fun lst -> (locType, lst))
    
    let basicJoinCondition locTypes =
        let findAndMkNot loc = Not $ findInitLocGuard loc in
        And $ fixedGuard :: List.map findAndMkNot locTypes
    
//    let discriminativeCondition locTypes =
//        let basicCondition = basicJoinCondition locTypes in
//        List.map getLocCondition locTypes
//        |> enumEveryN 2
//        |> List.map (And >> Not)
//        |> curry List.Cons basicCondition
//        |> And
    
    /// given two conjCmps from TWO DIFFERENT GUARDS
    /// returns 3 propositions:
    /// 1. the random var overlapping condition and their ranges
    /// 2. the first non-rand-var condition
    /// 3. the second non-rand-var condition
    let chooseOverlapRandVarRanges (ConjCmps l1) (ConjCmps l2) =
        let hasRandVar cmp =
            Set.exists (flip Set.contains randVars) $ collectVars cmp
        in
        let r1, l1 = List.partition (Compare >> hasRandVar) l1 in
        let r2, l2 = List.partition (Compare >> hasRandVar) l2 in
        if r1 = [] || r2 = [] then None else
        // see if in the proper ranges, the two are overlapping with each other
        let rsProp = conjCmpsToProp $ ConjCmps (r1 ++ r2) in
        let rvProp =
            getInvolvedRandVarRanges randVarRanges rsProp
            |> genRandVarRangesProp
        in
        let noRangeCoincidence =
            not $ checkSAT (mkQueryCtx ()) [ rsProp; rvProp ]
        in
        if noRangeCoincidence then None else
        // DEBUG: no need and cannot check if [l1; l2] holds simultaneously
        // this is because these guards will NEVER hold together
        // but the key is about checking whether the range can determine solely l1 or l2
        Some (And [ rsProp; rvProp ],
              conjCmpsToProp $ ConjCmps l1,
              conjCmpsToProp $ ConjCmps l2)
    
    let genRandOverlapsFromTwoLocConds pair =
        BiMap.bothMap (propToValidConjCmpList true) pair
        |> uncurry List.allPairs
        |> List.choose (uncurry chooseOverlapRandVarRanges)
    
    let randOverlaps locTypes =
        List.map getLocCondition locTypes
        |> enumEveryN 2
        |> List.map (function [ x; y ] -> (x, y) | _ -> IMPOSSIBLE ())
        |> List.collect genRandOverlapsFromTwoLocConds
    
    /// generate the guards that are not mergeable due to the discriminative reason
    let genNonMergeableGuards locTypes =
        let randOverlaps = randOverlaps locTypes in
        let checkIfStillValid mergedGuard =
            let mergedGuard = conjCmpsToProp mergedGuard in
            let cannotDistinguish (randVarProp, nonProp1, nonProp2) =
                // if all are SAT, then such locGuard will produce a problem
                flip List.forall [ randVarProp; nonProp1; nonProp2 ] $ fun prop ->
                    checkSAT (mkQueryCtx ()) [ mergedGuard; prop ]
            in
            not $ List.exists cannotDistinguish randOverlaps
        in
        basicJoinCondition locTypes
        |> propToValidConjCmpList false
        |> tryMergeWithConditions checkIfStillValid
    
    /// generate the location guards
    /// returns: [(loc, localGuard, varRanges)]
    let genLocJoinInfo basicProp loc =
        if loc = LZero then [] else
        genValidRandVarConditions basicProp loc
        |> divMultiBoundConditions
        |> List.map (fun (varRanges, localGuard) ->
            let varRanges = List.map ((fun (v, (l, _), (u, _)) -> (v, l, u))) varRanges in
            (loc, localGuard, varRanges))
    
    let chooseCompatibleJoinInfo bp lst =
        if lst = [] then None else
        let repose (l, prop, varRanges) = (prop, (l, varRanges)) in
        let totalCondList, info = List.unzip $ List.map repose lst in
        let totalCond = List.fold (+) (ConjCmps []) totalCondList in
        let prop = totalCond + bp in
        if checkConjCmpListSAT prop then Some $ NLJoin (prop, info) else None
    
    /// check whether Join should be generated, if so, pass the job to `PureGenJoin`
    member private x.GenJoin locTypes =
        // should find the NON-LOSS guards and make Not
        let basicProps =
            match locTypes with
            | [] | [ _ ] -> IMPOSSIBLE ()
            | [ _; _ ] ->
                // for only two of them, one can merge
                propToValidConjCmpList true $ basicJoinCondition locTypes
            | _ -> genNonMergeableGuards locTypes
        in
        let mayGenSomeJoins bp =
            // returns:
            // a list of Join items for EACH location
            // which is: [(loc, localGuard, varRanges)] where localGuard is compatible with `bp`
            List.map (genLocJoinInfo bp) locTypes
            |> listMayCartesian
            |> List.map (List.choose id)
            |> List.choose (chooseCompatibleJoinInfo bp)
        in
        List.collect mayGenSomeJoins basicProps
    
    member x.BasicDivisionAnalysis () =
        [
            match mayEndIfScoreGuard with
            | None ->
                // analyse 1 and -1
                genSingle LOne
                genSingle LNegOne
                x.GenJoin [ LOne; LNegOne ]
            | Some _ ->
                // analyse 1, 0 and -10
                genSingle LOne
                genSingle LZero
                genSingle LNegTen
                x.GenJoin [ LOne; LZero; LNegTen ]
        ]
        |> List.concat

let pathDivisionAnalysis arg =
    let analyser = PathDivisionImpl arg in
    analyser.BasicDivisionAnalysis ()

let rec boolExprToProposition (bExpr : BoolExpr) =
    let rec collectAndLevel bExpr =
        match bExpr with
        | BAnd (b1, b2) -> collectAndLevel b1 ++ collectAndLevel b2
        | _ -> [ bExpr ]
    in
    match bExpr with
    | BTrue -> True
    | BFalse -> False
    | BAnd _ -> And $ List.map boolExprToProposition (collectAndLevel bExpr)
    | BCompare (op, a1, a2) -> atomise $ Compare (op, a1, a2)
