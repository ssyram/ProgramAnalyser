module ProgramAnalyser.Analysis

open Microsoft.FSharp.Collections
open Objects
open ProgramAnalyser.Global
open ProgramAnalyser.Logic
open ProgramAnalyser.Logic.DisjunctiveNormal
open ProgramAnalyser.Polynomial
open ProgramAnalyser.Utils

// This module introduces a systematic division of the given assn-path in a non-nested loop.
// It divides a path into a set of possible target locations and their corresponding conditions.
// For example, given a path like:
// [ X ::= X + r ]
// with `r` being a bounded random variable, in range [0.5, 1]
// and the loop guard: X < 10
// the division produces:
// [
//      Single: X < 9: InLoop
//      Joined: 9 <= X <= 9.5:
//         0.5 <= r < 10 - X: InLoop
//         10 - X <= r <= 1: OutLoop
//      Single: X > 9.5: OutLoop
// ]


// --------------------------------------------- Greater-or-Equal Conjunction ---------------------------------------------
// This part is the infrastructure of handling the basic greater-or-equal conjunctions
// This is the target output format of the propositions

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
        match lst with
        | [] -> "true"
        | _  -> String.concat " and " $ List.map (fun x -> $"{x}>=0") lst
    interface IVariableCollectable with
        member this.CollectVars () =
            let (GeConj lst) = this in
            Set.unionMany $ List.map collectVars lst
        

/// a confirmation of loss -- add this to hint that there is a loss here
type LossConfirm = LossConfirm

/// MAY HAVE ACCURACY LOSS </br>
/// SHOULD CONFIRM THE LOSS HERE
/// 
/// from `e1 ~ e2` to `E >= 0`, returns `E`.
/// This equation is exact if `e1` and `e2` are both integers.
/// Otherwise, when either `e1` or `e2` is a real number, the accuracy is lost when `e1 > e2` or `e1 < e2`.
/// When `e1 == e2`, it returns: `e1 - e2` *and* `e2 - e1` to prevent accuracy loss.
let cmpToArithExprList LossConfirm (op, a1, a2) =
    let isIntVar (Variable v) = Set.contains v Flags.INT_VARS in
    let rec isIntExpr a =
        match a with
        | AVar v -> isIntVar v
        | AConst c -> c.IsInt
        | AOperation (_, lst) -> List.forall isIntExpr lst
    in
    let exprs =
        match op with
        | CmpEq -> [ AOperation (OpMinus, [a1; a2])
                     AOperation (OpMinus, [a2; a1]) ]
        | CmpNeq -> failwith "Neq is not expressible in out prop."
        | CmpGe -> [ AOperation (OpMinus, [a1; a2]) ]
        | CmpGt -> [ AOperation (OpMinus, [a1; a2]) ]
        | CmpLe -> [ AOperation (OpMinus, [a2; a1]) ]
        | CmpLt -> [ AOperation (OpMinus, [a2; a1]) ]
    in
    match op with
    // for int expr `e`, `e > 0` == `e >= 1` == `e - 1 >= 0`
    | CmpGt | CmpLt when List.forall isIntExpr exprs ->
        List.map (fun e -> AOperation (OpMinus, e :: [AConst NUMERIC_ONE])) exprs
    // otherwise, simply returns `expr` as it is a `Real` expression
    | _ -> exprs

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
    

// ------------------------------------------------- Decomposition of Propositions ---------------------------------------------

// a generally helper module for decomposing the propositions
// used by functions below this module
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
    
// --------------------------------------------- Usage of module `Decomposition` ---------------------------------------------

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






// --------------------------------------------- Location and NextLocInfo ---------------------------------------------

type Location =
    | InLoop
    | OutLoop
    override x.ToString () =
        match x with
        | InLoop -> "InLoop"
        | OutLoop -> "OutLoop"

/// should collect the conjunction of comparison list --
/// ONE STEP before the GeConj, in order to preserve the original form as well as also trivial to
/// convert to GeConj
type NextLocInfo =
    | NLSingle of Location * ConjCmps
    | NLJoin of totalGuard:ConjCmps *
                //            [ trueLoc , [ randVar ,   lower   ,   upper  ] ]
                concreteRange:(Location * (Variable * ArithExpr * ArithExpr) list) list

                

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

/// normalise the arithmetic expression to a *unique* simplified form:
/// ```
/// c + \sum_i c_i \prod_j v_{i, j}
/// ```
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
    decomposePropToValidExclusiveConjCmps prop
    |> if toMerge then tryMergeConjCmps else id
    
/// given a set of updates, compute the weakest pre-condition of the given proposition
let wpOfProp updates prop =
    substPropositionVars prop updates

type PathDivisionArgs = {
    /// the updates that will be applied to the variables
    /// Notably, the update is *ATOMIC*, i.e., for each `v |-> e` within:
    /// - The variables in RHS `e` denotes the variables BEFORE the update
    /// - The variables in LHS `v` denotes the variables AFTER the update
    /// 
    /// There is no concept of ORDER in the updates.
    /// E.g., given updates: `{ X ::= X + 1; Y ::= X + 2 }`,
    /// then the `X` in `Y ::= X + 2` is the value of `X` before the update.
    /// 
    /// For example, if `X = 1 && Y = 2` before the update,
    /// then after the update, `X = 2 && Y = 3`;
    /// instead of `X = 2 && Y = 4`.
    updates : Map<Variable, ArithExpr>;
    /// The guard that must be satisfied before the execution of the updates, but are NOT required to hold after the updates.
    /// This will NOT be used for the `wp` computation.
    /// It essentially contains the conjunction of:
    /// 1) the loop invariant, and,
    /// 2) the path condition (also named segment guard) of the path behind the updates.
    fixedGuard : Proposition<Compare>;
    /// the loop guard that must be taken into account during `wp` computation
    loopGuard : Proposition<Compare>;
    /// The ranges of the random variables, used extensively in the computation
    randVarRanges : Map<Variable, Numeric * Numeric>;
}
let simplifyConjCmps conjCmps =
    normaliseConjCmps conjCmps
    |> collectTightRanges
    |> Option.map (genBoundsConjCompsFromItemBoundMap >> ConjCmps)

/// A General Division -- no additional assumption required
type private PathDivisionImpl(input) =
    // basic information as input
    let updates = input.updates
    // DEBUG: handle the case generally
    let loopGuard = input.loopGuard
    let randVarRanges = input.randVarRanges
    /// the loop guard must also be in the fixed guard condition --
    /// this is because before the execution, the path must also satisfy the loop guard
    let fixedGuard = And [ input.fixedGuard; loopGuard ]
    
    // pre-computed weakest preconditions
    /// wp(g_l)
    let wpLoopGuard = wpOfProp updates loopGuard
    let randVars = Set.ofSeq $ Map.keys randVarRanges
    
    let wp prop = wpOfProp updates prop

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
        |> function
        | [] -> True
        | x  -> And x
        
    let rangeRandVars =
        Map.toList randVarRanges
        |> genRandVarRangesProp
    
    let conjCmpsToProp (ConjCmps lst) =
        match List.map (Compare >> atomise) lst with
        | [] -> True
        | [ x ] -> x
        | lst -> And lst
    
    let isImplied baseCond hd =
        // forall x. Range(var) /\ baseCond -> hd
        // ==>
        // ~ exists x. ~ (Range(var) /\ baseCond -> hd)
        let preCond = And [
            rangeRandVars
            baseCond
        ] in
        not $ checkSAT (mkQueryCtx ()) [ Not $ Implies (preCond, hd) ]
    
    let rec removeImplied fixGuard (ConjCmps lst) =
        let isImplied restCond hd =
            // forall x. Range(var) /\ baseCond -> hd
            // ==>
            // ~ exists x. ~ (Range(var) /\ baseCond -> hd)
            let preCond = And [
                rangeRandVars
                conjCmpsToProp fixGuard
                conjCmpsToProp $ ConjCmps restCond
            ] in
            not $ checkSAT (mkQueryCtx ()) [ Not $ Implies (preCond, conjCmpsToProp $ ConjCmps [ hd ]) ]
        in
        let rec tryRemove pre lst =
            match lst with
            | [] -> pre
            | hd :: lst ->
                // see if `hd` is implied by both, if it is, remove it, otherwise, leave it
                if isImplied (pre ++ lst) hd then tryRemove pre lst
                else tryRemove (hd :: pre) lst
        in
        let next = tryRemove [] lst in
        if next.Length < lst.Length then removeImplied fixGuard (ConjCmps next) else ConjCmps next
    
    let simplifyCmpProp toMerge prop =
        propToValidConjCmpList toMerge prop
        |> List.map (removeImplied $ ConjCmps [])
        |> List.map conjCmpsToCompareProp
        |> function
        | [] -> False
        | [ x ] -> x
        | lst -> Or lst
    
    /// After the update, the result still satisfies the loop guard, hence the next execution remains in the loop
    /// g_f /\ wp(g_l)
    let inLoopCondition =
        lazy
        simplifyCmpProp true $ And [ fixedGuard; wpLoopGuard ]  // g_f /\ wp(g_l)
    /// After the update, the result goes out from the loop --- hence the loop guard is no longer satisfied
    /// g_f /\ wp(~g_l)
    let outLoopCondition =
        lazy
        simplifyCmpProp true $ And [ fixedGuard; wp(Not loopGuard) ]
    
    /// given a target, automatically fill the information about random variables,
    /// - Input: `target` proposition
    /// - Output: quantifier eliminated result for `forall rvs. Range(rvs) -> target`
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
    
    // NOTE: differences between *Condition* and *Guard*:
    // - Condition: the raw condition *with random variables*, two conditions may be compatible
    //   This compatibility stems from the random variables.
    // - Guard: the condition that is *free of random variables*, and must be incompatible with the other guard
    //   The `Guard` is used for Single location generation, as a guard *exclusively* leads to the location.
    // Guards are obtained by eliminating the random variables from the conditions.
    let inLoopGuards = lazy simplifyCmpProp true (qeForallTarget inLoopCondition.Value)
    let outLoopGuards = lazy simplifyCmpProp true (qeForallTarget outLoopCondition.Value)
    
    /// location guard is the guard that EXCLUSIVELY leads to this location
    /// REGARDLESS OF the values of the random variables (in the given ranges)
    let findInitLocGuard loc =
        match loc with
        | InLoop -> inLoopGuards.Value
        | OutLoop -> outLoopGuards.Value
    
    let findGuardsForLoc loc =
        let initLocGuard = findInitLocGuard loc in
        if not $ checkSAT (mkQueryCtx ()) [ initLocGuard ] then [] else 
        let lst = decomposePropToValidExclusiveConjCmps $ findInitLocGuard loc in
        List.filter (fun (ConjCmps lst) ->
            checkSAT (mkQueryCtx ()) $ List.map (Compare >> atomise) lst) lst
    
    let genSingle loc =
        let guards = findGuardsForLoc loc in
        List.map (fun guard -> NLSingle (loc, guard)) guards
    
    /// given a clause of the form "P1 ~1 c1' /\ ... /\ Pi ~i ci'"
    /// where Pi is an expression, ci is a constant and ~i is the comparator
    /// Then, to collect the bounds of each random variables involved
    ///
    /// The extraction is given simply by form turning, for example:
    /// if there is a Pi of the form x1 * r + x2 > 1
    /// then extracting a bound: r > (1 - x2)/x1 -- assuming all other variables inside are positive
    ///
    /// For a single random variable, there might be multiple such bounds extracted
    ///
    /// Returns: [(var, [lower-bound-expr], [upper-bound-expr])]
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
        | InLoop -> inLoopCondition.Value
        | OutLoop -> outLoopCondition.Value
    
    let rec arithContainsRandVar aExpr =
        match aExpr with
        | AVar v -> randVars.Contains v
        | AConst _ -> false
        | AOperation (_, lst) -> List.exists arithContainsRandVar lst
    
    /// 1. should remove those impossible by the range of rand vars
    /// 2. should remove the meaningless bound-generating items -- those already implied
    ///
    /// Hence, returns: `[(full condition, rand var condition)]`
    /// where rand-var-condition is *part of* the full-condition with rand-var inside
    /// A full condition is *one* clause in the disjunctive normal form of `basicGuard /\ locGuard`
    /// for the given `loc`
    ///
    /// This function's functionality:
    /// 1. get the full proposition as basicGuard /\ locGuard
    /// 2. use each clause of the disjunctive normal form of the proposition as full-condition
    /// 3. filter those conditions when they are not satisfiable
    /// 4. for those satisfiable clause, select the part with the random variables inside as the second element
    /// 5. if the second element is meaningless (implied), remove the whole item
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
    
    /// combine the lower and upper bound conditions
    /// add the new guarantee that the lower bound is less than or equal to the upper bound
    /// i.e., the bound is valid
    /// 
    /// Note: this function simply combines but does not check
    let combineConditions (((lower, lEq as l), lCond), ((upper, uEq as u), uCond)) =
        let newCmp = ConjCmps [
                // if not (isConst lower || isConst upper) then
                let comparator =
                    match lEq, uEq with
                    | true, true -> CmpLe
                    | _, _       -> CmpLt
                in
                comparator, lower, upper
            ] in
        l, u, newCmp + lCond + uCond
    
    let rec allWithCond isLower pre lst =
        // DEBUG: make it strict to let the whole division non-overlapping
        let distinguish isLower (tarVal, tarEq) (otrVal, otrEq) =
            if isLower then
                match tarEq, otrEq with
                | false, true ->
                    // r > tar && r >= other
                    // so, to take: r > tar, it can be: tar >= other
                    CmpGe, tarVal, otrVal
                | _, _ ->
                    // otherwise, tar > other
                    CmpGt, tarVal, otrVal
            else
                match tarEq, otrEq with
                | false, true ->
                    // r < tar && r <= other
                    // to take: r < tar, it can be: tar < other
                    CmpLe, tarVal, otrVal
                | _, _ ->
                    // otherwise, tar < other
                    CmpLt, tarVal, otrVal
        in
        match lst with
        | [] -> []
        | hd :: lst ->
            let other = pre ++ lst in
            let cond = ConjCmps $ List.map (distinguish isLower hd) other in
            (hd, cond) :: allWithCond isLower (hd :: pre) lst
    
    /// Arguments:
    /// - isLower: whether the bound is lower bound or upper bound
    /// - dfl: the default value for the bound, if no bound is given
    /// - bounds: the list of bounds `[(bound, isEq)]`
    /// 
    /// Returns: `[(bound, condition)]`
    /// where the condition means the selected bound is the tightest one
    /// Namely, when is a lower bound, the bound is the greatest among all the lower bounds
    /// and when is an upper bound, the bound is the least among all the upper bounds
    let boundWithConditions isLower dfl bounds =
        let bounds = (AConst dfl, true) :: bounds in
        match bounds with
        | [] -> IMPOSSIBLE ()
        | [ x ] -> [ (x, ConjCmps []) ]
        | lst ->
            allWithCond isLower [] lst
    
    /// for this variable, returns the list of lower bound, upper bound and also the condition for this bound
    ///
    /// The bound condition is, for a given `l \in Lowers`, `u \in Uppers`
    /// ```
    /// l </<= u /\ forall l' \in Lowers. l >/>= l' /\ forall u' \in Uppers. u </<= u'
    /// ```
    /// I.e., the bound condition ensures the bound given must be the *tightest* one
    /// 
    /// Notably, this is requiered as `l` and `u` are potentially *parametric* with *program* variables
    /// As the program variables change, the bounds may also change
    let getConditionalVarBounds (var, (lowers, uppers)) =
        let dflLower, dflUpper = Map.find var randVarRanges in
        let lowerWithConditions = boundWithConditions true dflLower lowers in
        let upperWithConditions = boundWithConditions false dflUpper uppers in
        List.allPairs
            lowerWithConditions
            upperWithConditions
        |> List.map combineConditions
        |> List.map (fun e -> var, e)
    
    /// return the part that does not contain random variables from the conjunction of comparisons
    let noRvPart (ConjCmps lst) =
        let noRv (_,a1,a2) = not (arithContainsRandVar a1 || arithContainsRandVar a2) in
        ConjCmps $ List.filter noRv lst
    
    let combineBetweenVarsConds basicConds varRangesWithConds =
        let repose (var, (lower, upper, cond)) =
            ((var, lower, upper), cond)
        in
        let varRanges, totalCond =
            List.map repose varRangesWithConds
            |> List.unzip
            |> BiMap.sndMap (List.fold (+) (ConjCmps []))
        in
        let totalCond = totalCond + basicConds in
        if checkConjCmpListSAT totalCond then Some (varRanges, totalCond) else None
    
    /// take out each comparison condition to examine whether it can be implied by the other conditions
    /// if it can, then remove it
    let filterImpliedConds cond (var, (upper, lower, conjCmps)) =
        var, (upper, lower, removeImplied cond conjCmps)
    
    /// Analyse the conditions that are related to the random variables
    /// Argument:
    /// - `condRelList`: a list of pairs of conditions and its random-variable-Related conditions (subset of the full condition)
    /// 
    /// Returns: `[([(var, lower, upper)], condition)]`
    /// 
    /// More specifically, for each pair `(cond, relCond)` in `condRelList`,
    /// it returns *a list of* pairs `([(var, lower, upper)], condition)` (i.e., NOT a one-to-one correspondence), where:
    /// the former part `[(var, lower, upper)]` is essentially equivalent to the `relCond` part, expressed in terms of
    /// the random variables and their ranges, and the latter part `condition` is the condition that must hold
    /// which is a combination of:
    /// - the original `cond` that is irrelevant to the random variables;
    /// - and the required conditions for the random variables to take the range.
    let divMultiBoundConditions condRelList =
        let divider (cond, relCond) =
            // DEBUG: the condition should be only the part without random variables
            let cond = noRvPart cond in
            // DEBUG: revise the guard analysis method -- DO NOT USE CONJ-GE, keep the full guard
//            let relConjGe = conjCmpsToGeConj LossConfirm relCond in
            let varBounds = analyseGuardRandVarConds relCond in
            let condVarBounds =
                List.map getConditionalVarBounds varBounds
                |> List.map (List.map (filterImpliedConds cond))
            in
            listCartesian condVarBounds
            |> List.choose (combineBetweenVarsConds cond)
            // DEBUG: SHOULD NOT ADD ORIGINAL CONDITION
            // the current condition is the guard condition, which is as expected
//            |> List.map (BiMap.sndMap (fun x -> x + cond))
//            |> List.filter (snd >> checkConjCmpListSAT)
        in
        List.collect divider condRelList
    
    
    let basicJoinCondition locTypes =
        let findAndMkNot loc = Not $ findInitLocGuard loc in
        And $ fixedGuard :: List.map findAndMkNot locTypes
    
    /// given two conjCmps from TWO DIFFERENT GUARDS of TWO DIFFERENT LOCATIONS
    /// returns 3 propositions:
    /// 1. the random var overlapping condition and their ranges
    /// 2. the first non-rand-var condition
    /// 3. the second non-rand-var condition
    /// 
    /// If the two conditions are not overlapping, then returns None
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
    
    /// generate the location guards analysis
    /// 
    /// Returns: `[(loc, localGuard, varRanges)]` where `loc` is the given location
    /// - The `localGuard` is the guard that should be satisfied to reach the location
    ///     it is the guard for the *program variables*;
    /// - and `varRanges` is the list of random variables with their ranges
    ///     it essentially encodes the guard for the *random variables*.
    /// 
    /// The real total guard to reach this location is the conjunction of `localGuard` and `varRanges`.
    let genLocJoinInfo basicProp loc =
        // generate the raw `[(totalCondition, randVarCondition)]` for the location
        genValidRandVarConditions basicProp loc
        // for each, analyse the random variable conditions and express them in terms of ranges
        // Also returns the part that does not contain random variables
        |> divMultiBoundConditions
        // re-organise the information and return
        |> List.map (fun (varRanges, localGuard) ->
            // throw away the equality information -- this is not needed for the conjCmps result
            // NOTE: potentially losing accuracy here.
            let varRanges = List.map (fun (v, (l, _), (u, _)) -> v, l, u) varRanges in
            loc, localGuard, varRanges)
    
    /// If the `lst` presents a list of compatible conditions, returns the joined information.
    /// Otherwise, returns None
    let chooseCompatibleJoinInfo bp lst =
        if lst = [] then None else
        let repose (l, prop, varRanges) = prop, (l, varRanges) in
        let totalCondList, info = List.unzip $ List.map repose lst in
        let totalCond = List.fold (+) (ConjCmps []) totalCondList in
        let prop = totalCond + bp in
        if checkConjCmpListSAT prop then Some $ NLJoin (prop, info) else None
    
    let allMentionedRandVars =
        Map.toList updates
        |> List.map (snd >> collectVars)
        // all vars
        |> Set.unionMany
        // only the random vars
        |> Set.intersect randVars
        |> Set.toList
    
    /// fill the information about the *random* variables that do not take part in separating the cases in Join
    /// Simply attach the primitive range of the random variables.
    /// Terminology `var` here refers exclusively to the random variables, NOT the program variables
    let attachIrrelevantVars nlInfo =
        let addIfNotIn relVars ret rv =
            if Set.contains rv relVars then ret
            else
                match Map.tryFind rv randVarRanges with
                | Some (lower, upper) -> (rv, AConst lower, AConst upper) :: ret
                | None -> failwith $"Random Variable \"{rv}\" has no range."
        in
        let addIrrVars varRanges =
            // set of all relevant random vars
            let relVars = Set.ofList $ List.map (fun (x,_,_) -> x) varRanges in
            varRanges
            // to maintain the order for comparison, non-essential, could be removed
            |> List.rev
            |> flip (List.fold (addIfNotIn relVars)) allMentionedRandVars
            // to maintain the order for comparison, non-essential, could be removed
            |> List.rev
        in
        let addIrrVars (loc, vars) = (loc, addIrrVars vars) in
        match nlInfo with
        | NLJoin (totalGuard, lst) -> NLJoin (totalGuard, List.map addIrrVars lst)
        // this should not be called as we are handling the join case now
        | NLSingle _ -> IMPOSSIBLE ()
    
    /// check whether Join should be generated, if so, pass the job to `PureGenJoin`
    member private _x.GenJoin locTypes =
        // should find the NON-LOSS guards and make Not
        let basicProps =
            match locTypes with
            | [] | [ _ ] -> IMPOSSIBLE ()
            | [ _; _ ] ->
                // for only two of them, one can merge
                propToValidConjCmpList true $ basicJoinCondition locTypes
            | _ -> propToValidConjCmpList true $ basicJoinCondition locTypes
        in
        let mayGenSomeJoins bp =
            // returns:
            // a list of Join items for EACH location
            // which is: [(loc, localGuard, varRanges)] where localGuard is compatible with `bp`
            List.map (genLocJoinInfo bp) locTypes
            |> listMayCartesian
            |> List.map (List.choose id)
            |> List.choose (chooseCompatibleJoinInfo bp)
            |> List.map attachIrrelevantVars
        in
        List.collect mayGenSomeJoins basicProps
    
    member x.BasicDivisionAnalysis () =
        [
            genSingle InLoop
            genSingle OutLoop
            x.GenJoin [ InLoop; OutLoop ]
        ]
        |> List.concat

/// The main entry point for path division analysis
let pathDivisionAnalysis (arg: PathDivisionArgs) =
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
