module ProgramAnalyser.Polynomial

open System
open Global
open Objects
open ProgramAnalyser.Logic
open ProgramAnalyser.Logic.Parser
open ProgramAnalyser.Objects
open ProgramAnalyser.Utils
open ProgramAnalyser.Utils.NormPolynomial

/// the true polynomial to represent
type Polynomial =
    Polynomial of (Numeric * Variable list) list
    with
    interface IUnwrappable<(Numeric * Variable list) list> with
        member x.Unwrap () = match x with | Polynomial poly -> poly
    /// divide the constant
    static member (/) (Polynomial p, c) =
        Polynomial $ List.map (BiMap.fstMap (fun x -> x / c)) p
    /// to add two polynomials is simply by concatenate the internal list
    /// NO NORMALISATION WILL BE PERFORMED
    static member (+) (Polynomial p1, Polynomial p2) = Polynomial $ p1 ++ p2
    /// make sure the uniqueness of the whole element
    /// make sure the representation is c + \sum_i c_i \prod_j v_{i, j}, where for all `i`
    /// there is at least one `j` for v_{i, j}
    /// Also, for each `i`, the set of possible variable in `j` is in a fixed order
    static member FromNormalisedExpr (NormalisedExpr map) : Polynomial =
        let rec addCountUnit count unit lst =
            if count = 0u then lst else addCountUnit (count - 1u) unit (unit :: lst)
        in
        // accumulate the result, find the head const
        let folder (lst, maybeHeadConst) (varCounts, c) =
            let varsLst = List.fold
                              (fun lst (var, count) -> addCountUnit count var lst)
                              []
                              varCounts in
            match varsLst with
            | [] -> match maybeHeadConst with
                    | Some _ -> failwith "Polynomial Normalisation Error: multiple constant from normalised expr."
                    | None   -> (lst, Some c)
            | _ -> ((c, varsLst) :: lst, maybeHeadConst)
        in
        Map.toList map
        |> List.map (BiMap.fstMap (Map.toList >> List.sortBy fst))
        |> List.sortBy fst
        |> List.fold folder ([], None)
        |> function
           | lst, None   -> Polynomial lst
           | lst, Some c -> Polynomial $ (c, []) :: lst
    
let rec combineConst (aExpr : ArithExpr) =
    match aExpr with
    | AVar _ | AConst _ -> aExpr
    | AOperation (_, lst) when lst = [] -> aExpr 
    | AOperation (op, lst) ->
        let lst = List.map combineConst lst in
        let isConst = function AConst _ -> true | _ -> false in
        let getConst = function AConst c -> c | _ -> IMPOSSIBLE () in
        if not $ List.forall isConst lst then AOperation (op, lst) else
        let lst = List.map getConst lst in
        match op with
        | OpAdd -> AConst $ List.sum lst
        | OpMul -> AConst $ List.reduce (*) lst
        | OpMinus ->
            // DEBUG: in minus, when there is ONLY ONE element, it is to negate the value
            match lst with
            | [] -> IMPOSSIBLE ()
            | [ x ] -> AConst (-x)
            | _ -> let hd, rest = List.head lst, List.tail lst in
                   AConst $ hd - List.sum rest
        | OpDiv ->
            let hd, rest = List.head lst, List.tail lst in
            AConst $ hd / List.fold (*) NUMERIC_ONE rest
    
let arithExprToNormalisedPolynomial (aExpr : ArithExpr) : Polynomial =
    combineConst aExpr
    |> toExprEnv
    |> normaliseExprEnv
    |> fromNormalisedExpr
    
let polynomialToArithExpr (Polynomial lst) =
    let backFindPosAndNeg (c, vars) (pos, neg) =
        let placeTerm term =
            if c > NUMERIC_ZERO then (term :: pos, neg)
            elif c < NUMERIC_ZERO then (pos, term :: neg)
            else (pos, neg)
        in
        match vars with
        | [] -> placeTerm $ AConst (abs c)
        | vars ->
            if abs c = NUMERIC_ONE then
                match vars with
                | [ x ] -> placeTerm $ AVar x
                | _ -> placeTerm $ AOperation (OpMul, List.map AVar vars)
            else
                placeTerm $ AOperation (OpMul, AConst (abs c) :: List.map AVar vars)
    in
    let (pos, neg) = List.foldBack backFindPosAndNeg lst ([], []) in
    match pos with
    | [] ->
        combineConst $
        match neg with
        | [] -> AConst NUMERIC_ZERO  // nothing to add together, then 0
        | hd :: tl ->
            let negHead = AOperation (OpMinus, [ hd ]) in  // -hd
            match tl with
            | [] -> negHead
            | tl -> AOperation (OpMinus, negHead :: tl)  // (-neg1) - neg2 - ... - neg_n)
    | pos ->
        let posPart =
            match pos with
            | [] -> IMPOSSIBLE ()  // this part is covered above
            | [ x ] -> x
            | lst -> AOperation (OpAdd, lst)
        in
        match neg with
        | [] -> posPart
        | _  -> AOperation (OpMinus, posPart :: neg)

type Compare = Compare of Comparator * ArithExpr * ArithExpr
    with
    override x.ToString () = let (Compare (op, a1, a2)) = x in $"{a1} {op} {a2}"
    interface IUnwrappable<Comparator * ArithExpr * ArithExpr> with
        member this.Unwrap () = let (Compare (op, a1, a2)) = this in (op, a1, a2)
    interface ILispPrintable with
        member this.LispPrint() =
            let (Compare (op, a1, a2)) = this in
            $"({lispPrint op} {lispPrint a1} {lispPrint a2})"
    interface IVariableCollectable with
        member this.CollectVars() =
            let (Compare (_, a1, a2)) = this in
            Set.union (collectVars a1) (collectVars a2)
    interface IVarSubstitutable<ArithExpr, Compare> with
        member this.SubstituteVar map =
            let (Compare (op, a1, a2)) = this in
            Compare (op, substVars a1 map, substVars a2 map)

let negateCompare (Compare (op, a1, a2)) = Compare (op.Negate, a1, a2)

let nodeToCompare (node : Node) =
    match node with
    | NFunc (name, children) ->
        match name with
        | "<=" | ">=" | "<" | ">" | "=" | "distinct" ->
            match children with
            | [left; right] ->
                let cmp = match name with
                          | "<=" -> CmpLe
                          | ">=" -> CmpGe
                          | "<" -> CmpLt
                          | ">" -> CmpGt
                          | "=" -> CmpEq
                          | "distinct" -> CmpNeq
                          | _ -> failwith "Invalid comparator"
                Compare (cmp, nodeToArithExpr left, nodeToArithExpr right)
            | _ -> failwith "Invalid comparison expression"
        | _ -> failwith "Invalid proposition name"
    | _ -> failwith "Unknown comparison"

let inline nodeToCompareProp node =
    Atom (true, nodeToCompare node)

/// conjunctive comparative list:
/// a1 ~1 a1' /\ a2 ~2 a2' /\ ... an ~n an'  // ~i is comparator
type ConjCmps = ConjCmps of (Comparator * ArithExpr * ArithExpr) list
    with
    override x.ToString () =
        let (ConjCmps lst) = x in
        List.map (fun (op, a1, a2) -> $"{a1} {op} {a2}") lst
        |> String.concat " /\ "
    static member (+) ((ConjCmps l1), (ConjCmps l2)) = ConjCmps (l1 ++ l2)
    interface IUnwrappable<(Comparator * ArithExpr * ArithExpr) list> with
        member this.Unwrap () = let (ConjCmps lst) = this in lst
    interface IVariableCollectable with
        member this.CollectVars () =
            unwrap this
            |> List.map (Compare >> collectVars)
            |> Set.unionMany
    
    
/// disjunctive list of possible conjunctions
/// empty list is the same as `False`
type DisjConjCmps = DisjConjCmps of ConjCmps list
    with
    interface IUnwrappable<ConjCmps list> with
        member this.Unwrap () = let (DisjConjCmps lst) = this in lst
    
let trueDisj = DisjConjCmps [ ConjCmps [] ]
let falseDisj = DisjConjCmps []
    
open Logic.DisjunctiveNormal
    
let dnfToCmpList dnf =
    match dnf with
    | DNFTrue -> trueDisj
    | DNFFalse -> falseDisj
    | DNFProps sets ->
        Set.toList sets
        |> List.map (Set.toList >>
                     List.map (fun (isPos, (Compare (op, a1, a2))) ->
                         if isPos then (op, a1, a2) else (op.Negate, a1, a2)) >>
                     ConjCmps)
        |> DisjConjCmps
type BoundVal =
    | BVInfty
    | BVFinite of boundVal:Numeric * hasEq:bool
    member x.ExtractFiniteInfo =
        match x with
        | BVFinite (boundVal, hasEq) -> boundVal, hasEq
        | _ -> failwith "The value is infinite."
[<CustomComparison>]
[<CustomEquality>]
type LowerBound = LowerBound of BoundVal
    with
    override this.GetHashCode () =
        match unwrap this with
        | BVInfty -> hash -1
        | BVFinite (boundVal, hasEq) -> hash (boundVal, hasEq)
    override this.Equals obj =
        match obj with
        | :? LowerBound as that -> unwrap this = unwrap that
        | _ -> false
    interface IComparable with
        member this.CompareTo obj =
            match obj with
            | :? LowerBound as that ->
                match unwrap this, unwrap that with
                | BVInfty, BVInfty -> 0
                | BVInfty, _ -> -1
                | _, BVInfty -> 1
                | BVFinite (v1, eq1), BVFinite (v2, eq2) ->
                    match compare v1 v2 with
                    | 0 -> if eq1 = eq2 then 0 elif eq1 then -1 else 1
                    | v -> v
            | _ -> failwith "Comparing a LowerBound with other types."
    interface IUnwrappable<BoundVal> with
        member this.Unwrap () = let (LowerBound bv) = this in bv
    override this.ToString () =
        let bv = unwrap this in
        match bv with
        | BVInfty -> "- oo"
        | BVFinite (boundVal, hasEq) -> 
            toString boundVal + " " + if hasEq then "<=" else "<"
[<CustomComparison>]
[<CustomEquality>]
type UpperBound = UpperBound of BoundVal
    with
    override this.GetHashCode () =
        match unwrap this with
        | BVInfty -> hash -1
        | BVFinite (boundVal, hasEq) -> hash (boundVal, hasEq)
    override this.Equals obj =
        match obj with
        | :? UpperBound as that -> unwrap this = unwrap that
        | _ -> false
    interface IComparable with
        member this.CompareTo obj =
            match obj with
            | :? UpperBound as that ->
                match unwrap this, unwrap that with
                | BVInfty, BVInfty -> 0
                | BVInfty, _ -> 1
                | _, BVInfty -> -1
                | BVFinite (v1, eq1), BVFinite (v2, eq2) ->
                    match compare v1 v2 with
                    | 0 -> if eq1 = eq2 then 0 elif eq1 then 1 else -1
                    | v -> v
            | _ -> failwith "Comparing an UpperBound with other types."
    interface IUnwrappable<BoundVal> with
        member this.Unwrap () = let (UpperBound bv) = this in bv
    override this.ToString () =
        let bv = unwrap this in
        match bv with
        | BVInfty -> "+ oo"
        | BVFinite (boundVal, hasEq) -> 
            toString boundVal + " " + if hasEq then ">=" else ">"
type Bound =
    | BLower of LowerBound
    | BUpper of UpperBound
    with
    interface IUnwrappable<BoundVal> with
        member this.Unwrap () =
            match this with
            | BLower lowerBound -> unwrap lowerBound
            | BUpper upperBound -> unwrap upperBound
type Range = Range of lower:LowerBound * upper:UpperBound
    with
    interface IUnwrappable<LowerBound * UpperBound> with
        member this.Unwrap () =
            let (Range (lower, upper)) = this in (lower, upper)
    override this.ToString () =
        let lbv, ubv = BiMap.pairMap (unwrap, unwrap) $ unwrap this in
        let lower =
            match lbv with
            | BVInfty -> "(- oo"
            | BVFinite (lb, lEq) -> if lEq then "[" else "(" + toString lb
        in
        let upper =
            match ubv with
            | BVInfty -> "+ oo)"
            | BVFinite (ub, uEq) -> toString ub + if uEq then "]" else ")"
        in
        $"{lower}, {upper}"

let nonVoidPeriod (Range (lower, upper)) =
    match lower, upper with
    | _, UpperBound BVInfty -> true
    | LowerBound BVInfty, _ -> true
    | LowerBound (BVFinite (lbv, lEq)), UpperBound (BVFinite (ubv, uEq)) ->
        // either l < u
        lbv < ubv ||
        // or l = u and l <= obj <= u so obj = l = u
        (lbv = ubv && lEq && uEq)

let unifyBound (Range (oriLower, oriUpper)) newBound : Range option =
    match newBound with
    | BLower newLower ->
        let newLowerLargerThanOriUpper =
            // obj </<= upper /\ boundVal </<= obj -> False
            // =>
            // boundVal > upper || boundVal = upper && ~(obj <= upper && obj >= lower)
            not $ nonVoidPeriod (Range (newLower, oriUpper))
        in
        let ret unifiedLower = Some $ Range (unifiedLower, oriUpper) in
        if newLowerLargerThanOriUpper then None else ret $ max oriLower newLower
//        match unwrap oriLower with
//        | BVInfty -> newLower
//        | BVFinite (oriVal, oriHasEq) ->
//            if oriVal < boundVal then (boundVal, hasEq)
//            elif oriVal = boundVal then (boundVal, hasEq && oriHasEq)
//            else (oriVal, oriHasEq)
    | BUpper newUpper ->
        let newUpperLessThanOriLower =
            not $ nonVoidPeriod (Range (oriLower, newUpper))
        in
        let ret unifiedUpper = Some $ Range (oriLower, unifiedUpper) in
        if newUpperLessThanOriLower then None else ret $ min oriUpper newUpper
            
/// returns: (isLower, hasEq)
let getOpProperty op =
    match op with
    | CmpLt -> false, false
    | CmpLe -> false, true
    | CmpGt -> true, false
    | CmpGe -> true, true
    | _ -> IMPOSSIBLE ()
    
let wrapOpToBound op rhsVal =
    let isLower, hasEq = getOpProperty op in
    BVFinite (rhsVal, hasEq)
    |> if isLower then BLower << LowerBound else BUpper << UpperBound

let wrapOpToNewRange op rhsVal =
    match wrapOpToBound op rhsVal with
    | BLower lower -> Range (lower, UpperBound BVInfty)
    | BUpper upper -> Range (LowerBound BVInfty, upper)
/// the standard comparison operation
/// LHS ~ RHS
/// where:
///     LHS is a polynomial without constant item
///     RHS is a constant value
///     ~ is either `>=` or `>`, `hasEq` denotes whether `=` is included
type StdCmp = StdCmp of lhs:Polynomial * rhs:Numeric * mayEq:bool

let stdCmpToCmp (StdCmp (lhs, rhs, mayEq)) =
    let rhs = AConst rhs in
    let lhs = polynomialToArithExpr lhs in
    if mayEq then Compare (CmpGe, lhs, rhs)
    else Compare (CmpGt, lhs, rhs)

/// returns: the converted comparison result to `StdCmp`
/// where the `bool` represents the relationship of content inside
/// `true` means: /\
/// `false` means: \/
let compareToStdCmps (Compare (op, a1, a2)) =
    let hasEq =
        match op with
        | CmpGe | CmpEq | CmpLe -> true
        | CmpGt | CmpNeq | CmpLt -> false
    in
    let aExprLst, isConj =
        match op with
        | CmpLe | CmpLt -> [ AOperation (OpMinus, [a2; a1]) ], true
        | CmpGe | CmpGt -> [ AOperation (OpMinus, [a1; a2]) ], true
        | CmpEq -> [ AOperation (OpMinus, [a2; a1])
                     AOperation (OpMinus, [a1; a2]) ], true
        | CmpNeq -> [ AOperation (OpMinus, [a2; a1])
                      AOperation (OpMinus, [a1; a2]) ], false
    in
    let toStdCmp aExpr =
        let lst, c =
            match unwrap $ arithExprToNormalisedPolynomial aExpr with
            | (c, []) :: lst -> (lst, -c)
            | lst -> (lst, NUMERIC_ZERO)
        in
        StdCmp (Polynomial lst, c, hasEq)
    in
    List.map toStdCmp aExprLst, isConj

let backToCmp (isPos, StdCmp (lhs, rhs, hasEq)) =
    let op = if hasEq then CmpGe else CmpGt in
    let op = if isPos then op else op.Negate in
    let lhs, op, rhs =
        match lhs with
        | Polynomial ((c, _) :: _) ->
            // normalise the head
            lhs / c, (if c < NUMERIC_ZERO then op.Reverse else op), rhs / c
        | _ -> lhs, op, rhs
    in
    (op, polynomialToArithExpr lhs, AConst rhs)

/// let every item be of form:
/// t ~ c
/// where `t` must be of positive form and is normalised
/// this is for `collectTightRanges`
let normaliseConjCmps (ConjCmps lst) =
    List.map Compare lst
    |> List.collect (fst << compareToStdCmps)
    |> List.map (curry backToCmp true)
    |> ConjCmps

/// Turn examples of the form:
/// P1 ~1 c1 /\ P2 ~2 c2 /\ ... /\ Pn ~n cn
/// where Pi is a term, ~i is the comparator and ci must be constant (AConst ci)
/// Then, find the tight range of each Pi -- will unify the range
///
/// WILL NOT test the form of Pi, it is just an auxiliary function
/// If there is inconsistency, for example: a > 0 /\ a < 0 then there is no range
/// Hence it returns `None` as the value -- indicating the contradiction within it
let collectTightRanges (ConjCmps lst) =
    let itemBoundMap = HashMap () in
    let addAndFindInConsistency (op, lhs, rhs) =
        let boundVal =
            match rhs with
            | AConst c -> c
            | _ -> IMPOSSIBLE ()
        in
        match HashMap.tryFind lhs itemBoundMap with
        | None ->
            let range = wrapOpToNewRange op boundVal in
            HashMap.add lhs range itemBoundMap;
            false
        | Some oldRange ->
            let bound = wrapOpToBound op boundVal in
            match unifyBound oldRange bound with
            | Some newRange -> HashMap.add lhs newRange itemBoundMap; false
            | None -> true
    in
    List.tryFind addAndFindInConsistency lst
    |> function
    | Some _ -> None
    | None -> Some itemBoundMap
