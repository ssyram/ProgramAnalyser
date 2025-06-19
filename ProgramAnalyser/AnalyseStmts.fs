module ProgramAnalyser.AnalyseStmts

(*
    This module contains the priliminary analysis of the statements in a non-nested loop.
    The given statement list, representing non-loopy contents, either in a non-nested loop or in a non-loop context,
    is converted to a list of CFG edges, each with its own path condition and discrete numeric probability.

    Ultimately, a `CfgEdge` is a tuple of:
    - the updates of program variables
    - the list of scoring happening on the edge
    - the probability of the edge
    - the total path condition of the edge, namely, the condition that must hold for the edge to be taken to execute

    The only public function is `stmtsToCfgEdges`, which conducts the above analysis.
*)

open ParserSupport
open Objects
open Utils
open Global
open Logic
open Polynomial

/// The edge of the control flow graph, which is a tuple of:
/// - the updates of program variables, the orders does not matter,
///   as given a mapping `v |-> e` all RHS variables in `e` are the *former* values BEFORE the edge is executed,
///   and the LHS variables `v` are the *new* values AFTER the edge is executed
/// - the probability of the edge
/// - the path condition of the edge, namely, the condition that must hold for the edge to be taken to execute,
///   the variables in the condition are the *former* values BEFORE the edge is executed
/// - the list of scores that are accumulated on the edge
type CfgEdge = { update: Map<Variable, ArithExpr>
                 prob: ArithExpr
                 guard: Proposition<Compare>
                 scores: ArithExpr list
                 /// This is important, as if `isBreak` then it must get out of the loop
                 isBreak: bool }
with
    override x.ToString () =
        let updateStr = Map.toList x.update |> List.map (fun (v, e) -> $"{v}:={e}") |> String.concat ", "
        let probStr = $"prob: {x.prob}"
        let guardStr = $"guard: {x.guard}"
        let scoresStr = String.concat "*" (List.map (fun e -> $"({e})") x.scores)
        let breakStr = if x.isBreak then "BREAK" else "no-break"
        $"CfgEdge({updateStr}, {probStr}, {guardStr}, {scoresStr}, {breakStr})"

/// the statements that are to appear on the edge
type private EdgeStatement =
    | ESAssign of Variable * ArithExpr
    | ESScore of ArithExpr
    | ESBreak
    | ESCond of BoolExpr
    | ESProb of ArithExpr
    override x.ToString () =
        match x with
        | ESAssign (var, expr) -> $"{var}:={expr}"
        | ESScore expr -> $"score({expr})"
        | ESBreak -> "break"
        | ESCond guard -> $"assume[{guard}]"
        | ESProb prob -> $"prob({prob})"

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
                cond, appendNode (statementsToTree statements) rest)
        | STIfProb (prob, lT, lF) ->
            [ prob, lT;
              AOperation (OpMinus, [AConst (Numeric 1); prob]), lF ]
            |> List.map (fun (prob, statements) ->
                prob, appendNode (statementsToTree statements) rest)
            |> NProb

let rec simplyBoolExpr bExpr =
    match bExpr with
    | BAnd (b1, b2) ->
        match simplyBoolExpr b1, simplyBoolExpr b2 with
        | b1, BTrue -> b1
        | BTrue, b2 -> b2
        | BFalse, _ -> BFalse
        | _, BFalse -> BFalse
        | b1, b2 -> BAnd (b1, b2)
    | _ -> bExpr

/// This is just a helper type for psudo-edges
/// It is not used in the final output
type private Edge = Edge of EdgeStatement list

let rec private nodeToEdges node : Edge list =
    let addToEdges e ess =
        List.map (fun (Edge ess) -> Edge (e :: ess)) ess
    in
    let addToEdgesFromNode e node =
        nodeToEdges node
        |> addToEdges e
    in
    match node with
    | NEnd -> [ Edge [] ]
    | NNormal (es, next) -> addToEdgesFromNode es next
    | NProb lst ->
        let mapper (prob, next) = addToEdgesFromNode (ESProb prob) next in
        List.concat $ List.map mapper lst
    | NIf lst ->
        let mapper (guard, next) =
            addToEdgesFromNode (ESCond (simplyBoolExpr guard)) next
        in
        List.concat $ List.map mapper lst

exception BreakMark of CfgEdge

/// To perform the `wp` computation along the edge, that is, each variable is along every update
/// Returns also a map of updated variables to their expressions, which is the ultimate result of the update
/// Namely, for each item `v |-> e` in the map, it means that `v` is ultimately updated to `e` after executing the edge
let private edgeToCfgEdge (Edge ess) =
    // helper constructs
    let (|->) v e = Map.add v e Map.empty in
    let updateMap v e (map: Map<Variable,ArithExpr>) =
        let e' = substVars e map in
        Map.add v e' map
    in
    let updateExpr e map = substVars e map in
    let initCfgEdge: CfgEdge =
        { update = Map.empty
          prob = AConst NUMERIC_ONE
          guard = True
          scores = []
          isBreak = false } in

    let folder cfgEdge es =
        let map = cfgEdge.update in
        match es with
        | ESAssign (var, expr) -> { cfgEdge with update = updateMap var expr map }
        | ESScore expr -> { cfgEdge with scores = updateExpr expr map :: cfgEdge.scores }
        // it should always be the last item in the edge after the cut
        // so no need to stop the computation here as there will be no more statements behind
        | ESBreak -> { cfgEdge with isBreak = true }
        | ESCond guard -> { cfgEdge with guard = And [ cfgEdge.guard; boolExprToProposition $ updateExpr guard map ] }
        | ESProb prob ->
            { cfgEdge with prob = AOperation (OpMul, [cfgEdge.prob; updateExpr prob map]) }
    in
    List.fold folder initCfgEdge ess

let private cutOnBreak (edge : Edge) =
    let rec cut acc edge =
        match edge with
        | Edge [] -> Edge (List.rev acc)
        | Edge (ESBreak :: _) -> Edge (List.rev (ESBreak :: acc))
        | Edge (es :: rest) -> cut (es :: acc) (Edge rest)
    in
    cut [] edge

/// The interface of this file, which converts a list of statements to a list of CFG edges
/// Namely, from a non-loop context, it enumerates all the possible paths from this context
let stmtsToCfgEdges (statements: Statement list) : CfgEdge list =
    // convert the statements to a tree structure
    statementsToTree statements
    // convert the tree structure to edges
    |> nodeToEdges
    |> List.map cutOnBreak
    |> List.distinct
    // convert the edges to CfgEdge
    |> List.map edgeToCfgEdge
