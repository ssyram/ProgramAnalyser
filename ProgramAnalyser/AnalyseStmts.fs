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
    | ESCond of Proposition<Compare>
    | ESProb of ArithExpr
    override x.ToString () =
        match x with
        | ESAssign (var, expr) -> $"{var}:={expr}"
        | ESScore expr -> $"score({expr})"
        | ESCond guard -> $"assume[{guard}]"
        | ESProb prob -> $"prob({prob})"

type private NodeStatement = NSAssn of Variable * ArithExpr | NSScore of ArithExpr | NSBreak

/// the supportive structure to help discover possible paths
type private Node =
    | NEnd
    | NNormal of NodeStatement * Node
    | NProb of (ArithExpr * Node) list
    | NIf of (Proposition<Compare> * Node) list

let rec private appendNode above below =
    match above with
    | NEnd -> below
    // stop right the way, no appending
    | NNormal (NSBreak, next) -> assert (next = NEnd); NNormal (NSBreak, NEnd)
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
        // stop right the way
        | STBreak -> NNormal (NSBreak, NEnd)
        | STAssn (var, expr) -> NNormal (NSAssn (var, expr), rest)
        | STInLoopScore expr -> NNormal (NSScore expr, rest)
        | STIfBool(b, t, f) ->
            let p = boolExprToProposition b in
            NIf [ p, appendNode (statementsToTree t) rest;
                  Not p, appendNode (statementsToTree f) rest ]
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
type private Edge = Edge of EdgeStatement list * isBreak:bool

let private nsToEs (ns: NodeStatement) =
    match ns with
    | NSAssn (var, expr) -> ESAssign (var, expr)
    | NSScore expr -> ESScore expr
    | NSBreak -> failwith "NSBreak should not be here, it is handled separately in the  `nodeToEdges` function"

let rec private nodeToEdges node : Edge list =
    let addToEdges e ess =
        List.map (fun (Edge (ess, b)) -> Edge (e :: ess, b)) ess
    in
    let addToEdgesFromNode e node =
        nodeToEdges node
        |> addToEdges e
    in
    match node with
    | NEnd -> [ Edge ([], false) ]
    | NNormal (NSBreak, next) ->
        assert (next = NEnd);
        [ Edge ([], true) ]
    | NNormal (es, next) -> addToEdgesFromNode (nsToEs es) next
    | NProb lst ->
        let mapper (prob, next) = addToEdgesFromNode (ESProb prob) next in
        List.concat $ List.map mapper lst
    | NIf lst ->
        let mapper (guard, next) =
            addToEdgesFromNode (ESCond guard) next
        in
        List.concat $ List.map mapper lst

/// To perform the `wp` computation along the edge, that is, each variable is along every update
/// Returns also a map of updated variables to their expressions, which is the ultimate result of the update
/// Namely, for each item `v |-> e` in the map, it means that `v` is ultimately updated to `e` after executing the edge
let private edgeToCfgEdge (Edge (ess, isBreak)) =
    // helper constructs
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
          isBreak = isBreak } in

    let folder cfgEdge es =
        let map = cfgEdge.update in
        match es with
        | ESAssign (var, expr) -> { cfgEdge with update = updateMap var expr map }
        | ESScore expr -> { cfgEdge with scores = updateExpr expr map :: cfgEdge.scores }
        // it should always be the last item in the edge after the cut
        // so no need to stop the computation here as there will be no more statements behind
        | ESCond guard -> { cfgEdge with guard = And [ cfgEdge.guard; substPropositionVars guard map ] }
        | ESProb prob ->
            { cfgEdge with prob = AOperation (OpMul, [cfgEdge.prob; updateExpr prob map]) }
    in
    List.fold folder initCfgEdge ess

/// The interface of this file, which converts a list of statements to a list of CFG edges
/// Namely, from a non-loop context, it enumerates all the possible paths from this context
let stmtsToCfgEdges (statements: Statement list) : CfgEdge list =
    // convert the statements to a tree structure
    statementsToTree statements
    // convert the tree structure to edges
    |> nodeToEdges
    |> List.distinct
    // convert the edges to CfgEdge
    |> List.map edgeToCfgEdge



// ----------------------------------------- Analyse as Guarded Groups -----------------------------------------

// In this part, we are instead analysing the statements as groups of guarded commands.
// A group of guarded commands is a set of commands that have probabilities add up to one with a specific guard.
// this can be considered as a probabilistic branching prepended by an assume statement.

type ProbCmd =
    { updates : Map<Variable, ArithExpr>
      scores: ArithExpr list
      prob: ArithExpr
      isBreak: bool }
    override x.ToString () =
        let updateStr = Map.toList x.updates |> List.map (fun (v, e) -> $"{v}:={e}") |> String.concat ", "
        let probStr = $"prob: {x.prob}"
        let scoresStr = String.concat "*" (List.map (fun e -> $"({e})") x.scores)
        let breakStr = if x.isBreak then "BREAK" else "no-break"
        $"updates:{updateStr}\nprob:{probStr}\nscores:{scoresStr}\n{breakStr}"
let private defaultProbUpdates =
    { updates = Map.empty
      scores = []
      prob = AConst NUMERIC_ONE
      isBreak = false }

type GrdCmdGroup<'p> =
    { guard: 'p
      cmds: ProbCmd list }
    override x.ToString () =
        let guardStr = $"guard: {x.guard}"
        let cmdsStr = String.concat "\n" (List.map (fun c -> $"  {c}") x.cmds)
        $"GrdCmdGroup:[{guardStr}]\n{cmdsStr}\nEndGroup"

type Prop = Proposition<Compare>
type PropGroup = GrdCmdGroup<Prop>

/// the singleton map
let private (|->) v e = Map.add v e Map.empty in
    
/// when the updates given are from behind, everything involving the variable should be updated
let private backwardUpdates (var, expr) updates =
    // let `var` be in `updates` and then update every RHS involving `var` to `expr`
    let updates =
        match Map.tryFind var updates with
        | Some _ -> updates
        | None -> Map.add var (AVar var) updates
    in
    // now update every RHS expression in the updates with `var` to `expr`
    Map.map (fun _ e -> substVars e (var |-> expr)) updates

/// add the update info to each command in the group, also note to update the guard -- as this is a backward update
let private fuseAssnToGroups var expr (group: PropGroup) =
    let substMap = var |-> expr in
    { group with
        guard = substPropositionVars group.guard substMap
        cmds = 
            List.map (fun x ->
                { x with
                    updates = backwardUpdates (var, expr) x.updates
                    scores = List.map (flip substVars substMap) x.scores
                    prob = substVars x.prob substMap })
                group.cmds }
/// add the score to each command in the group
let private fuseScoreToGroups expr (group: PropGroup) =
    { group with cmds = List.map (fun x -> { x with scores = expr :: x.scores }) group.cmds }
/// multiply the probability of each command in the group by the given probability
let private fuseProbToGroups prob (group: PropGroup) =
    { group with cmds = List.map (fun x -> { x with prob = AOperation (OpMul, [x.prob; prob]) }) group.cmds }
/// add the guard to each command in the group
let private fuseGuardToGroup guard (group: PropGroup) =
    { group with guard = And [ group.guard; guard ] }

/// if the joined guard is SAT, then combine the groups into one
let private tryCombineGroups (groups: PropGroup list) : PropGroup option =
    let joinedGuard = And $ List.map (fun g -> g.guard) groups in
    if checkSAT (mkQueryCtx ()) [ joinedGuard ] then
        Some { guard = joinedGuard; cmds = List.concat (List.map (fun g -> g.cmds) groups) }
    else None

let rec private nodeToGroups (node: Node) : PropGroup list =
    match node with
    | NEnd -> [  { guard = True; cmds = [ defaultProbUpdates ] } ]
    | NNormal (NSBreak, next) ->
        assert (next = NEnd);
        // this is a break, so we need to return a group with an empty guard
        [ { guard = True; cmds = [ { defaultProbUpdates with isBreak = true } ] } ]
    | NNormal (NSAssn (var, expr), next) ->
        nodeToGroups next
        |> List.map (fuseAssnToGroups var expr)
    | NNormal (NSScore expr, next) ->
        nodeToGroups next
        |> List.map (fuseScoreToGroups expr)
    | NProb lst ->
        List.map (BiMap.sndMap nodeToGroups) lst
        |> List.map (fun (p,gs) -> List.map (fuseProbToGroups p) gs)
        |> listCartesian
        |> List.choose tryCombineGroups
    | NIf lst ->
        List.map (BiMap.sndMap nodeToGroups) lst
        |> List.collect (fun (guard, gs) -> List.map (fuseGuardToGroup guard) gs)

let stmtsToGuardedCommandGroups (stmts : Statement list) : PropGroup list =
    statementsToTree stmts
    |> nodeToGroups
