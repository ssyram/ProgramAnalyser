module ProgramAnalyser.Logic

open System
open System.Text.RegularExpressions
open Microsoft.FSharp.Collections
open Microsoft.Z3
open ProgramAnalyser.Global
open ProgramAnalyser.Objects
open Utils

// this file is about the logistical operations

type Proposition<'a> =
    | True
    | False
    | Atom of isPos:bool * atom:'a
    | And of Proposition<'a> list
    | Or of Proposition<'a> list
    | Not of Proposition<'a>
    | Implies of Proposition<'a> * Proposition<'a>
//    | Forall of Variable list * Proposition<'a>
//    | Exists of Variable list * Proposition<'a>
    static member MapAtom x map =
        let inline recur x = Proposition<_>.MapAtom x map in
        match x with
        | True -> True
        | False -> False
        | Atom (isPos, atom) -> map (isPos, atom)
        | And lst -> And $ List.map recur lst
        | Or lst -> Or $ List.map recur lst
        | Not p -> Not $ recur p
        | Implies (p1, p2) -> Implies (recur p1, recur p2)
    static member SubsVars prop map =
        let inline recur prop = Proposition<_>.SubsVars prop map in
        match prop with
        | True | False -> prop
        | Atom (isPos, atom) -> Atom (isPos, substVars atom map)
        | And lst -> And $ List.map recur lst
        | Or lst -> Or $ List.map recur lst
        | Not p -> Not $ recur p
        | Implies (p1, p2) -> Implies (recur p1, recur p2)
    override x.ToString () =
        match x with
        | True -> "true"
        | False -> "false"
        | Atom (isPos, atom) -> if isPos then $"{atom}" else $"~({atom})"
        | And [] | Or [] -> "()"  // just add special marks
        | And [ x ] | Or [ x ] -> $"({x})"  // just wrap them specially, not to bother the outer stuff
        | And props ->
            let toString prop =
                match prop with
                | Or _ | Implies _ -> $"({prop})"
                | _ -> toString prop in
            String.concat " && "
                (List.map toString props |> List.filter (fun x -> x.Length > 0))
        | Or props ->
            let toString prop =
                match prop with
                | Implies _ -> $"({prop})"
                | _ -> toString prop in
            String.concat " || "
                (List.map toString props |> List.filter (fun x -> x.Length > 0))
        | Not prop ->
            match prop with
            | True | False -> "~" + toString prop
            | _ -> $"~({prop})"
        | Implies (p1, p2) ->
            let strP1 =
                match p1 with
                | Implies _ -> $"({p1})"
                | _ -> toString p1
            in
            let strP2 = toString p2 in
            $"{strP1} -> {strP2}"

type Forall<'a> = Forall of Variable list * Proposition<'a>
    with
    override x.ToString () =
        match x with
        | Forall (vList, prop) ->
            let varList =
                List.map toString vList
                |> String.concat " "
            in
            $"forall {varList}.{prop}"

/// due to the constraints in the type system cannot let `IVarSubstitutable<_,_>` be implementable
/// here is an additional form 
let inline substPropositionVars prop map = Proposition<_>.SubsVars prop map

let atomise x = Atom (true, x)

///// Given an assignment statement, compute the weakest precondition of the proposition
//let assnWeakestPrecondition assnStmt =
//    Proposition<_>.SubstituteVars subs uncurry Map.add assnStmt Map.empty

let rec lispPrintProposition prop : string =
    let inline recur prop = lispPrintProposition prop in
    match prop with
    | True -> "true"
    | False -> "false"
    | Atom (isPos, atom) -> if isPos then lispPrint atom
                            else $"(not {lispPrint atom})"
    | And props -> $"""(and {String.concat " " (List.map recur props)})"""
    | Or props -> $"""(or {String.concat " " (List.map recur props)})"""
    | Not prop -> $"(not {recur prop})"
    | Implies (p1, p2) -> $"(=> {recur p1} {recur p2})"

let lispPrintForall forall : string =
    match forall with
    | Forall (vars, prop) ->
        let varList = String.concat " " (List.map (fun v -> $"({v} Real)") vars)
        $"(forall ({varList}) {lispPrintProposition prop})"


module Parser = begin
    type private Token =
        | LParen
        | RParen
        | Symbol of string

    let private tokenise (input : string) : Token list =
        let regex = Regex(@"\(|\)|[^\s\(\)]+")
        let matches = regex.Matches(input)

        [for m in matches -> 
            match m.Value with
            | "(" -> LParen
            | ")" -> RParen
            | s -> Symbol s]

    type private GeneralNode =
        | Branch of GeneralNode list
        | Info of string
    
    let rec private parseGeneralNode tokens =
        match tokens with
        | Symbol s :: rest -> Info s, rest
        | LParen :: rest ->
            let children, remaining = parseGeneralNodeList rest in
            Branch children, remaining
        | RParen :: _ | [] -> failwith "Invalid input or unbalanced parentheses"

    and private parseGeneralNodeList tokens =
        let rec loop tokens acc =
            match tokens with
            | RParen :: rest -> List.rev acc, rest
            | [] -> failwith "Unbalanced parentheses"
            | _ ->
                let node, remaining = parseGeneralNode tokens
                loop remaining (node :: acc)
        in
        loop tokens []

    type Node =
        /// has a starting information, may also be a pure list depending on semantics
        | NFunc of string * Node list
        /// does not have start information, which is definitely list
        | NList of Node list
        
    let rec eliminateLetBindings node =
        match node with
        | NFunc ("let", bindingsNode :: [ bodyNode ]) ->
            match bindingsNode with
            | NList bindings ->
                let varMap =
                    bindings
                    |> List.map (function
                        | NFunc (varName, [value]) -> (Variable varName, eliminateLetBindings value)
                        | _ -> failwith "Invalid let binding")
                    |> Map.ofList
                in
                let expandedBody = substituteVarsInNode varMap bodyNode in
                eliminateLetBindings expandedBody
            | _ -> failwith "Invalid let bindings"
        | NFunc (name, children) -> NFunc (name, List.map eliminateLetBindings children)
        | NList nodes -> NList (List.map eliminateLetBindings nodes)

    and substituteVarsInNode (map: Map<Variable, Node>) (node: Node) : Node =
        match node with
        | NFunc (name, children) ->
            match map.TryFind (Variable name) with
            | Some value ->
                match value with
                | NFunc (v, nodes) -> NFunc (v, nodes ++ List.map (substituteVarsInNode map) children)
                | NList lst -> NList $ lst ++ List.map (substituteVarsInNode map) children
            | None -> NFunc (name, List.map (substituteVarsInNode map) children)
        | NList nodes -> NList (List.map (substituteVarsInNode map) nodes)
    
    let rec private parseNode tokens =
        match tokens with
        | Symbol s :: rest -> NFunc (s, []), rest
        | LParen :: Symbol s :: rest ->
            let children, remaining = parseNodeList rest in
            NFunc (s, children), remaining
        | LParen :: LParen :: rest ->
            let lst, remaining = parseNodeList (LParen :: rest) in
            NList lst, remaining
        | LParen :: RParen :: rest ->
            NList [], rest
        | [ LParen ] | RParen :: _ | [] -> failwith "Unbalanced parentheses"
    and private parseNodeList tokens =
        let rec loop tokens acc =
            match tokens with
            | RParen :: rest -> List.rev acc, rest
            | [] -> failwith "Unbalanced parentheses"
            | _ ->
                let node, remaining = parseNode tokens
                loop remaining (node :: acc)
        in
        loop tokens []

    let nodeToNumeric node =
        match node with
        | NFunc ("/", [NFunc (x, []); NFunc (y, [])]) ->
            Numeric.Parse x / Numeric.Parse y
        | NFunc (x, []) ->
            Numeric.Parse x
        | _ -> failwith "Invalid numeric format."
    
    let rec nodeToArithExpr node =
        match node with
        | NFunc (name, children) ->
            match name with
            | "+" -> AOperation (OpAdd, List.map nodeToArithExpr children)
            | "*" -> AOperation (OpMul, List.map nodeToArithExpr children)
            | "-" -> AOperation (OpMinus, List.map nodeToArithExpr children)
            | "/" -> AOperation (OpDiv, List.map nodeToArithExpr children)
            | "let" ->
                match children with
                | NList bindings :: [ expr ] ->
                    let map = bindingsToMap bindings in
                    let arithExpr = nodeToArithExpr expr in
                    substVars arithExpr map
                | _ -> failwith "Invalid let expression"
            | _ ->
                if Char.IsLetter name[0] then AVar (Variable name)
                else AConst $ nodeToNumeric node
        | NList _ -> failwith "NList nodes should not appear at this point"
    and bindingsToMap bindings =
        bindings
        |> List.map (function
            | NFunc (var, [value]) -> (Variable var, nodeToArithExpr value)
            | _ -> failwith "Invalid binding format")
        |> Map.ofList

    
    let parseSMTLIBToNode (input : string) : Node =
        let tokens = tokenise input
        let node, remaining = parseNode tokens

        match remaining with
        | [] -> node
        | _ -> failwith "Invalid SMT-LIB input"
    
    let rec nodeToProposition parseUnknown node =
        let inline recur node = nodeToProposition parseUnknown node in
        match node with
        | NFunc (name, children) ->
            match name with
            | "true" -> True
            | "false" -> False
            | "and" -> And (List.map recur children)
            | "or" -> Or (List.map recur children)
            | "not" ->
                match children with
                | [child] -> Not (recur child)
                | _ -> failwith "Invalid not expression"
            | "implies" ->
                match children with
                | [left; right] ->
                    Implies (recur left, recur right)
                | _ -> failwith "Invalid implies expression"
//            | "forall" ->
//                match children with
//                | NList varNodes :: [ propNode ] ->
//                    let vars = List.map
//                                   (function
//                                    | NFunc (v, []) -> Variable v
//                                    | _ -> failwith "Invalid variable") varNodes in
//                    Forall (vars, recur propNode)
//                | NFunc (var, varNodes) :: [ propNode ] ->
//                    let vars = List.map
//                                   (function
//                                    | NFunc (v, []) -> Variable v
//                                    | _ -> failwith "Invalid variable") varNodes in
//                    Forall (Variable var :: vars, recur propNode)
//                | _ -> failwith "Invalid forall function"
            | _ -> parseUnknown node
        | _ -> parseUnknown node
    
    let nodeToPropWithNodeToAtom nodeToAtom node =
        let parse node = Atom (true, nodeToAtom node) in
        nodeToProposition parse node
    
    let parseSMTLIB2Proposition additionalParse (input : string) =
        parseSMTLIBToNode input
        |> eliminateLetBindings
        |> nodeToProposition additionalParse
    
end

type VarType =
    | VTReal
    | VTInt
    override x.ToString () =
        match x with
        | VTReal -> "Real"
        | VTInt  -> "Int"

type LogicSupp<'a> = {
    allVars : Set<Variable> option
    /// var |-> (lower, upper)
    varRange : Map<Variable, ArithExpr * ArithExpr>
    /// var |-> { Real | Int }
    specialVarTypes : Map<Variable, VarType>
    atomParse : Parser.Node -> Proposition<'a>
}

// UGLY TRICK TO WORK AROUND THE TYPE SYSTEM PROBLEM
type private PropSupp<'p> = {
    collectVars : 'p -> Set<Variable>
    lispPrint : 'p -> string
}

// should define an additional function to work on this
let rec collectPropositionVars prop =
    let inline recur prop = collectPropositionVars prop in
    match prop with
    | True | False -> Set.empty
    | Atom (_, atom) -> collectVars atom
    | And lst -> Set.unionMany $ List.map recur lst
    | Or lst -> Set.unionMany $ List.map recur lst
//    | Forall (tmpBounded, prop) -> Set.difference (recur prop) (Set.ofList tmpBounded)
//    | Exists (tmpBounded, prop) -> Set.difference (recur prop) (Set.ofList tmpBounded)
    | Implies (p1, p2) -> Set.union (recur p1) (recur p2)
    | Not prop -> recur prop

let collectForallVars (Forall (vars, prop)) =
    Set.difference
        (collectPropositionVars prop)
        (Set.ofSeq vars)

/// declare the variables of the proposition according to the supplementary information of variables
let varDeclSString supp =
    let declPart =
        supp.allVars.Value
        |> Set.toSeq
        |> Seq.map (fun x ->
            let ty = Option.defaultValue VTReal $ Map.tryFind x supp.specialVarTypes in
            $"(declare-const {x} {ty})")
        |> String.concat "\n"
    in
    let rangePart =
        supp.allVars.Value
        |> Set.toSeq
        |> Seq.map (fun x -> 
            match Map.tryFind x supp.varRange with
            | Some (lower, upper) ->
                let lower, upper = lispPrint lower, lispPrint upper in
                $"(assert (<= {x} {upper}))" + "\n" +
                $"(assert (>= {x} {lower}))"
            | None -> "")
        |> String.concat "\n"
    in
    declPart + rangePart

/// force the Z3 environment into a `Monad` to keep the context always free
let private execZ3 exec =
    use ctx = new Context () in
    exec ctx

/// Monadic function to the Z3 Monad, accept the state Z3 and also returns it.
/// Do the following basic shared preprocessing for Z3-related stuff:
/// 1. collect the variables if not yet given
/// 2. convert the proposition into a variable declared constraint expression 
let private preprocess (z3Ctx : Context) supp pSupp propositions =
    let supp = match supp.allVars with
               | Some _ -> supp
               | None   -> {
                   supp with
                       allVars =
                           Seq.map pSupp.collectVars propositions
                           |> Set.unionMany
                           |> Some
               }
    in
    let varDeclStr = varDeclSString supp in
    let propStr =
        Seq.map (fun proposition ->
            $"(assert {pSupp.lispPrint proposition})")
            propositions
        |> String.concat "\n"
    in
    let inquiry = varDeclStr + propStr in
    // debugPrint $"Z3 Inquiry: {inquiry}"
    let constraints = z3Ctx.ParseSMTLIB2String inquiry in
    z3Ctx, supp, constraints
    

let private propSup =
    { collectVars = collectPropositionVars
      lispPrint = lispPrintProposition }

/// returns whether the proposition is satisfiable
let checkSAT supp propositions =
    /// the monadic execution function
    let exec z3Ctx =
        let z3Ctx, _, constraints = preprocess z3Ctx supp propSup propositions in
        let solver = z3Ctx.MkSolver () in
        solver.Assert constraints;
        match solver.Check [] with
        | Status.SATISFIABLE -> true
        | Status.UNSATISFIABLE -> false
        | Status.UNKNOWN -> failwith $"Result Unknown, due to: {solver.ReasonUnknown}"
        | _ -> IMPOSSIBLE ()
    in
    execZ3 exec

let private forallSup =
    { collectVars = collectForallVars
      lispPrint = lispPrintForall }

let quantifierElimination supp foralls =
    let exec ctx =
        let ctx, _, toEliminate = preprocess ctx supp forallSup foralls in
        let tactic = ctx.MkTactic("qe") in
        let goal = ctx.MkGoal () in
        goal.Add(toEliminate);
        let param = ctx.MkParams() in
        param.Add("qe_nonlinear", true) |> ignore;
        let applyResult = tactic.Apply(goal, param) in
        // extract and Parse the information
        let mapper (goal : Goal) =
            goal.Formulas
            |> Array.map (fun (bExpr : Microsoft.Z3.BoolExpr) ->
                Parser.parseSMTLIB2Proposition supp.atomParse $ toString bExpr)
        in
        let simplify (goal : Goal) =
            let simTac = ctx.MkTactic "ctx-simplify" in
            simTac.Apply(goal).Subgoals
        in
        // the propositions are essentially of conjunctive relation
        Array.collect simplify applyResult.Subgoals
        |> Array.map mapper
        |> Array.concat
        |> List.ofArray
        |> And
    in
    execZ3 exec

let rec toNnf (prop: Proposition<'a>) : Proposition<'a> =
    match prop with
    // basic case
    | And props -> And (List.map toNnf props)
    | Or props -> Or (List.map toNnf props)
//    | Forall (vList, prop) -> Forall (vList, toNnf prop)
//    | Exists (vList, prop) -> Exists (vList, toNnf prop)
    | Implies (p1, p2) -> toNnf (Or [Not p1; p2])
    | Atom _ | True | False -> prop
    // eliminate Not
    | Not (And props) -> Or (List.map (fun p -> toNnf (Not p)) props)
    | Not (Or props) -> And (List.map (fun p -> toNnf (Not p)) props)
    | Not (Not p) -> toNnf p
    | Not (Implies (p1, p2)) -> toNnf (And [p1; Not p2])
    | Not (Atom (isPos, atom)) -> Atom (not isPos, atom)
//    | Not (Forall (vList, prop)) -> Exists (vList, toNnf (Not prop))
//    | Not (Exists (vList, prop)) -> Forall (vList, toNnf (Not prop))
    | Not False -> True
    | Not True -> False

#nowarn "58"

module DisjunctiveNormal = begin
    /// assume the Negative Normal Form of the proposition
    /// and the atomic will contain also the negation information
    type NnfProp<'a> =
        | LTrue
        | LFalse
        | LAtom of 'a
        | LOr of NnfProp<'a> list
        | LAnd of NnfProp<'a> list

    /// \/_i ( /\_j a_{i, j} )
    type DisjunctiveNormalProp<'a when 'a : comparison> =
        | DNFTrue
        | DNFFalse
        | DNFProps of Set<Set<'a>>

    let rec nnfPropToDNF lp =
        match lp with
        | LTrue -> DNFTrue
        | LFalse -> DNFFalse
        | LAtom a -> DNFProps $ Set.singleton (Set.singleton a)
        | LOr lst ->
            let folder prevRes nEle =
                match prevRes with
                | DNFTrue -> DNFTrue
                | DNFFalse -> nnfPropToDNF nEle
                | DNFProps set ->
                    match nnfPropToDNF nEle with
                    | DNFTrue -> DNFTrue
                    | DNFFalse -> prevRes
                    | DNFProps set' -> DNFProps $ Set.union set set'
            in
            List.fold folder DNFFalse lst
        | LAnd lst ->
            let folder prevRes nextElement =
                match prevRes with
                | DNFTrue -> nnfPropToDNF nextElement
                | DNFFalse -> DNFFalse
                | DNFProps set ->
                    match nnfPropToDNF nextElement with
                    | DNFTrue -> prevRes
                    | DNFFalse -> DNFFalse
                    | DNFProps set' ->
                        Seq.allPairs (Set.toSeq set) (Set.toSeq set')
                        |> Seq.map (uncurry Set.union)
                        |> Set.ofSeq
                        |> DNFProps
            in
            List.fold folder DNFTrue lst

    /// to check whether there exists some `a` such that `a` and `Neg a` exist at the same time
    let isConsistent (seq : seq<bool * 'a>) =
        let hashSave = HashMap () in
        let findInconsistency (isPos, atom) =
            match HashMap.tryFind atom hashSave with
            | Some posVal -> isPos <> posVal
            | None -> HashMap.add atom isPos hashSave; false
        in
        Option.isNone $ Seq.tryFind findInconsistency seq

    /// obtain a list of formally consistent while mutually exclusive rules
    let toMutuallyExclusive (clauses : Set<Set<bool * 'a>>) =
        let consistentClauses = Set.filter (Set.toSeq >> isConsistent) clauses in
        let allAtoms = Set.unionMany $ Set.map (Set.map snd) consistentClauses in
        let expand set =
            Set.map snd set
            // obtain those not mentioned
            |> Set.difference allAtoms
            // expand each of these elements and then enumerate them separately
            |> Set.toList
            |> List.fold (fun sets a ->
                List.map (curry List.Cons (true, a)) sets ++
                List.map (curry List.Cons (false, a)) sets) [ Set.toList set ]
            |> List.map Set.ofList
        in
        Set.toList consistentClauses
        |> List.map expand
        |> List.concat
        |> Set.ofSeq

end

open DisjunctiveNormal

/// an internally NNF `Proposition` to `NnfProp`
let rec propToNnfProp prop =
    match prop with
    | And lst -> LAnd $ List.map propToNnfProp lst
    | Or lst -> LOr $ List.map propToNnfProp lst
    | Not _ | Implies _ ->
        let str =
            "To NNF Proposition should not contain `not` and `implies`."
        in
        failwith str 
    | Atom (isPos, atom) -> LAtom (isPos, atom)
    | True -> LTrue
    | False -> LFalse

let dnfPropToProp atomise dnfProp =
    match dnfProp with
    | DNFTrue -> True
    | DNFFalse -> False
    | DNFProps set ->
        Set.toList set
        |> List.map Set.toList
        |> List.filter isConsistent
        |> List.map (List.map atomise >> And)
        |> Or

///// to valid DNF
//let simplifyProposition prop =
//    toNnf prop
//    |> propToNnfProp
//    |> nnfPropToDNF
//    |> dnfPropToProp Atom
    
