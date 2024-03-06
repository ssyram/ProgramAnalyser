module ProgramAnalyser.Test

open System.Collections.Generic
open System.IO
open Microsoft.Z3
open ProgramAnalyser.Global
open ProgramAnalyser.Output
open Utils
open Logic.DisjunctiveNormal
open Logic
open Polynomial
open Run
    
let testNormaliseProp () =
    let toTest = [
        LTrue;
        LFalse;
        LAtom "A";
        LOr [LAtom "A"; LAtom "B"];
        LAnd [LAtom "A"; LAtom "B"];
        LOr [LAnd [LAtom "A"; LAtom "B"]; LAnd [LAtom "C"; LAtom "D"]];
        LAnd [LAtom "A"; LOr [LAtom "B"; LAtom "C"]]
        LOr [LAnd [LAtom "A"; LAtom "B"]; LAnd [LAtom "C"; LOr [LAtom "D"; LAtom "E"]]];
        LAnd [LOr [LAtom "A"; LAtom "B"]; LOr [LAtom "C"; LAtom "D"]];
        LAnd [LAtom "A"; LOr [LAtom "B"; LAnd [LAtom "C"; LAtom "D"]]];
        LOr [LAnd [LAtom "A"; LOr [LAtom "B"; LAtom "C"]]; LAnd [LAtom "D"; LAtom "E"]];
        LAnd [LAtom "A"; LOr [LAtom "B"; LAnd [LAtom "C"; LOr [LAtom "D"; LAtom "E"]]]];
    ]

    let expectedResult = [
        DNFTrue;
        DNFFalse;
        DNFProps (Set.singleton (Set.singleton "A"));
        DNFProps (Set.ofList [Set.singleton "A"; Set.singleton "B"]);
        DNFProps (Set.singleton (Set.ofList ["A"; "B"]));
        DNFProps (Set.ofList [Set.ofList ["A"; "B"]; Set.ofList ["C"; "D"]]);
        DNFProps (Set.ofList [Set.ofList ["A"; "B"]; Set.ofList ["A"; "C"]]);
        DNFProps (Set.ofList [Set.ofList ["A"; "B"]; Set.ofList ["C"; "D"]; Set.ofList ["C"; "E"]]);
        DNFProps (Set.ofList [Set.ofList ["A"; "C"]; Set.ofList ["A"; "D"]; Set.ofList ["B"; "C"]; Set.ofList ["B"; "D"]]);
        DNFProps (Set.ofList [Set.ofList ["A"; "B"]; Set.ofList ["A"; "C"; "D"]]);
        DNFProps (Set.ofList [Set.ofList ["A"; "B"]; Set.ofList ["A"; "C"]; Set.ofList ["D"; "E"]]);
        DNFProps (Set.ofList [Set.ofList ["A"; "B"]; Set.ofList ["A"; "C"; "D"]; Set.ofList ["A"; "C"; "E"]]);
    ]

    let results =
        List.map nnfPropToDNF toTest
        |> List.zip expectedResult
    in
    if List.forall (uncurry (=)) results then printfn "All Test Passed."
    else results
         |> List.zip toTest
         |> List.iter (fun (ori, (cmp1, cmp2)) ->
             if cmp1 <> cmp2 then
                 printfn $"Error with example: \"{ori}\", result: {cmp1}, while expected result: {cmp2}")

/// test reading from various examples
let testParsingResult () =
    /// the prepend path
    let prepend = "../../../../examples/" in
    // the testing examples
    let example1 = "h-t-r-2-3.program" in
    let example2 = "h-t-r-2-3-input-score.program" in
    
    undefined ()

    
let eliminateQuantifier (ctx : Context) (constraints: Microsoft.Z3.BoolExpr[]) =
    let tactic = ctx.MkTactic("qe") in
    let paras = ctx.MkParams() in
    paras.Add("qe_nonlinear", true) |> ignore
    let goal = ctx.MkGoal() in
    goal.Add(constraints)
    let applyResult = tactic.Apply(goal, paras) in
    
    // split the clauses in the sub-goals
    applyResult.Subgoals
    |> Array.map (fun x -> x.Simplify ())
    
let tryMy () =
    use ctx = new Context () in
    let str =
        """(declare-const a Real)
(declare-const b Real)
(declare-const c Real)

(assert (exists ((x Real)) (= (+ (* a x x) (* b x) c) 0.0)))""" in
    let expr = ctx.ParseSMTLIB2String str in
    eliminateQuantifier ctx expr
    |> Array.map (fun x -> x.Formulas)
    |> Array.concat
    |> Array.map (fun x -> Parser.parseSMTLIB2Proposition nodeToCompareProp $ toString x)
    |> Array.iteri (fun idx prop ->
        printfn $"{idx}: {prop}")
    
let testSolve () =

    // Initialize the Z3 context
    let dic = Dictionary ()
    dic.Add("model", "true")
    let ctx = new Context(dic)

    // Declare the variables
    let h = ctx.MkRealConst("h")
    let t = ctx.MkRealConst("t")
    let r : RealExpr = ctx.MkRealConst("r")
    
    printfn $"r is: {r}"
    printfn $"r.SExpr () is: {r.SExpr ()}"
    
    // Define the constraints
    let r_le_3 = ctx.MkLe(r, ctx.MkReal(3))
    let r_ge_2 = ctx.MkGe(r, ctx.MkReal(2))
    let h_le_t = ctx.MkLe(h, t)
    let h_plus_r_le_t_plus_1 = ctx.MkLe(ctx.MkAdd(h, r), ctx.MkAdd(t, ctx.MkReal(1)))

    printfn $"expr is: {h_plus_r_le_t_plus_1.ToString ()}"
    printfn $"expr.SExpr () is: {h_plus_r_le_t_plus_1.SExpr ()}"
    
    // Call the function to eliminate the quantifier for r
    let constraints =
        ctx.MkForall(
            [| r |], 
            ctx.MkImplies(ctx.MkAnd [| r_le_3; r_ge_2 |], ctx.MkOr [| h_le_t; h_plus_r_le_t_plus_1 |]))
    let result = eliminateQuantifier ctx [| constraints |]
    

    // Print the result
    let mapper (goal : Goal) =
        goal.Formulas
        |> Array.map (fun (bExpr : Microsoft.Z3.BoolExpr) ->
            Parser.parseSMTLIB2Proposition nodeToCompareProp $ toString bExpr)
    in
    Array.map mapper result
    |> Array.concat
    |> Array.iteri (fun idx prop -> printfn $"{idx}: {prop}")

    // Define the constraints
//    let r_le_3 = ctx.MkLe(r, ctx.MkInt(3))
//    let r_ge_2 = ctx.MkGe(r, ctx.MkInt(2))
//    let h_le_t = ctx.MkLe(h, t)
//    let h_plus_r_le_t_plus_1 = ctx.MkLe(ctx.MkAdd(h, r), ctx.MkAdd(t, ctx.MkInt(1)))
//
////    let qe = ctx.MkTactic "qe"
////    let goal = ctx.MkGoal ()
//    
//    // Combine constraints into a single formula
//    let constraints = ctx.MkAnd([|r_le_3; r_ge_2; h_le_t; h_plus_r_le_t_plus_1|])
//
//    // Eliminate the quantifier for r
//    let eliminator = ctx.MkForall([|r|], constraints)
//    goal.Add eliminator
    
//    let result =
//        let applyResult = qe.Apply(goal)
//        let result = applyResult.Subgoals.[0].Simplify()
//        
//        
//
//        if ctx.MkNot(result).IsFalse then
//            let solver = ctx.MkSolver()
//            solver.Add(result)
//            let checkResult = solver.Check()
//            match checkResult with
//            | Status.SATISFIABLE ->
//                let model = solver.Model
//                Some model
//            | Status.UNSATISFIABLE ->
//                None
//            | _ ->
//                None
//        else
//            None
    
//    let solver = ctx.MkSolver "qe"
//    solver.Add(eliminator)
//    let result = solver.Check()
//
//    // Print the result
//    match result with
//    | Status.SATISFIABLE ->
//        let model = solver.Model
//        printfn "Satisfiable: %A" model
//    | Status.UNSATISFIABLE ->
//        printfn "Unsatisfiable"
//    | _ ->
//        printfn "Unknown"

    // Dispose of the Z3 context
    ctx.Dispose()

let testParseNumber () =
    printfn $"""{(Numeric.Parse "1E-5").ToString "float"}"""

let testZ3 () =
    // Initialize Z3 context
    let ctx = new Context()

    // Declare variables
    let r = ctx.MkRealConst("r")
    let h = ctx.MkRealConst("h")
    let t = ctx.MkRealConst("t")

    // Define the constraints
    let r_ge_2 = ctx.MkGe(r, ctx.MkReal(2))
    let r_le_3 = ctx.MkLe(r, ctx.MkReal(3))
    let h_le_t = ctx.MkLe(h, t)
    let h_plus_r_le_t_plus_1 = ctx.MkLe(ctx.MkAdd(h, r), ctx.MkAdd(t, ctx.MkReal(1)))

    // Combine the constraints
    let formula = ctx.MkImplies(ctx.MkAnd(r_ge_2, r_le_3), ctx.MkAnd(h_le_t, h_plus_r_le_t_plus_1))
    
//    let formula = ctx.MkExists ([| h; t |], formula)
    let quantifier = ctx.MkForall ([| r |], formula)
    
    let solver = ctx.MkSolver ()
    match solver.Check quantifier with
    | Status.SATISFIABLE ->
        printfn $"{solver.Model}"
    | _ ->
        printfn "UNSATISFIABLE"
    
    let tactic = ctx.MkTactic("qe")
    let goal = ctx.MkGoal ()
    goal.Add quantifier;
    let result = tactic.Apply goal in
    let goal = result.Subgoals[0].Simplify ()
    printfn $"{goal}"
    
    ctx.Dispose ()

/// assume that the examples are from "../../../../examples/"
let private getExamplePath (exampleName : string) =
    let exampleName =
        if exampleName.EndsWith ".program" then exampleName
        else exampleName + ".program" in
    "../../../../examples/" + exampleName

let private testExecPrint exec input =
    let time, res = exec input in
    printfn $"{res}"
    printfn $"Time Elapsed: {time}."

let private testExecPrintToOutputLog exec input =
    // firstly, generate the output path, if not existed, create it
    let outputPath =
        let directory = Path.GetDirectoryName input.programPath in
        let outputDirectory = Path.Combine(directory, "output") in
        Directory.CreateDirectory outputDirectory |> ignore;
        let outputFileName =
            Path.ChangeExtension(Path.GetFileName input.programPath, ".txt") in
        Path.Combine(outputDirectory, outputFileName) in
    
    // execute the information
    let time, res = exec input in
    
    // write and return
    File.WriteAllText(outputPath, res + "\n" + $"Generation Time: {time}\n")
    
let private testExec input =
    // perform execution
    let timing = System.Diagnostics.Stopwatch () in
    timing.Start ();
    let ret = fst $ runParseAnalysis input None in
    let time = timing.Elapsed in
    time, ret

/// the central function to modify if the printing mode is to change
let private testRunParseAnalysis input =
    testExecPrintToOutputLog testExec input

let private usualTestExample exampleName =
    let input = {
            programPath = getExamplePath exampleName
            toTruncate = true
            terminationType = ProgramTerminationType.PTTTermination
            endLoopScoreAccuracy = None
        }
    in
    testRunParseAnalysis input


let test_hare_turtle_outside () = usualTestExample "h-t-r-2-3"

let test_hare_turtle_inside () = usualTestExample "h-t-r-2-3-inside-score"

let test_growing_walk () =
    testRunParseAnalysis {
        programPath = getExamplePath "growing-walk-Q1"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = Some "1e-4"
    }

let test_para_estimate () =
    testRunParseAnalysis {
        programPath = getExamplePath "para-estimation-recursive"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = Some "1e-5"
    }

/// the conditional wraps probability pattern
let test_ped_multi_v5_cond_prob () =
    testRunParseAnalysis {
        programPath = getExamplePath "pedestrian-multiple-branches-v5"
        toTruncate = true
        terminationType = PTTDirect
        endLoopScoreAccuracy = Some "1e-4"
    }

/// tested:
/// v3, v4
let test_ped_multi_v3_cond_only () =
    testRunParseAnalysis {
        programPath = getExamplePath "pedestrian-multiple-branches-v4"
        toTruncate = true
        terminationType = PTTDirect
        endLoopScoreAccuracy = Some "1e-4"
    }

/// Q1 && Q2 -- PASSED
let test_neg_ten_mode () =
    testRunParseAnalysis {
        programPath = getExamplePath "add-uniform-unbounded-Q1"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = None
    }

/// Looks like no problem
let test_cav_example_5 () =
    testRunParseAnalysis {
        programPath = getExamplePath "cav-example-5-Q2"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = None }

let test_cav_example_7 () =
    testRunParseAnalysis {
        programPath = getExamplePath "cav-example-7-Q1"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = None }

let test_ped_original () =
    testRunParseAnalysis {
        programPath = getExamplePath "pedestrian"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = Some "1e-4" }

/// tested:
/// v1, v2, v3, dev5
let test_ped_beta () =
    testRunParseAnalysis {
        programPath = getExamplePath "pedestrian-deviation5.program"
        toTruncate = true
        terminationType = PTTDirect
        endLoopScoreAccuracy = Some "1e-4" }

let test_random_box_walk () =
    testRunParseAnalysis {
        programPath = getExamplePath "random-box-walk-Q1"
        toTruncate = false
        terminationType = PTTDirect
        endLoopScoreAccuracy = None }

/// tested:
/// v1, v2, v3, v4
let test_random_walk_inside () =
    testRunParseAnalysis {
        programPath = getExamplePath "random-walk-beta-inside-scorey-v4.program"
        toTruncate = true
        terminationType = PTTTermination
        endLoopScoreAccuracy = None }

let test_run_all () =
    List.iter (fun func -> func ()) [
        test_hare_turtle_outside
        test_hare_turtle_inside
        test_growing_walk
        test_para_estimate
        test_ped_multi_v5_cond_prob
        test_ped_multi_v3_cond_only
        test_neg_ten_mode
        test_cav_example_5
        test_cav_example_7
        test_ped_original
        test_ped_beta
        test_random_box_walk
        test_random_walk_inside
    ]

let testStringSlice () =
    let str = "12345" in
    printfn $"Str: {str[5..7]}"

let exampleConfig () =
    [
        [
            "h-t-r-2-3"
        ]
    ]

let test_table_1 () =
    undefined ()
