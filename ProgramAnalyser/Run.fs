module ProgramAnalyser.Run

open System
open System.IO
open Microsoft.FSharp.Reflection
open ProgramAnalyser
open ProgramAnalyser.Global
open ProgramAnalyser.Output
open ProgramAnalyser.ParserSupport
open Utils

type AnalysisContext = {
    programPath : string
    toTruncate : bool
    terminationType : ProgramTerminationType
    endLoopScoreAccuracy : string option
}

let inline runGenOutput input =
    genOutput input

let inline runParseAnalysis input =
    let programPath = input.programPath in
    let (RandomVarList lst), program = Input.parseByPath programPath in
    let randVarRanges =
        Map.ofSeq $ List.map (BiMap.sndMap getDistDomainRange) lst
    in
    let programName = Path.GetFileNameWithoutExtension programPath in
    let input =
        {
            programName = programName
            program = program
            randomVars = lst
            toTruncate = input.toTruncate
            terminationType = input.terminationType
            randVarRanges = randVarRanges
            endLoopScoreAccuracy = input.endLoopScoreAccuracy
        }
    in
    runGenOutput input

let inline runPrintingOut input (outPath : string option) =
    let pPath = input.programPath in
    let outPath =
        match outPath with
        | Some path -> path
        | None ->
            let path = Path.GetDirectoryName pPath in
            let fileName = Path.ChangeExtension (Path.GetFileName pPath, "txt") in
            Path.Combine (path, fileName)
    in
    File.WriteAllText (outPath, runParseAnalysis input)

type ArgAnalysisResult = {
    fileName : string option
    outFilePath : string option
    toTruncate : bool option
    terminationType : ProgramTerminationType option
    endLoopScoreAccuracy : string option
}

let private checkHasExtension (name : string) ext =
    let realExt = Path.GetExtension name in
    if realExt[1..] = ext then name
    else failwith $"\"{name}\" should be of \".{ext}\" type, but has \".{realExt}\" type."

let private checkShouldExist obj objName =
    match obj with
    | Some obj -> obj
    | None -> failwith $"Expected {objName}."

let defaultArgResult () = {
    fileName = None
    outFilePath = None
    toTruncate = None
    terminationType = None
    endLoopScoreAccuracy = None
}

let argResultsToAnalysisContext argRes =
    let fileName = checkShouldExist argRes.fileName "file name" in
    {
        programPath = fileName
        toTruncate = Option.defaultValue true argRes.toTruncate
        terminationType = Option.defaultValue PTTTermination argRes.terminationType
        endLoopScoreAccuracy = argRes.endLoopScoreAccuracy
    }

let private isTerType (toParse : string) =
    toParse.StartsWith "-" &&
    let toParse = toParse[1..] in
    FSharpType.GetUnionCases typeof<ProgramTerminationType>
    |> Array.exists (fun info -> info.Name[3..].ToLower () = toParse)

let private getTerType (toParse : string) =
    // remove the starting "-"
    let toParse = toParse[1..] in
    FSharpType.GetUnionCases typeof<ProgramTerminationType>
    |> Array.pick (fun info ->
        if info.Name[3..].ToLower () = toParse then
            Some $ (FSharpValue.MakeUnion (info, [||]) :?> ProgramTerminationType)
        else None)

let private truncationStrings = [ "truncation"; "truncate" ]

let private isNonTruncate (toParse : string) =
    strConsistsBy toParse [
        [ "-" ]
        [ "non"; "no" ]
        [ "-"; "_" ]
        truncationStrings
    ]

let private isTruncate (toParse : string) =
    toParse.StartsWith "-" &&
    List.contains toParse[1..] truncationStrings

let private checkValidPath (path : string) =
    let invalidChars = Set.ofSeq $ Path.GetInvalidPathChars () in
    let invalidParts = String.filter (flip Set.contains invalidChars) path in
    if invalidParts <> "" then
        invalidParts.ToCharArray ()
        |> Array.map (fun c -> $"\"{c}\"")
        |> String.concat ", "
        |> fun s ->
            failwith $"Invalid path: {path}, containing invalid character(s): {s}."

let rec private argAnalysis args acc =
    let loop = argAnalysis in
    match args with
    | [] -> acc
    | "-O" :: outFileName :: args ->
        checkValidPath outFileName;
        loop args {
            acc with
                outFilePath = Some $ checkHasExtension outFileName "txt"
        }
    | ("-accuracy" | "-acc") :: accVal :: args ->
        try Numeric.Parse accVal |> ignore
        with
        | :? FormatException ->
            failwith $"Invalid accuracy number \"{accVal}\"."
        loop args {
            acc with
                endLoopScoreAccuracy = Some accVal
        }
    | terType :: args when isTerType terType ->
        loop args {
            acc with
                terminationType = Some $ getTerType terType
        }
    | truncate :: args when isTruncate truncate ->
        loop args {
            acc with
                toTruncate = Some true
        }
    | nonTruncate :: args when isNonTruncate nonTruncate ->
        loop args {
            acc with
                toTruncate = Some false
        }
    | fileName :: args ->
        checkValidPath fileName;
        loop args {
            acc with
                fileName = Some $ checkHasExtension fileName "program"
        }

/// <summary>
/// Runs argument analysis on the given arguments and executes the appropriate action based on the analysis.
/// </summary>
/// <param name="args">The arguments to analyze.</param>
let runArgAnalysis args =
    let argResult = argAnalysis args $ defaultArgResult () in
    let anaCtx = argResultsToAnalysisContext argResult in
    runPrintingOut anaCtx argResult.outFilePath
