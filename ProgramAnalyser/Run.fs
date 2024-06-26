module ProgramAnalyser.Run

open System
open System.IO
open Microsoft.FSharp.Reflection
open ProgramAnalyser
open ProgramAnalyser.Global
open ProgramAnalyser.Objects
open ProgramAnalyser.Output
open ProgramAnalyser.ParserSupport
open Utils

type AnalysisContext = {
    programPath : string
    toTruncate : bool
    terminationType : ProgramTerminationType
    endLoopScoreAccuracy : string option
}

type ArgAnalysisResult = {
    fileName : string option
    outFilePath : string option
    toTruncate : bool option
    terminationType : ProgramTerminationType option
    endLoopScoreAccuracy : string option
    /// by default 60
    globalDivisionM : int
    /// var |-> m
    varDivisionM : Map<string, int>
    /// var |-> (min, max)
    /// by default (0, 5)
    /// see Flags.DEFAULT_CONFIG_VAR_RANGE
    specifiedRanges : Map<string, RealInf * RealInf>
    /// by default 6
    degree1 : int
    /// by default 6
    degree2 : int
    /// by default "LP", another option is "SDP"
    solver : string
    /// by default 1
    table : int
}

let inline runGenOutput input =
    genOutput input

let runGenConfig program randVars args =
    let varDivM =
        Map.toList args.varDivisionM
        |> List.map (fun (k, v) -> (Variable k, uint v))
        |> Map.ofList in
    let varRanges =
        Map.toList args.specifiedRanges
        |> List.map (fun (k, v) -> (Variable k, v))
        |> Map.ofList in
    let cfgInput =
        {
            cfgProgram = program
            cfgRandVars = randVars
            cfgDegOne = uint args.degree1
            cfgDegTwo = uint args.degree2
            cfgDefDivM = uint args.globalDivisionM
            cfgVarDivM = varDivM
            cfgVarRanges = varRanges
            cfgSolver = args.solver
            cfgTable = uint args.table 
        }
    in
    genConfigOutput cfgInput

/// returns: (main, Maybe config)
let inline runParseAnalysis main maybeArgs =
    let programPath = main.programPath in
    let (RandomVarList lst), program = Input.parseByPath programPath in
    let program = simplifyProgram program in
    let randVarRanges =
        Map.ofSeq $ List.map (BiMap.sndMap getDistDomainRange) lst
    in
    let programName = Path.GetFileNameWithoutExtension programPath in
    let input =
        {
            programName = programName
            program = program
            randomVars = lst
            toTruncate = main.toTruncate
            terminationType = main.terminationType
            randVarRanges = randVarRanges
            endLoopScoreAccuracy = main.endLoopScoreAccuracy
        }
    in
    let main = runGenOutput input in
    let maybeConfig = Option.map (runGenConfig program lst) maybeArgs in
    
    (main, maybeConfig)

let private getAllSp () =
    undefined ()

let runSpAnalysis name =
    Map.tryFind name $ genAllSp ()
    
let runAllAnalysis main maybeArgs =
    let fileName = Path.GetFileNameWithoutExtension main.programPath in
    match runSpAnalysis fileName with
    | Some ret -> ret
    | None     -> runParseAnalysis main maybeArgs

let inline runPrintingOut (mainInput, args) (outPath : string option) =
    let pPath = mainInput.programPath in
    let fileName = Path.GetFileNameWithoutExtension pPath in
    let mainFileName = fileName + "-input.txt" in
    let configFileName = fileName + "-config.txt" in
    let (outMainPath, outConfigPath) =
        let path = match outPath with
                   | Some path -> path
                   | None -> Path.GetDirectoryName pPath in
        (Path.Combine (path, mainFileName), Path.Combine (path, configFileName))
    in
    let timing = System.Diagnostics.Stopwatch () in
    timing.Start ();
    let main, cfg = runAllAnalysis mainInput args in
    let time = timing.Elapsed in
    let cfg = "Parser@" + time.TotalSeconds.ToString "f4" + "\n" + Option.get cfg in
    File.WriteAllText (outMainPath, main);
    File.WriteAllText (outConfigPath, cfg);
    debugPrint $"Time generating {Path.GetFileName pPath}: {time}"

// let testFloatToString () =
//     let f = 123456.123456789 in
//     let str = f.ToString "f4" in
//     printfn $"{str}"

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
    globalDivisionM = 60
    varDivisionM = Map.empty
    specifiedRanges = Map.empty
    degree1 = 6
    degree2 = 6
    solver = "LP"
    table = 1
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

let private getPosIntVal str =
    try
        let ret = Int32.Parse str in
        if ret < 0 then None
        else Some ret
    with | _ -> None

let private getNumeric (str : string) =
    try match str.ToLower () with
        | "-inf" -> Some RINegInf
        | "+inf" | "inf" -> Some RIPosInf
        | str -> Some (RINum $ Numeric.Parse str)
    with | _ -> None

/// -m:number
/// OR
/// -Mname:number
/// returns: Maybe (Maybe Name, Int)
let parseMSpec (str : string) =
    let addNoName x = (None, x) in
    let getVal (str : string) =
        if str[2] <> ':' then None
        else Option.map addNoName $ getPosIntVal (str[3..])
    in
    let addName name v = (Some name, v) in
    let getNameAndVal (str : string) =
        let divPos = str.IndexOf ':' in
        if divPos = -1 then None
        elif divPos = 2 then None
        else Option.map (addName str[2..divPos-1]) $ getPosIntVal str[divPos+1..]
    in
    if str.Length <= 2 then None
    elif str.StartsWith "-m" then getVal str
    elif str.StartsWith "-M" then getNameAndVal str
    else None

let private testExamples exec examples =
    let printer x =
        let res = exec x in
        printfn $"{x} |-> {res}"
    in
    List.iter printer examples
    printfn "Done"

/// passed
let testParseMSpec () =
    testExamples parseMSpec [
            "-m"
            "-m:"
            "-m:-1"
            "-m:80"
            "-M"
            "-M:100"
            "-Mp_t:100"
        ]

/// -Rname:min~max
/// example:
/// -Rp_t:0~5
let parseVarRange (str : string) =
    let nameDivPos = str.IndexOf ':' in
    let valDivPos = str[nameDivPos..].IndexOf '~' in
    let analyse () =
        let valDivPos = valDivPos + nameDivPos in
        let varName = str[2..nameDivPos-1] in
        let min = getNumeric str[nameDivPos+1..valDivPos-1] in
        let max = getNumeric str[valDivPos+1..] in
        match (min, max) with
        | (Some min, Some max) -> Some (varName, (min, max))
        | _ -> None
    in
    if str.StartsWith "-R" &&
       nameDivPos <> -1 &&
       nameDivPos <> 2 &&
       valDivPos <> -1 then
        analyse ()
    else None

/// passed
let testParseVarRange () =
    testExamples parseVarRange [
        "-a"
        "-R"
        "-Rvar:"
        "-R:"
        "-R:4"
        "-R:10-a"
        "-Rr_t:2~10"
        "-Rp_t:0~0.1"
        "-Rp_x:-0.8~0.8"
        "-Rp:-inf~inf"
    ]

let parseDegreeSpec (str : string) =
    if str.StartsWith "-degree:" then
        let d = getPosIntVal str[8..] in
        (d, d)
    elif str.StartsWith "-degree1:" then
        (getPosIntVal str[9..], None)
    elif str.StartsWith "-degree2:" then
        (None, getPosIntVal str[9..])
    else (None, None)

let testParseDegreeSpec () =
    testExamples parseDegreeSpec [
        "-d"
        "-degree"
        "-degree:"
        "-degree:6"
        "-degree1:9"
    ]
    
let private parseSolver (str : string) =
    match str.ToLower () with
    | "-solver:lp" -> Some "LP"
    | "-solver:sdp" -> Some "SDP"
    | _ -> None
    
let private parseTab (str : string) =
    let intVal =
        if str.StartsWith "-tab:" && str.Length > 5 then getPosIntVal str[5..]
        elif str.StartsWith "-table:" && str.Length > 7 then getPosIntVal str[7..]
        else None
    in
    flip Option.bind intVal $ fun v -> if v > 3 || v < 1 then None else Some v

// let testParseTab () =
//     testExamples parseTab [
//         "-tab:1"
//         "-tab"
//         "-tab:"
//         "-table:2"
//         "-table:5"
//     ]

let private parseIntVar (str : string) =
    if str.StartsWith "-int:" && str.Length > 5 then Some $ str[5..]
    else None

let private parseEncPath (str : string) =
    if str.StartsWith "-enc:" && str.Length > 5 then Some $ str[5..]
    else None

let testIsInt () =
    let tester str = (Numeric.Parse str).IsInt in
    testExamples tester [
        "1/2"
        "6/3"
        "5.00"
        "5.01"
    ]

// let testParseIntVar () =
//     testExamples parseIntVar [
//         "-int:"
//         "-int:p_x"
//         "-int:p_y"
//         "-int:123"
//     ]

let rec private argAnalysis args acc =
    let loop = argAnalysis in
    match args with
    | [] -> acc
    | "-O" :: outDir :: args ->
        checkValidPath outDir;
        loop args {
            acc with
                outFilePath = Some outDir
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
    | intVar :: args when Option.isSome $ parseIntVar intVar ->
        Flags.INT_VARS <- Set.add (Option.get $ parseIntVar intVar) Flags.INT_VARS;
        loop args acc
    | encPath :: args when Option.isSome $ parseEncPath encPath ->
        let path = Option.get $ parseEncPath encPath in
        let _ : unit =
            if File.Exists path then Flags.ENC_PATH <- path
            elif Directory.Exists path then Flags.ENC_PATH <- Path.Combine(path, ".enc.fl")
            else failwith $"path \"{path}\" does not exist."
        in
        loop args acc
    | "-debug" :: args ->
        Flags.DEBUG <- true;
        loop args acc
    | table :: args when Option.isSome $ parseTab table ->
        let table = Option.get $ parseTab table in
        Flags.TABLE <- table;
        loop args {
            acc with table = table
        }
    | solver :: args when Option.isSome $ parseSolver solver ->
        loop args {
            acc with solver = Option.get $ parseSolver solver 
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
    | mSpec :: args when Option.isSome $ parseMSpec mSpec ->
        match Option.get $ parseMSpec mSpec with
        | (Some var, mVal) ->
            loop args {
                acc with varDivisionM = Map.add var mVal acc.varDivisionM 
            }
        | (None, mVal) ->
            loop args {
                acc with globalDivisionM = mVal 
            }
    | vRange :: args when Option.isSome $ parseVarRange vRange ->
        let (var, range) = Option.get $ parseVarRange vRange in
        loop args {
            acc with specifiedRanges = Map.add var range acc.specifiedRanges
        }
    | degree :: args when parseDegreeSpec degree <> (None, None) ->
        let (d1, d2) = parseDegreeSpec degree in
        loop args {
            acc with
                degree1 = Option.defaultValue acc.degree1 d1
                degree2 = Option.defaultValue acc.degree2 d2 
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
    runPrintingOut (anaCtx, Some argResult) argResult.outFilePath
