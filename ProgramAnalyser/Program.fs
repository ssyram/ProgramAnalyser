// For more information see https://aka.ms/fsharp-console-apps
    
open ProgramAnalyser
open Run
open Utils

[<EntryPoint>]
let main args =
    runArgAnalysis $ Array.toList args;
    0
