// For more information see https://aka.ms/fsharp-console-apps
    
open ProgramAnalyser
open Run


[<EntryPoint>]
let main args =
    runByAnalysingArgs args;
    0
