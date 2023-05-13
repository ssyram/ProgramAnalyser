module ProgramAnalyser.Input

open System.IO
open ProgramAnalyser
open Utils

let parseProgramFromStr progStr =
    parse Lexer.token Parser.program progStr
    
let parseRVarsFromStr rvarStr =
    parse Lexer.token Parser.randvars rvarStr

let parseByPath programPath =
    let rvars = parseRVarsFromStr $ File.ReadAllText (programPath + ".rvars") in 
    let program = parseProgramFromStr $ File.ReadAllText programPath in
    (rvars, program)
