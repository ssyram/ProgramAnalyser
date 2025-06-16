module ProgramAnalyser.Input

open System.IO
open ProgramAnalyser
open Utils

let parseProgramFromStr progStr =
    parse Lexer.token Parser.program progStr

let parseByPath programPath =
    parseProgramFromStr $ File.ReadAllText programPath
