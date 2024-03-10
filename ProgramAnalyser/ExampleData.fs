module ProgramAnalyser.ExampleData

type SpProgram =
    | SPAddUniformUnboundedQ1
    | SPAddUniformUnboundedQ2
    | SP_CAV_Ex5_Q1
    | SP_CAV_Ex5_Q2
    | SP_CAV_Ex7_Q1
    | SP_CAV_Ex7_Q2
    | SPGrowingWalkQ1
    | SPGrowingWalkQ2
    | SPRdBoxWalk

module Main =
    let x = 1


module Config =
    let addUniformUnboundedQ1 =
        "6
6
bounded_domain
p_x@0 1
p_y@0 1
no_common_invs
initial_inputs
p_x@constant@0
p_y@constant@0
solver@LP"

let testAddUniform () =
    printfn $"{Config.addUniformUnboundedQ1}"
