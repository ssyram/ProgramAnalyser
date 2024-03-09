module ProgramAnalyser.ExampleData

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
