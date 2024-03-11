#!/bin/bash

cd "Table 2 (fix para-recur)/parser-inputs2/"

program="dotnet ../../../ProgramAnalyser/bin/Debug/net8.0/ProgramAnalyser.dll -O ../output -tab:2"

$program para-estimation-recursive.program -direct -acc 1e-5 -Rp_p:0~1 -Rp_t:-inf~inf -degree:8
$program pd-beta-v1.program -direct -acc 1e-4
$program pd-beta-v2.program -direct -acc 1e-4
$program pd-beta-v3.program -direct -acc 1e-4
$program pd-beta-v4.program -direct -acc 1e-4
$program pdld.program -direct -acc 1e-4
$program pdmb-v5.program -direct -acc 1e-4
$program pd.program -direct -acc 1e-4 -m:60 -degree:10 -solver:SDP
