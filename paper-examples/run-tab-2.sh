#!/bin/bash

cd "Table 2 (fix para-recur)/parser-inputs2/"

program="dotnet ../../../ProgramAnalyser/bin/Debug/net8.0/ProgramAnalyser.dll -O ../output"

$program -tab:2 para-estimation-recursive.program -no_truncate -direct -acc 1e-5 -Rp_p:0~1 -Rp_t:0~10 -degree:8
$program -tab:2 pedestrian-beta-inside-v1.program -direct -acc 1e-4
$program -tab:2 pedestrian-beta-inside-v2.program -direct -acc 1e-4
$program -tab:2 pedestrian-beta-inside-v3.program -direct -acc 1e-4
$program -tab:2 pedestrian-beta-inside-v4.program -direct -acc 1e-4
$program -tab:2 pedestrian-deviation5.program -direct -acc 1e-4
$program -tab:2 pedestrian-multiple-branches-v5.program -direct -acc 1e-4
$program -tab:2 pedestrian.program -direct -acc 1e-4 -m:90 -degree:10 -solver:SDP
