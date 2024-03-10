#!/bin/bash

cd "Table 1 (fix birth)/parser-inputs1/"

program="dotnet ../../../ProgramAnalyser/bin/Debug/net8.0/ProgramAnalyser.dll -O ../output"

$program -tab:1 h-t-r-2-3.program -termination -m:40
$program -tab:1 h-t-r-2-3-inside-score.program -concentration -m:40
$program -tab:1 pedestrian-beta.program -direct -solver:SDP
$program -tab:1 pedestrian-multiple-branches-v3.program -termination -degree:4
$program -tab:1 pedestrian-multiple-branches-v4.program -termination -degree:4
$program -tab:1 phylogenetic-model.program -termination -m:40 -Rp_lambda:0~2 -Rp_time:0~10
$program -tab:1 random-walk-beta-inside-scorey-v1.program -termination
$program -tab:1 random-walk-beta-inside-scorey-v2.program -termination
$program -tab:1 random-walk-beta-inside-scorey-v3.program -termination
$program -tab:1 random-walk-beta-inside-scorey-v4.program -termination
