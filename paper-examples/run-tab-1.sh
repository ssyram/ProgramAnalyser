#!/bin/bash

cd "Table 1 (fix birth)/parser-inputs1/"

program="dotnet ../../../ProgramAnalyser/bin/Debug/net8.0/ProgramAnalyser.dll -O ../output"

$program h-t-r-2-3.program -concentration -m:40
$program h-t-r-2-3-inside-score.program -concentration -m:40
$program pedestrian-beta.program -direct
$program pedestrian-multiple-branches-v3.program -termination -degree:4
$program pedestrian-multiple-branches-v4.program -termination -degree:4
$program phylogenetic-model.program -no_truncate -termination -m:40 -Rp_lambda:0~2 -Rp_time:0~10
$program random-walk-beta-inside-scorey-v1.program -termination
$program random-walk-beta-inside-scorey-v2.program -termination
$program random-walk-beta-inside-scorey-v3.program -termination
$program random-walk-beta-inside-scorey-v4.program -termination
