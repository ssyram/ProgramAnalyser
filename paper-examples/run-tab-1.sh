#!/bin/bash

cd "Table 1 (fix birth)/parser-inputs1/"

program="dotnet ../../../ProgramAnalyser/bin/Debug/net8.0/ProgramAnalyser.dll -O ../pt-inputs1 -tab:1"

$program race-v1.program -termination -m:40
$program race-v2.program -concentration -m:40
$program pd-v1.program -direct -solver:SDP
$program pdmb-v3.program -termination -degree:4
$program pdmb-v4.program -termination -degree:4
$program birth.program -termination -m:40 -Rp_lambda:0~2 -Rp_time:0~10
$program rdwalk-v1.program -termination
$program rdwalk-v2.program -termination
$program rdwalk-v3.program -termination
$program rdwalk-v4.program -termination
