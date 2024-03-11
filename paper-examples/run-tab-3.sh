#!/bin/bash

cd "Table 3 (fix add-uniform & random-walk)/parser-inputs3/"

program="dotnet ../../../ProgramAnalyser/bin/Debug/net8.0/ProgramAnalyser.dll -O ../output -tab:3"

$program add-uniform-unbounded-Q1.program -no_truncate -direct -Rp_x:0~1 -Rp_y:0~1 -int:p_y
$program add-uniform-unbounded-Q2.program -no_truncate -direct -Rp_x:0~1 -Rp_y:0~1 -int:p_y
$program cav-example-5-Q1.program -no_truncate -direct -m:10 -Rp_money:10~20 -Rp_i:0~20
$program cav-example-5-Q2.program -no_truncate -direct -m:10 -Rp_money:10~20 -Rp_i:0~20
$program cav-example-7-Q1.program -no_truncate -direct -Rp_count:0~30 -Rp_i:0~4
$program cav-example-7-Q2.program -no_truncate -direct -Rp_count:0~30 -Rp_i:0~4
$program growing-walk-Q1.program -no_truncate -direct -acc 1e-4 -Rp_t:0~0.1 -Rp_x:1~10 -degree:8
$program growing-walk-Q2.program -no_truncate -direct -acc 1e-4 -Rp_t:0~0.1 -Rp_x:1~10 -degree:8
$program random-box-walk-Q1.program -no_truncate -direct -Rp_x:-0.8~0.8 -Rp_t:0~10 -degree:4
