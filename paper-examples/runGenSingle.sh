#!/bin/bash

# Path to the input file
input_file=$(realpath "$1")

# Extract the file name from the path
file_name=$(basename "$input_file")

# Define the program command (replace this with the actual command if necessary)
program="RUN_PROGRAM_WITH_OUTPUT_PATH" # Make sure to replace this with the actual program command

# Match the file name and execute the corresponding command
case "$file_name" in
    "race-v1.program")
        $program "$input_file" -tab:1 -termination -m:40
        ;;
    "race-v2.program")
        $program "$input_file" -tab:1 -concentration -m:40
        ;;
    "pd-v1.program")
        $program "$input_file" -tab:1 -direct -solver:SDP
        ;;
    "pdmb-v3.program"|"pdmb-v4.program")
        $program "$input_file" -tab:1 -termination -degree:4
        ;;
    "birth.program")
        $program "$input_file" -tab:1 -termination -m:40 -Rp_lambda:0~2 -Rp_time:0~10
        ;;
    "rdwalk-v1.program"|"rdwalk-v2.program"|"rdwalk-v3.program"|"rdwalk-v4.program")
        $program "$input_file" -tab:1 -termination
        ;;
    "para-estimation-recursive.program")
        $program "$input_file" -tab:2 -direct -acc 1e-5 -Rp_p:0~1 -Rp_t:-inf~inf -degree:8
        ;;
    "pd-beta-v1.program"|"pd-beta-v2.program"|"pd-beta-v3.program"|"pd-beta-v4.program"|"pdld.program"|"pdmb-v5.program"|"pd.program")
        $program "$input_file" -tab:2 -direct -acc 1e-4
        ;;
    "pd.program")
        $program "$input_file" -tab:2 -direct -acc 1e-4 -m:60 -degree:10 -solver:SDP
        ;;
    "add-uni-Q1.program"|"add-uni-Q2.program")
        $program "$input_file" -tab:3 -no_truncate -direct -Rp_x:0~1 -Rp_y:0~1 -int:p_y
        ;;
    "cav-ex-5-Q1.program"|"cav-ex-5-Q2.program"|"cav-ex-7-Q1.program"|"cav-ex-7-Q2.program")
        $program "$input_file" -tab:3 -no_truncate -direct -m:10 -Rp_money:10~20 -Rp_i:0~20
        ;;
    "growing-walk-Q1.program"|"growing-walk-Q2.program")
        $program "$input_file" -tab:3 -no_truncate -direct -acc 1e-4 -Rp_t:0~0.1 -Rp_x:1~10 -degree:8
        ;;
    "random-box-walk-Q1.program")
        $program "$input_file" -tab:3 -no_truncate -direct -Rp_x:-0.8~0.8 -Rp_t:0~10 -degree:4
        ;;
    *)
        echo "No matching program for $file_name"
        ;;
esac
