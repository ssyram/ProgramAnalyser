#!/bin/bash

# Directory to read files from
directory="$1"

# File to append filenames to
output_file="$2"

# Check if directory is provided
if [ -z "$directory" ]; then
    echo "No directory provided. Please specify a directory."
    exit 1
fi

# Check if output file is provided
if [ -z "$output_file" ]; then
    echo "No output file provided. Please specify an output file."
    exit 1
fi

# Iterate through all files in the directory
for file in "$directory"/*; do
    # Check if the file has a .program extension
    if [[ "$file" == *.program ]]; then
        # Append the filename to the output file
        echo "$(basename "$file")" >> "$output_file"
    fi
done

echo "Filenames with .program extension have been appended to $output_file"
