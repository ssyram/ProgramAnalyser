#!/bin/bash

# Check if exactly three arguments are given
if [ "$#" -ne 3 ]; then
    echo "Usage: $0 <target_directory> <original_name> <target_name>"
    exit 1
fi

# Assign arguments to variables
target_directory=$1
original_name=$2
target_name=$3

# Check if the target directory exists
if [ ! -d "$target_directory" ]; then
  echo "Error: Target directory '$target_directory' does not exist."
  exit 1
fi

# Change to the target directory
cd "$target_directory"

# Loop through all files that start with the original name
for file in ${original_name}.*; do
  # Extract the part of the filename after the first "."
  rest_of_name=${file#*.}
  # Rename the file
  mv "$file" "$target_name.$rest_of_name"
done

echo "Renaming completed."
