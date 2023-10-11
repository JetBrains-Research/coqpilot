#!/bin/bash

# Git config directory
directory=~/.config/git

# Check if the directory exists
if [ ! -d "$directory" ]; then
    # If not, create directory
    echo "Git directory not found. Creating..."
    mkdir $directory
else
    echo "Git directory exists."
fi

# Navigate to the directory
cd $directory

# Check if ignore file exists
if [ ! -f "ignore" ]; then
    # If not, create file
    echo "Ignore file not found. Creating..."
    touch ignore
else
    echo "Ignore file exists."
fi

# Append the string to the file
echo "Appending string to the file..."
echo "*_cp_aux.v" >> ignore

# Display the contents of the file
echo "Contents of the ignore file:"
cat ignore