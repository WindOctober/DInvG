#!/bin/bash

# Create temporary directory
mkdir -p ./tmp/output

# Initialize counter for files with differences
diff_count=0

# Iterate over all .in files in Benchmark/in directory
for file in ./Benchmark/in/*.in
do
  # Get the base name of the file (no path or extension)
  base=$(basename "$file" .in)
  echo $file
  # Run the binaries and redirect output to temporary directory
  ./bin/origin newdfs_seq_propagation < "$file" | sed -n '/< < < compute_invariants_by_propagation_with_farkas()/,/Status after Solver:/p' > "./tmp/output/${base}_origin.out"
  ./bin/lstingX newdfs_seq_propagation < "$file" | sed -n '/< < < compute_invariants_by_propagation_with_farkas()/,/Status after Solver:/p' > "./tmp/output/${base}_lstingX.out"
  
  # Compare output files and store the result in a diff file
  diff_output=$(diff -y --suppress-common-lines "./tmp/output/${base}_origin.out" "./tmp/output/${base}_lstingX.out")
  if [ -n "$diff_output" ]; then
    echo "$diff_output" > "./tmp/output/${base}_diff.out"
    echo "Difference found in file: $file"
    diff_count=$((diff_count+1))
  fi
done

# Print the total count of files with differences
echo "Total files with differences: $diff_count"
