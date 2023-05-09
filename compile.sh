#!/bin/sh

# Check if cmake is installed
if ! command -v cmake >/dev/null 2>&1; then
    echo "Error: cmake not found. Please ensure cmake is installed and in your PATH."
    exit 1
fi

# Check if make is installed
if ! command -v make >/dev/null 2>&1; then
    echo "Error: make not found. Please ensure make is installed and in your PATH."
    exit 1
fi

# Create a build directory if it doesn't exist
if [ ! -d "build" ]; then
    echo "Creating build directory..."
    mkdir build || { echo "Error: Unable to create build directory."; exit 1; }
fi

# Change to the build directory
cd build

# Run cmake
echo "Running cmake..."
cmake .. || { echo "Error: cmake failed."; exit 1; }

# Run make
echo "Running make..."
make || { echo "Error: make failed."; exit 1; }

echo "Build completed successfully!"

# Return to the root directory
cd ..
