#!/bin/sh

# Check if git is installed
if ! command -v git >/dev/null 2>&1; then
    echo "Error: git not found. Please ensure git is installed and in your PATH."
    exit 1
fi

# Check if there are any uncommitted changes
if ! git diff --exit-code >/dev/null; then
    # Run 'git add .'
    echo "Adding all files to the staging area..."
    git add . || { echo "Error: Unable to add files to the staging area."; exit 1; }

    # Get the current system time as the commit message
    commit_message=$(date)

    # Run 'git commit'
    echo "Creating a new commit..."
    git commit -m "${commit_message}" || { echo "Error: Unable to create a new commit."; exit 1; }
fi

# Run 'git push'
echo "Pushing changes to GitHub..."
git push || { echo "Error: Unable to push changes to GitHub."; exit 1; }

echo "One-click upload script completed!"
