#!/bin/bash
#
# Setup script for rhval global alias
#
# This script helps configure the global 'rhval' command that can be executed
# from any directory to run the V5 Coronación validation.
#

echo "🔧 Setting up rhval global alias..."
echo

# Get the current repository path
REPO_PATH="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
RHVAL_SCRIPT="$REPO_PATH/rhval.sh"

echo "Repository path: $REPO_PATH"
echo "rhval script: $RHVAL_SCRIPT"
echo

# Check if the rhval.sh script exists
if [ ! -f "$RHVAL_SCRIPT" ]; then
    echo "❌ Error: rhval.sh script not found!"
    exit 1
fi

# Make sure the script is executable
chmod +x "$RHVAL_SCRIPT"

# Generate the alias command
ALIAS_COMMAND="alias rhval=\"$RHVAL_SCRIPT\""

echo "🔧 To set up the global rhval alias, add the following line to your ~/.zshrc:"
echo
echo "    $ALIAS_COMMAND"
echo
echo "📋 You can do this by running:"
echo "    echo '$ALIAS_COMMAND' >> ~/.zshrc"
echo "    source ~/.zshrc"
echo
echo "✅ After setup, you can run 'rhval' from any directory!"
echo "   This will execute: python3 validate_v5_coronacion.py --precision 15"
echo

# Offer to automatically add to ~/.zshrc if it exists
if [ -f "$HOME/.zshrc" ]; then
    read -p "🤔 Would you like to automatically add the alias to ~/.zshrc? (y/N): " -n 1 -r
    echo
    if [[ $REPLY =~ ^[Yy]$ ]]; then
        # Check if alias already exists
        if grep -q "alias rhval=" "$HOME/.zshrc"; then
            echo "⚠️  rhval alias already exists in ~/.zshrc"
            echo "   You may need to update it manually if the path changed."
        else
            echo "$ALIAS_COMMAND" >> "$HOME/.zshrc"
            echo "✅ Added rhval alias to ~/.zshrc"
            echo "   Run 'source ~/.zshrc' or restart your terminal to use it."
        fi
    else
        echo "📝 Manual setup required. Please add the alias command above to your ~/.zshrc"
    fi
else
    echo "📝 ~/.zshrc not found. Please create it and add the alias command above."
fi

echo
echo "🏆 Setup complete! Once configured, 'rhval' will run:"
echo "   V5 CORONACIÓN: COMPLETE RIEMANN HYPOTHESIS PROOF VALIDATION"