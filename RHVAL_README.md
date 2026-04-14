# rhval - Global Riemann Hypothesis Validation Command

This repository provides a global `rhval` command that can be executed from any directory to run the complete V5 Coronación validation of the Riemann Hypothesis proof framework.

## Quick Setup

### Automatic Setup (Recommended)

Run the setup script:
```bash
./setup_rhval.sh
```

This will guide you through the process and optionally add the alias to your `~/.zshrc` automatically.

### Manual Setup

1. Add the following line to your `~/.zshrc`:
```bash
alias rhval="cd ~/path/to/Riemann-Adelic && python3 validate_v5_coronacion.py --precision 15"
```

Replace `~/path/to/Riemann-Adelic` with the actual path to this repository.

2. Reload your shell configuration:
```bash
source ~/.zshrc
```

### Alternative: Direct Script Execution

You can also create a global alias using the provided script:
```bash
alias rhval="/full/path/to/repository/rhval.sh"
```

## Usage

Once configured, simply run from any directory:
```bash
rhval
```

This will automatically:
- Change to the repository directory
- Execute `python3 validate_v5_coronacion.py --precision 15`
- Display the complete validation results

## Expected Output

When you run `rhval`, you should see output similar to:

```
🏆 V5 CORONACIÓN: COMPLETE SUCCESS!
✨ The Riemann Hypothesis proof framework is fully verified!
```

The command performs comprehensive validation including:
- Axioms → Lemmas verification
- Archimedean rigidity derivation
- Paley-Wiener uniqueness identification
- Zero localization via dual routes
- Complete coronación integration

## Files

- `rhval.sh` - The main script that executes the validation
- `setup_rhval.sh` - Setup helper script for configuring the global alias
- `RHVAL_README.md` - This documentation file

## Troubleshooting

If the `rhval` command is not found:
1. Make sure you added the alias to `~/.zshrc` (not `.bashrc` or other shell configs)
2. Run `source ~/.zshrc` to reload the configuration
3. Ensure the script paths are correct and the files are executable

If you're using a different shell (bash, fish, etc.), add the alias to the appropriate configuration file (.bashrc, config.fish, etc.).