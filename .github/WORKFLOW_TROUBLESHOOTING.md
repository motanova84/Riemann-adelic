# GitHub Actions Workflow Troubleshooting Guide

## Branch Reference Issues

### Problem: "fatal: couldn't find remote ref refs/heads/[branch-name]"

This error occurs when a workflow attempts to checkout a branch that doesn't exist on the remote repository.

#### Common Causes:

1. **Scheduled workflows**: When a workflow runs on a schedule, it needs an explicit branch reference
2. **Manual triggers**: When manually triggering a workflow, ensure the selected branch exists
3. **Deleted branches**: A branch was deleted but workflows still reference it
4. **Typos**: Incorrect branch name in workflow configuration

#### Solution:

For **scheduled workflows**, always specify an explicit branch in the checkout action:

```yaml
steps:
  - uses: actions/checkout@v4
    with:
      ref: main  # Explicitly checkout main branch for scheduled runs
```

For **manual triggers** (workflow_dispatch), the workflow will use the branch from which it was triggered. Make sure you're triggering from an existing branch.

For **push/pull_request triggers**, the checkout action automatically uses the branch that triggered the workflow.

### Workflows Fixed in This Repository

The following workflows have been updated to explicitly checkout the `main` branch for scheduled runs:

1. `auto_evolution.yml` - Runs every 12 hours
2. `auto_publish.yml` - Runs monthly
3. `monitor.yml` - Runs daily
4. `notebooks.yml` - Runs weekly on Mondays
5. `performance-benchmark.yml` - Runs weekly on Sundays (4 jobs)
6. `production-qcal.yml` - Runs every 4 hours
7. `qcal-auto-evolution.yml` - Runs daily at 3 AM UTC
8. `rh-ds-validation.yml` - Runs weekly on Mondays (2 jobs)
9. `status.yml` - Runs daily

### Best Practices

1. **For scheduled workflows**: Always use `ref: main` (or your default branch)
2. **For event-triggered workflows**: Let checkout use the default (triggering branch)
3. **For manual workflows**: Consider adding a branch input parameter if needed:

```yaml
on:
  workflow_dispatch:
    inputs:
      branch:
        description: 'Branch to checkout'
        required: false
        default: 'main'
        type: string

jobs:
  my-job:
    steps:
      - uses: actions/checkout@v4
        with:
          ref: ${{ inputs.branch || 'main' }}
```

### Checking Available Branches

To verify which branches exist on your repository:

```bash
# List all remote branches
git branch -r

# List all branches (local and remote)
git branch -a

# Fetch latest branches from remote
git fetch --all
```

### Workflow Trigger Patterns

Our repository uses these branch patterns in workflow triggers:

- `main` - Main stable branch
- `develop` - Development branch
- `copilot/**` - All copilot branches
- `copilot/fix-**` - Copilot fix branches specifically

Make sure your branch matches these patterns if you want workflows to trigger automatically.

## Additional Resources

- [GitHub Actions documentation](https://docs.github.com/en/actions)
- [actions/checkout documentation](https://github.com/actions/checkout)
- Repository branch protection rules: `.github/branch-protection.md`
- Copilot instructions: `.github/copilot-instructions.md`

---

**Last Updated**: 2025-11-17  
**Issue Reference**: Fixed branch reference errors for scheduled workflows
