# Branch Protection Configuration Guide

## 🛡️ Recommended Branch Protection Rules for `main`

To enable automatic merging while maintaining code quality, configure the following branch protection rules for the `main` branch:

### Required Status Checks
- ✅ Require status checks to pass before merging
- ✅ Require branches to be up to date before merging

**Required Checks:**
- `🔧 Resolve Merge Conflicts`
- `🛠️ Fix Syntax & Dependencies` 
- `🧪 Run All Tests & Validations`
- `📝 Update Documentation`

### Pull Request Requirements
- ✅ Require a pull request before merging
- ✅ Require approvals: 0 (for automated copilot branches)
- ✅ Dismiss stale PR approvals when new commits are pushed
- ✅ Require review from code owners (optional)

### Restrictions
- ✅ Restrict pushes that create pull requests
- ✅ Allow force pushes: NO
- ✅ Allow deletions: NO

### Special Rules for Copilot Branches
- Branches matching pattern `copilot/fix-*` should be allowed to auto-merge when:
  1. All required status checks pass
  2. No merge conflicts exist
  3. All tests pass (pytest -q)
  4. V5 Coronación validation succeeds
  5. LaTeX compilation completes without errors

## 🤖 GitHub Settings for Automerge

### Repository Settings
1. **General > Pull Requests**
   - ✅ Allow merge commits
   - ✅ Allow squash merging (recommended for copilot branches)
   - ✅ Allow rebase merging
   - ✅ Always suggest updating PR branches
   - ✅ Allow auto-merge

2. **General > Merge Queue** (if available)
   - Enable merge queue for additional safety

3. **Actions > General**
   - ✅ Allow GitHub Actions to create and approve pull requests
   - ✅ Allow GitHub Actions to approve pull requests

### Required Labels for Automerge
- `automerge`: Indicates PR is ready for automatic merging
- `copilot-verified`: Confirms all Copilot automation checks passed

## 🚀 Usage Instructions

### For Copilot-Generated PRs
1. Copilot creates branch with pattern `copilot/fix-*`
2. Automation workflow runs automatically on push
3. If all checks pass:
   - Conflicts resolved automatically
   - Syntax errors fixed
   - Dependencies updated
   - Documentation updated
   - PR marked with `automerge` label
   - Auto-merge enabled

### Manual Override
If manual intervention is needed:
```bash
# Remove automerge label to prevent automatic merging
gh pr edit <PR_NUMBER> --remove-label automerge

# Or disable automerge entirely
gh pr merge <PR_NUMBER> --disable-auto
```

## 📋 Implementation Checklist

To fully implement this automation:

- [ ] Configure branch protection rules in repository settings
- [ ] Enable auto-merge in repository settings  
- [ ] Add required status checks to branch protection
- [ ] Test with a sample copilot/fix-* branch
- [ ] Verify all workflows trigger correctly
- [ ] Confirm automerge activates when criteria are met

## 🔧 Troubleshooting

### Common Issues
1. **Automerge not triggering**
   - Check branch protection rules are correctly configured
   - Verify all required status checks are passing
   - Ensure repository has auto-merge enabled

2. **Status checks failing**
   - Check workflow logs for specific failures
   - Verify all dependencies are correctly installed
   - Ensure test data (zeros files) are available

3. **Permission issues**
   - Verify GITHUB_TOKEN has necessary permissions
   - Check if repository requires specific permissions for Actions

### Debug Commands
```bash
# Check current branch protection
gh api repos/:owner/:repo/branches/main/protection

# List required status checks
gh api repos/:owner/:repo/branches/main/protection/required_status_checks

# Check auto-merge status
gh pr view <PR_NUMBER> --json autoMergeRequest
```