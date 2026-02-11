#!/usr/bin/env python3
"""
Check AI Comment for Problematic Suggestions
=============================================

This script is called by the Noesis Guardian workflow to check
GitHub comments for problematic normalization suggestions.

It reads environment variables set by the workflow and exits
with code 1 if intervention is needed.
"""

import os
import sys

# Add repo root to path
sys.path.insert(0, '.')

from consciousness.noesis_sentinel_bot import NoesisSentinel


def main():
    """Check AI comment for problematic patterns."""
    # Get environment variables
    author = os.environ.get('COMMENT_AUTHOR', 'unknown')
    comment = os.environ.get('COMMENT_BODY', '')
    pr_number = os.environ.get('PR_NUMBER', '')
    repo = os.environ.get('GITHUB_REPOSITORY', '')
    
    # Initialize sentinel
    sentinel = NoesisSentinel()
    
    # Scan comment
    result = sentinel.scan_comment(author, comment, {
        'pr': pr_number,
        'repo': repo
    })
    
    # If intervention needed, write response and exit with error
    if result['intervention_needed']:
        print('INTERVENTION_NEEDED=true')
        with open('noesis_response.txt', 'w') as f:
            f.write(result['response'])
        sys.exit(1)
    else:
        print('INTERVENTION_NEEDED=false')
        sys.exit(0)


if __name__ == '__main__':
    main()
