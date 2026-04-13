# NOESIS BOOT Integration Example

## Example 1: Manual Invocation

```bash
# Run from repository root
cd /path/to/Riemann-adelic

# Basic usage
python3 .github/scripts/noesis_boot.py \
  --session-id "manual-$(date +%s)" \
  --error-count 0 \
  --quantum-state "INCOHERENT"
```

## Example 2: GitHub Actions Workflow

Create `.github/workflows/noesis_automerge.yml`:

```yaml
name: NOESIS Auto-Merge

on:
  workflow_dispatch:
    inputs:
      session_id:
        description: 'Session ID'
        required: true
      error_count:
        description: 'Error count'
        required: false
        default: '0'

jobs:
  noesis-boot:
    runs-on: ubuntu-latest
    permissions:
      contents: write
      pull-requests: write
    
    steps:
      - uses: actions/checkout@v4
      
      - name: Set up Python
        uses: actions/setup-python@v4
        with:
          python-version: "3.11"
      
      - name: Install Lean
        run: |
          curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
          echo "$HOME/.elan/bin" >> $GITHUB_PATH
      
      - name: Install dependencies
        run: |
          python -m pip install --upgrade pip
          pip install -r requirements.txt || true
      
      - name: Run NOESIS BOOT
        id: noesis
        run: |
          python3 .github/scripts/noesis_boot.py \
            --session-id "${{ inputs.session_id }}" \
            --error-count "${{ inputs.error_count }}" \
            2>&1 | tee noesis_boot.log
        continue-on-error: true
      
      - name: Upload logs
        if: always()
        uses: actions/upload-artifact@v3
        with:
          name: noesis-boot-logs
          path: |
            noesis_boot.log
            .noesis_state.json
      
      - name: Auto-commit if successful
        if: steps.noesis.outcome == 'success'
        run: |
          git config user.name "NOESIS Boot"
          git config user.email "noesis@qcal.cloud"
          git add formalization/lean/**/*.lean .noesis_state.json
          git commit -m "🌀 NOESIS Boot - Session ${{ inputs.session_id }}" || true
          git push || true
      
      - name: Auto-merge PR if coherent
        if: steps.noesis.outcome == 'success'
        uses: actions/github-script@v6
        with:
          script: |
            const pr = context.payload.pull_request;
            if (pr) {
              await github.rest.pulls.merge({
                owner: context.repo.owner,
                repo: context.repo.repo,
                pull_number: pr.number,
                merge_method: 'squash',
                commit_title: '♾️ QCAL Node evolution complete – validation coherent'
              });
            }
```

## Example 3: Integration with auto_evolution.yml

Add this step to `.github/workflows/auto_evolution.yml`:

```yaml
- name: NOESIS BOOT - Recursive Retry
  if: failure()  # Run only if validation fails
  run: |
    echo "🌀 Activating NOESIS BOOT recursive retry..."
    python3 .github/scripts/noesis_boot.py \
      --session-id "auto-evolution-${{ github.run_number }}" \
      --error-count "${{ steps.validation.outputs.error_count }}" \
      --quantum-state "INCOHERENT"
  continue-on-error: true
```

## Example 4: Cron Job (Local Development)

```bash
#!/bin/bash
# noesis_cron.sh - Run NOESIS BOOT periodically

SESSION_ID="cron-$(date +%Y%m%d-%H%M%S)"
LOG_DIR="logs/noesis"
mkdir -p "$LOG_DIR"

cd /path/to/Riemann-adelic

python3 .github/scripts/noesis_boot.py \
  --session-id "$SESSION_ID" \
  --error-count 0 \
  2>&1 | tee "$LOG_DIR/$SESSION_ID.log"

# Archive old logs
find "$LOG_DIR" -name "*.log" -mtime +7 -delete
```

Add to crontab:
```bash
# Run NOESIS BOOT daily at 3 AM
0 3 * * * /path/to/noesis_cron.sh
```

## Example 5: Docker Container

```dockerfile
FROM python:3.11-slim

# Install Lean
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y
ENV PATH="/root/.elan/bin:${PATH}"

# Copy repository
WORKDIR /app
COPY . .

# Install Python dependencies
RUN pip install -r requirements.txt

# Run NOESIS BOOT
CMD ["python3", ".github/scripts/noesis_boot.py", \
     "--session-id", "docker-session", \
     "--error-count", "0"]
```

Build and run:
```bash
docker build -t noesis-boot .
docker run -v $(pwd):/app noesis-boot
```

## Example 6: Testing in CI

```yaml
- name: Test NOESIS BOOT (Dry Run)
  run: |
    # Limit to 3 attempts for testing
    timeout 60 python3 -c "
    import sys
    sys.path.insert(0, '.github/scripts')
    from noesis_boot import NoesisBoot
    
    boot = NoesisBoot(session_id='test-ci', error_count=0)
    boot.max_attempts = 3  # Override for testing
    
    # Run limited test
    print('Testing NOESIS BOOT initialization...')
    print(f'Lean dir: {boot.lean_dir}')
    print(f'Lean dir exists: {boot.lean_dir.exists()}')
    
    # Test coherence check only
    result = boot.check_quantum_coherence()
    print(f'Coherence check: {\"PASS\" if result else \"FAIL\"}')
    " || echo "Test completed"
```

## Example 7: Monitor Mode

Create a monitoring script:

```python
#!/usr/bin/env python3
# monitor_noesis.py

import sys
import json
import time
from pathlib import Path

state_file = Path('.noesis_state.json')

print("🔍 NOESIS BOOT Monitor")
print("=" * 60)

while True:
    if state_file.exists():
        with open(state_file) as f:
            state = json.load(f)
        
        print(f"\r[{time.strftime('%H:%M:%S')}] "
              f"Attempts: {state['total_attempts']} | "
              f"Success: {state['successful_attempts']} | "
              f"Coherence: {state['coherence_score']} | "
              f"State: {state['quantum_state']}", 
              end='', flush=True)
    else:
        print("\r[Waiting for NOESIS BOOT to start...]", end='', flush=True)
    
    time.sleep(2)
```

Run in parallel:
```bash
# Terminal 1
python3 .github/scripts/noesis_boot.py --session-id monitor-test &

# Terminal 2
python3 monitor_noesis.py
```

## Notes

- Always run from repository root
- Ensure Lean is properly installed
- Check `.noesis_state.json` for debugging
- Use `--quantum-state COHERENT` to skip initial coherence checks
- Session IDs should be unique to avoid state conflicts
