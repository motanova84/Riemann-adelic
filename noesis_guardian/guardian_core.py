#!/usr/bin/env python3
"""
NOESIS GUARDIAN 3.0 — CORE
Sistema técnico de monitorización y mantenimiento ligero del repositorio.

No es un sistema consciente, ni autónomo en sentido fuerte:
simplemente automatiza chequeos y pequeñas reparaciones estructurales.

Author: José Manuel Mota Burruezo (JMMB Ψ ✧)
System: QCAL–SABIO ∞³

This is the core Guardian module that orchestrates coherency checks
and validation of the QCAL framework.

Features:
- Repository state monitoring
- Spectral validation
- Coherency hooks execution
- Logging and notification
- AIK synchronization (optional)

Security Guarantees:
- ❌ Does NOT modify Lean files
- ❌ Does NOT write to critical files
- ❌ Does NOT create infinite loops
- ❌ Does NOT affect formal proofs
- ✔️ Only executes existing Python code
- ✔️ Captures failures
- ✔️ Records logs
- ✔️ Emits minimal alerts
"""

import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Dict, Optional

# Handle both package import and direct script execution
if __name__ == "__main__":
    sys.path.insert(0, str(Path(__file__).parent.parent))
    from noesis_guardian.modules.coherency_hooks import CoherencyHooks
else:
    from .modules.coherency_hooks import CoherencyHooks

# Log file path for Guardian activity
LOGFILE = "noesis_guardian/logs/guardian_log.json"


class Notifier:
    """Simple notification handler for Guardian alerts."""

    @staticmethod
    def alert(message: str, data: Optional[Dict] = None) -> None:
        """
        Send an alert notification.

        Args:
            message: Alert message
            data: Optional additional data
        """
        print(f"🚨 ALERT: {message}")
        if data:
            # Print summary of hook results
            for title, result in data.items():
                status = "✅" if result.get("ok", False) else "❌"
                print(f"   {status} {title}")


class AikSync:
    """AIK synchronization handler for Guardian entries."""

    @staticmethod
    def emit(entry: Dict) -> None:
        """
        Emit entry to AIK synchronization system.

        Args:
            entry: Guardian entry data
        """
        # Generate AIK hash for entry
        entry_json = json.dumps(entry, sort_keys=True, default=str)
        aik_hash = hashlib.sha256(entry_json.encode()).hexdigest()[:16]
        print(f"🔗 AIK Hash: {aik_hash}")


class NoesisGuardian:
    """
    NOESIS Guardian 3.0 — Core Controller

    Orchestrates validation cycles, coherency checks, and logging
    for the QCAL ∞³ framework.
    """

    def __init__(self, repo_root: Optional[Path] = None):
        """
        Initialize the Guardian.

        Args:
            repo_root: Path to repository root. If None, auto-detected.
        """
        if repo_root:
            self.repo_root = Path(repo_root)
        else:
            # Auto-detect repository root
            self.repo_root = self._find_repo_root()

        self.logs_dir = Path(__file__).parent / "logs"
        self.logs_dir.mkdir(parents=True, exist_ok=True)

        self.log_file = self.logs_dir / "guardian_log.json"
        
        # Initialize components for compatibility with tests
        from .modules.watcher import RepoWatcher
        from .modules.autorepair_engine import AutoRepairEngine
        from .modules.spectral_monitor import SpectralMonitor
        
        self.watcher = RepoWatcher()
        self.repair_engine = AutoRepairEngine()
        self.spectral_monitor = SpectralMonitor()

    @staticmethod
    def _find_repo_root() -> Path:
        """Find the repository root by looking for .git directory."""
        current = Path.cwd()
        while current != current.parent:
            if (current / '.git').exists():
                return current
            current = current.parent
        return Path.cwd()

    def get_repo_state(self) -> Dict[str, Any]:
        """
        Get current repository state information.

        Returns:
            Dictionary with repository state details.
        """
        state = {
            "path": str(self.repo_root),
            "timestamp": datetime.now(timezone.utc).isoformat(),
        }

        try:
            # Get current commit hash
            result = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                state["commit"] = result.stdout.strip()

            # Get current branch
            result = subprocess.run(
                ["git", "rev-parse", "--abbrev-ref", "HEAD"],
                cwd=self.repo_root,
                capture_output=True,
                text=True,
                timeout=10
            )
            if result.returncode == 0:
                state["branch"] = result.stdout.strip()

        except Exception as e:
            state["error"] = str(e)

        return state

    def get_spectral_state(self) -> Dict[str, Any]:
        """
        Get spectral validation state.

        Returns:
            Dictionary with spectral state information.
        """
        state = {
            "base_frequency": 141.7001,  # Hz - QCAL base frequency
            "coherence_constant": 244.36,  # C constant
        }

        # Check for spectral data file
        spectral_file = self.repo_root / "Evac_Rpsi_data.csv"
        if spectral_file.exists():
            state["data_file"] = str(spectral_file)
            state["data_exists"] = True
        else:
            state["data_exists"] = False

        return state

    def run_cycle(self) -> Dict[str, Any]:
        """
        Run a complete Guardian validation cycle.

        Returns:
            Dictionary with complete cycle results.
        """
        print("🧠 NOESIS Guardian 3.0 — Starting cycle...")
        print("=" * 60)

        # Build entry
        entry: Dict[str, Any] = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "version": "3.0.0",
        }

        # Get repository state
        print("\n📂 Checking repository state...")
        entry["repo"] = self.get_repo_state()

        # Get spectral state
        print("\n📊 Checking spectral state...")
        entry["spectral"] = self.get_spectral_state()

        # -------------------------
        #  COHERENCY HOOKS
        # -------------------------
        print("\n🔍 Running coherency hooks...")
        hook_report = CoherencyHooks.run_all()
        entry["hooks"] = hook_report

        # Check for failures
        if any(not h["ok"] for h in hook_report.values()):
            Notifier.alert("❌ Hook de coherencia falló", hook_report)
            AikSync.emit(entry)

        # Save log
        self._save_log(entry)

        print("\n" + "=" * 60)
        print("🧠 Guardian 3.0 ciclo completado.")

        # Print summary
        passed = sum(1 for h in hook_report.values() if h["ok"])
        total = len(hook_report)
        print(f"📈 Hooks: {passed}/{total} passed")

        return entry

    def _save_log(self, entry: Dict[str, Any]) -> None:
        """
        Save entry to log file.

        Args:
            entry: Entry data to save
        """
        # Load existing log or create new
        log_data = []
        if self.log_file.exists():
            try:
                with open(self.log_file, 'r') as f:
                    log_data = json.load(f)
                    if not isinstance(log_data, list):
                        log_data = [log_data]
            except (json.JSONDecodeError, FileNotFoundError):
                log_data = []

        # Append new entry
        log_data.append(entry)

        # Keep only last 100 entries
        log_data = log_data[-100:]

        # Save
        with open(self.log_file, 'w') as f:
            json.dump(log_data, f, indent=2, default=str)

        print(f"📝 Log saved to: {self.log_file}")

    def run(self) -> Dict[str, Any]:
        """
        Run the Guardian and produce a log entry.
        
        This is an alias for run_cycle() for backward compatibility.
        
        Returns:
            Dictionary with complete cycle results.
        """
        entry = {
            "timestamp": datetime.now(timezone.utc).isoformat(),
            "repo": self.get_repo_state(),
            "spectral": self.spectral_monitor.check(),
        }
        return entry

    def log(self, entry: Dict[str, Any]) -> None:
        """
        Log an entry to the log file.
        
        Args:
            entry: Entry data to log
        """
        self._save_log(entry)


def main():
    """Main entry point for Guardian execution."""
    guardian = NoesisGuardian()
    result = guardian.run_cycle()

    # Exit with appropriate code
    hooks = result.get("hooks", {})
    all_passed = all(h.get("ok", False) for h in hooks.values())

    sys.exit(0 if all_passed else 1)


if __name__ == "__main__":
    main()

