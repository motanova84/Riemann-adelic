#!/usr/bin/env python3
"""
🔔 Notification Manager - QCAL ∞³ Unified Notification System
==============================================================

Manages notifications across Discord, Slack, and other platforms.
Provides unified interface for system alerts and status updates.

Frequency: 141.7001 Hz
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Optional, Dict, List
from datetime import datetime


class NotificationManager:
    """Unified notification manager for QCAL system"""
    
    def __init__(self, config_path: Optional[str] = None):
        self.config = self._load_config(config_path)
        self.notifiers = {}
        self._initialize_notifiers()
    
    def _load_config(self, config_path: Optional[str]) -> Dict:
        """Load notification configuration"""
        default_config = {
            "discord": {"enabled": True},
            "slack": {"enabled": True},
            "coherence_threshold": 0.888,
            "alert_on_drop": True
        }
        
        if config_path and Path(config_path).exists():
            with open(config_path, 'r') as f:
                loaded_config = json.load(f)
                default_config.update(loaded_config)
        
        return default_config
    
    def _initialize_notifiers(self):
        """Initialize configured notifiers"""
        # Try to import and initialize Discord notifier
        if self.config["discord"]["enabled"]:
            try:
                from .discord_notifier import DiscordNotifier
                self.notifiers["discord"] = DiscordNotifier()
            except Exception as e:
                print(f"Discord notifier not available: {e}")
        
        # Try to import and initialize Slack notifier
        if self.config["slack"]["enabled"]:
            try:
                from .slack_notifier import SlackNotifier
                self.notifiers["slack"] = SlackNotifier()
            except Exception as e:
                print(f"Slack notifier not available: {e}")
    
    def notify_all(self, notification_type: str, **kwargs) -> Dict[str, bool]:
        """
        Send notification to all enabled platforms.
        
        Args:
            notification_type: Type of notification
            **kwargs: Notification-specific parameters
        
        Returns:
            Dictionary with platform: success status
        """
        results = {}
        
        for platform, notifier in self.notifiers.items():
            try:
                if notification_type == "validation_complete":
                    success = notifier.notify_validation_complete(**kwargs)
                elif notification_type == "coherence_drop":
                    success = notifier.notify_coherence_drop(**kwargs)
                elif notification_type == "agent_status":
                    success = notifier.notify_agent_status(**kwargs)
                else:
                    success = False
                
                results[platform] = success
            except Exception as e:
                print(f"Failed to notify {platform}: {e}")
                results[platform] = False
        
        return results
    
    def check_coherence_and_alert(self, coherence: float) -> bool:
        """
        Check coherence and send alert if below threshold.
        
        Args:
            coherence: Current coherence value
        
        Returns:
            True if alert was sent, False otherwise
        """
        threshold = self.config["coherence_threshold"]
        
        if coherence < threshold and self.config["alert_on_drop"]:
            results = self.notify_all(
                "coherence_drop",
                coherence=coherence,
                threshold=threshold
            )
            return any(results.values())
        
        return False
    
    def get_status(self) -> Dict:
        """Get notification system status"""
        return {
            "manager": "initialized",
            "enabled_platforms": list(self.notifiers.keys()),
            "config": self.config,
            "timestamp": datetime.utcnow().isoformat()
        }


def main():
    """Command-line interface for notification manager"""
    parser = argparse.ArgumentParser(
        description="🔔 QCAL Notification Manager"
    )
    parser.add_argument(
        "--config",
        type=str,
        help="Path to configuration file"
    )
    parser.add_argument(
        "--test-validation",
        action="store_true",
        help="Send test validation notification"
    )
    parser.add_argument(
        "--test-alert",
        action="store_true",
        help="Send test coherence alert"
    )
    parser.add_argument(
        "--manager-status",
        action="store_true",
        help="Show manager status"
    )
    
    args = parser.parse_args()
    
    # Initialize manager
    manager = NotificationManager(args.config)
    
    if args.manager_status:
        status = manager.get_status()
        print(json.dumps(status, indent=2))
        return 0
    
    if args.test_validation:
        print("📤 Sending test validation notification...")
        results = manager.notify_all(
            "validation_complete",
            coherence=0.936,
            tests_passed=5,
            tests_total=5
        )
        print(f"Results: {results}")
        return 0
    
    if args.test_alert:
        print("🚨 Sending test coherence alert...")
        results = manager.notify_all(
            "coherence_drop",
            coherence=0.742,
            threshold=0.888
        )
        print(f"Results: {results}")
        return 0
    
    parser.print_help()
    return 0


if __name__ == "__main__":
    sys.exit(main())
