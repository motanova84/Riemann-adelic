#!/usr/bin/env python3
"""
🔔 Discord Notifier - QCAL ∞³ Notification System
=================================================

Sends rich notifications to Discord channels via webhooks.
Supports coherence alerts, validation results, and system status.

Frequency: 141.7001 Hz
"""

import os
import json
import requests
from datetime import datetime
from typing import Optional, Dict, List


class DiscordNotifier:
    """Discord webhook notification handler"""
    
    def __init__(self, webhook_url: Optional[str] = None):
        self.webhook_url = webhook_url or os.getenv("DISCORD_WEBHOOK_URL")
        
        if not self.webhook_url:
            raise ValueError("Discord webhook URL not configured")
    
    def send_embed(
        self,
        title: str,
        description: str,
        color: int = 0x00FF00,
        fields: Optional[List[Dict]] = None,
        footer: Optional[str] = None
    ) -> bool:
        """
        Send rich embed message to Discord.
        
        Args:
            title: Embed title
            description: Embed description
            color: Color code (default: green)
            fields: List of field dicts with 'name' and 'value'
            footer: Footer text
        
        Returns:
            True if successful, False otherwise
        """
        embed = {
            "title": title,
            "description": description,
            "color": color,
            "timestamp": datetime.utcnow().isoformat(),
        }
        
        if fields:
            embed["fields"] = fields
        
        if footer:
            embed["footer"] = {"text": footer}
        
        payload = {
            "embeds": [embed]
        }
        
        try:
            response = requests.post(
                self.webhook_url,
                json=payload,
                timeout=10
            )
            return response.status_code == 204
        except Exception as e:
            print(f"Discord notification failed: {e}")
            return False
    
    def notify_validation_complete(
        self,
        coherence: float,
        tests_passed: int,
        tests_total: int
    ) -> bool:
        """Send validation completion notification"""
        status = "✅ SUCCESS" if coherence >= 0.888 else "⚠️ WARNING"
        color = 0x00FF00 if coherence >= 0.888 else 0xFFAA00
        
        fields = [
            {
                "name": "📊 Coherence",
                "value": f"{coherence:.3f}",
                "inline": True
            },
            {
                "name": "✅ Tests Passed",
                "value": f"{tests_passed}/{tests_total}",
                "inline": True
            },
            {
                "name": "📡 Frequency",
                "value": "141.7001 Hz",
                "inline": True
            }
        ]
        
        return self.send_embed(
            title=f"{status} - QCAL Validation Complete",
            description="V5 Coronación validation has completed",
            color=color,
            fields=fields,
            footer="QCAL ∞³ System | Ψ = I × A_eff² × C^∞"
        )
    
    def notify_coherence_drop(self, coherence: float, threshold: float) -> bool:
        """Send coherence drop alert"""
        return self.send_embed(
            title="🚨 COHERENCE DROP ALERT",
            description=f"System coherence has dropped below threshold!",
            color=0xFF0000,
            fields=[
                {
                    "name": "Current Coherence",
                    "value": f"{coherence:.3f}",
                    "inline": True
                },
                {
                    "name": "Threshold",
                    "value": f"{threshold:.3f}",
                    "inline": True
                }
            ],
            footer="Immediate investigation required"
        )
    
    def notify_agent_status(
        self,
        agent_name: str,
        status: str,
        details: Optional[Dict] = None
    ) -> bool:
        """Send agent status notification"""
        color_map = {
            "RUNNING": 0x0099FF,
            "COMPLETE": 0x00FF00,
            "FAILED": 0xFF0000
        }
        
        fields = []
        if details:
            for key, value in details.items():
                fields.append({
                    "name": key,
                    "value": str(value),
                    "inline": True
                })
        
        return self.send_embed(
            title=f"🤖 {agent_name} - {status}",
            description=f"Agent status update",
            color=color_map.get(status, 0x808080),
            fields=fields,
            footer=f"QCAL ∞³ Agent System"
        )


def main():
    """Command-line interface for Discord notifier"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Discord Notifier")
    parser.add_argument("--test", action="store_true", help="Send test notification")
    parser.add_argument("--coherence", type=float, help="Send coherence notification")
    
    args = parser.parse_args()
    
    try:
        notifier = DiscordNotifier()
        
        if args.test:
            success = notifier.send_embed(
                title="🧪 Test Notification",
                description="Discord notifier is working correctly!",
                color=0x00FF00,
                fields=[
                    {"name": "Frequency", "value": "141.7001 Hz", "inline": True},
                    {"name": "Status", "value": "Operational", "inline": True}
                ]
            )
            print(f"Test notification sent: {success}")
        
        elif args.coherence is not None:
            success = notifier.notify_validation_complete(
                coherence=args.coherence,
                tests_passed=5,
                tests_total=5
            )
            print(f"Coherence notification sent: {success}")
        
        else:
            parser.print_help()
    
    except ValueError as e:
        print(f"Error: {e}")
        print("Set DISCORD_WEBHOOK_URL environment variable")
        return 1
    
    return 0


if __name__ == "__main__":
    exit(main())
