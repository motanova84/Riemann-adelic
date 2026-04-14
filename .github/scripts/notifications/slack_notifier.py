#!/usr/bin/env python3
"""
💬 Slack Notifier - QCAL ∞³ Notification System
===============================================

Sends block-based notifications to Slack channels via webhooks.
Supports coherence alerts, validation results, and system status.

Frequency: 141.7001 Hz
"""

import os
import json
import requests
from datetime import datetime
from typing import Optional, Dict, List


class SlackNotifier:
    """Slack webhook notification handler"""
    
    def __init__(self, webhook_url: Optional[str] = None):
        self.webhook_url = webhook_url or os.getenv("SLACK_WEBHOOK_URL")
        
        if not self.webhook_url:
            raise ValueError("Slack webhook URL not configured")
    
    def send_blocks(
        self,
        text: str,
        blocks: List[Dict]
    ) -> bool:
        """
        Send block-based message to Slack.
        
        Args:
            text: Fallback text for notifications
            blocks: List of Slack block elements
        
        Returns:
            True if successful, False otherwise
        """
        payload = {
            "text": text,
            "blocks": blocks
        }
        
        try:
            response = requests.post(
                self.webhook_url,
                json=payload,
                timeout=10
            )
            return response.status_code == 200
        except Exception as e:
            print(f"Slack notification failed: {e}")
            return False
    
    def notify_validation_complete(
        self,
        coherence: float,
        tests_passed: int,
        tests_total: int
    ) -> bool:
        """Send validation completion notification"""
        status_emoji = ":white_check_mark:" if coherence >= 0.888 else ":warning:"
        
        blocks = [
            {
                "type": "header",
                "text": {
                    "type": "plain_text",
                    "text": f"{status_emoji} QCAL Validation Complete"
                }
            },
            {
                "type": "section",
                "fields": [
                    {
                        "type": "mrkdwn",
                        "text": f"*Coherence:*\n{coherence:.3f}"
                    },
                    {
                        "type": "mrkdwn",
                        "text": f"*Tests Passed:*\n{tests_passed}/{tests_total}"
                    },
                    {
                        "type": "mrkdwn",
                        "text": f"*Frequency:*\n141.7001 Hz"
                    },
                    {
                        "type": "mrkdwn",
                        "text": f"*Timestamp:*\n{datetime.utcnow().strftime('%Y-%m-%d %H:%M UTC')}"
                    }
                ]
            },
            {
                "type": "context",
                "elements": [
                    {
                        "type": "mrkdwn",
                        "text": "QCAL ∞³ System | Ψ = I × A_eff² × C^∞"
                    }
                ]
            }
        ]
        
        return self.send_blocks(
            text=f"QCAL Validation: Coherence {coherence:.3f}",
            blocks=blocks
        )
    
    def notify_coherence_drop(self, coherence: float, threshold: float) -> bool:
        """Send coherence drop alert"""
        blocks = [
            {
                "type": "header",
                "text": {
                    "type": "plain_text",
                    "text": "🚨 COHERENCE DROP ALERT",
                    "emoji": True
                }
            },
            {
                "type": "section",
                "text": {
                    "type": "mrkdwn",
                    "text": "*System coherence has dropped below threshold!*"
                }
            },
            {
                "type": "section",
                "fields": [
                    {
                        "type": "mrkdwn",
                        "text": f"*Current Coherence:*\n{coherence:.3f}"
                    },
                    {
                        "type": "mrkdwn",
                        "text": f"*Threshold:*\n{threshold:.3f}"
                    }
                ]
            },
            {
                "type": "divider"
            },
            {
                "type": "context",
                "elements": [
                    {
                        "type": "mrkdwn",
                        "text": ":rotating_light: *Immediate investigation required*"
                    }
                ]
            }
        ]
        
        return self.send_blocks(
            text=f"ALERT: Coherence dropped to {coherence:.3f}",
            blocks=blocks
        )
    
    def notify_agent_status(
        self,
        agent_name: str,
        status: str,
        details: Optional[Dict] = None
    ) -> bool:
        """Send agent status notification"""
        emoji_map = {
            "RUNNING": ":gear:",
            "COMPLETE": ":white_check_mark:",
            "FAILED": ":x:"
        }
        
        emoji = emoji_map.get(status, ":robot_face:")
        
        blocks = [
            {
                "type": "header",
                "text": {
                    "type": "plain_text",
                    "text": f"{emoji} {agent_name} - {status}"
                }
            }
        ]
        
        if details:
            fields = []
            for key, value in details.items():
                fields.append({
                    "type": "mrkdwn",
                    "text": f"*{key}:*\n{value}"
                })
            
            blocks.append({
                "type": "section",
                "fields": fields
            })
        
        blocks.append({
            "type": "context",
            "elements": [
                {
                    "type": "mrkdwn",
                    "text": "QCAL ∞³ Agent System"
                }
            ]
        })
        
        return self.send_blocks(
            text=f"{agent_name}: {status}",
            blocks=blocks
        )


def main():
    """Command-line interface for Slack notifier"""
    import argparse
    
    parser = argparse.ArgumentParser(description="Slack Notifier")
    parser.add_argument("--test", action="store_true", help="Send test notification")
    parser.add_argument("--coherence", type=float, help="Send coherence notification")
    
    args = parser.parse_args()
    
    try:
        notifier = SlackNotifier()
        
        if args.test:
            blocks = [
                {
                    "type": "header",
                    "text": {
                        "type": "plain_text",
                        "text": "🧪 Test Notification"
                    }
                },
                {
                    "type": "section",
                    "text": {
                        "type": "mrkdwn",
                        "text": "*Slack notifier is working correctly!*"
                    }
                },
                {
                    "type": "section",
                    "fields": [
                        {
                            "type": "mrkdwn",
                            "text": "*Frequency:*\n141.7001 Hz"
                        },
                        {
                            "type": "mrkdwn",
                            "text": "*Status:*\nOperational"
                        }
                    ]
                }
            ]
            
            success = notifier.send_blocks("Test notification", blocks)
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
        print("Set SLACK_WEBHOOK_URL environment variable")
        return 1
    
    return 0


if __name__ == "__main__":
    exit(main())
