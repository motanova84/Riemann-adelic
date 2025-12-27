"""
AI notifier module for Noesis Guardian 3.0.

Alert and notification system for Guardian events.

Author: Jose Manuel Mota Burruezo (JMMB)
"""

from typing import Any, Dict


class Notifier:
    """
    Notification component for Guardian alerts.
    
    Provides simple console-based notifications for Guardian events.
    Can be extended for more sophisticated notification mechanisms.
    """

    @staticmethod
    def alert(message: str, data: Dict[str, Any] = None) -> None:
        """
        Send an alert notification.

        Args:
            message: Alert message to display.
            data: Optional additional data to include in the alert.
        """
        print(f"ALERTA: {message}")
        if data:
            for key, value in data.items():
                print(f"   {key}: {value}")
