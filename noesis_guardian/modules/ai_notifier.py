"""
AI notifier module for Noesis Guardian 3.0.

Provides notification capabilities for the guardian system.
"""

from typing import Any, Dict


class Notifier:
    """Placeholder: por ahora solo imprime en consola."""

    @staticmethod
    def alert(title: str, data: Dict[str, Any]) -> None:
        """
        Send an alert notification.

        Args:
            title: Title of the notification.
            data: Dictionary containing notification data.
        """
        print(f"⚠️ NOTIFICACIÓN: {title}")
        # Aquí podrías integrar Telegram / email en el futuro.
