#!/usr/bin/env python3
"""
NOESIS GUARDIAN — AI Notifier Module
=====================================

Sistema de notificaciones para alertas del Guardian.
Soporta múltiples canales de notificación.

Canales soportados:
- Telegram
- Email
- Logs
- Consola

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
License: Creative Commons BY-NC-SA 4.0
"""

import json
import logging
import os
from datetime import datetime
from pathlib import Path
from typing import Any, Dict, List, Optional

# Configurar logging
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    datefmt="%Y-%m-%d %H:%M:%S",
)
logger = logging.getLogger("NoesisNotifier")


class NotificationConfig:
    """Configuración de notificaciones."""

    def __init__(self, config_path: Optional[Path] = None):
        """
        Inicializa la configuración.

        Args:
            config_path: Ruta al archivo de configuración JSON
        """
        self.config = {
            "enabled": True,
            "channels": {
                "console": True,
                "log_file": True,
                "telegram": False,
                "email": False,
            },
            "telegram": {
                "bot_token": os.environ.get("TELEGRAM_BOT_TOKEN", ""),
                "chat_id": os.environ.get("TELEGRAM_CHAT_ID", ""),
            },
            "email": {
                "smtp_host": os.environ.get("SMTP_HOST", ""),
                "smtp_port": int(os.environ.get("SMTP_PORT", "587")),
                "username": os.environ.get("SMTP_USERNAME", ""),
                "password": os.environ.get("SMTP_PASSWORD", ""),
                "recipient": os.environ.get("ALERT_EMAIL", ""),
            },
            "log_file": {
                "path": "noesis_guardian/guardian_alerts.log",
            },
        }

        if config_path and config_path.exists():
            self._load_config(config_path)

    def _load_config(self, path: Path):
        """Carga configuración desde archivo JSON."""
        try:
            with open(path, "r", encoding="utf-8") as f:
                loaded = json.load(f)
                self._deep_update(self.config, loaded)
        except Exception as e:
            logger.warning(f"Could not load config from {path}: {e}")

    def _deep_update(self, base: dict, update: dict):
        """Actualización profunda de diccionarios."""
        for key, value in update.items():
            if key in base and isinstance(base[key], dict) and isinstance(value, dict):
                self._deep_update(base[key], value)
            else:
                base[key] = value


class Notifier:
    """
    Sistema de notificaciones del Guardian NOESIS.

    Envía alertas a través de múltiples canales configurables.
    """

    _instance: Optional["Notifier"] = None
    _config: Optional[NotificationConfig] = None

    @classmethod
    def _get_config(cls) -> NotificationConfig:
        """Obtiene la configuración singleton."""
        if cls._config is None:
            cls._config = NotificationConfig()
        return cls._config

    @classmethod
    def alert(cls, message: str, data: Optional[Dict[str, Any]] = None) -> Dict[str, Any]:
        """
        Envía una alerta a todos los canales habilitados.

        Args:
            message: Mensaje de la alerta
            data: Datos adicionales de la alerta

        Returns:
            Resultado del envío a cada canal
        """
        config = cls._get_config()
        results = {
            "timestamp": datetime.now().isoformat(),
            "message": message,
            "channels": {},
        }

        if not config.config["enabled"]:
            results["status"] = "disabled"
            return results

        channels = config.config["channels"]

        # Console
        if channels.get("console", True):
            results["channels"]["console"] = cls._send_console(message, data)

        # Log file
        if channels.get("log_file", True):
            results["channels"]["log_file"] = cls._send_log_file(message, data, config)

        # Telegram (si está configurado)
        if channels.get("telegram", False):
            results["channels"]["telegram"] = cls._send_telegram(message, data, config)

        # Email (si está configurado)
        if channels.get("email", False):
            results["channels"]["email"] = cls._send_email(message, data, config)

        return results

    @classmethod
    def _send_console(cls, message: str, data: Optional[Dict[str, Any]]) -> Dict[str, Any]:
        """Envía alerta a la consola."""
        try:
            print(f"\n🔔 NOESIS ALERT: {message}")
            if data:
                print(f"   Data: {json.dumps(data, default=str)[:200]}...")
            return {"success": True}
        except Exception as e:
            return {"success": False, "error": str(e)}

    @classmethod
    def _send_log_file(
        cls, message: str, data: Optional[Dict[str, Any]], config: NotificationConfig
    ) -> Dict[str, Any]:
        """Envía alerta al archivo de log."""
        try:
            log_path = Path(config.config["log_file"]["path"])
            log_path.parent.mkdir(parents=True, exist_ok=True)

            log_entry = {
                "timestamp": datetime.now().isoformat(),
                "message": message,
                "data": data,
            }

            with open(log_path, "a", encoding="utf-8") as f:
                f.write(json.dumps(log_entry, default=str) + "\n")

            return {"success": True, "path": str(log_path)}
        except Exception as e:
            return {"success": False, "error": str(e)}

    @classmethod
    def _send_telegram(
        cls, message: str, data: Optional[Dict[str, Any]], config: NotificationConfig
    ) -> Dict[str, Any]:
        """Envía alerta a Telegram."""
        try:
            telegram_config = config.config.get("telegram", {})
            bot_token = telegram_config.get("bot_token", "")
            chat_id = telegram_config.get("chat_id", "")

            if not bot_token or not chat_id:
                return {"success": False, "error": "Telegram not configured"}

            import requests

            url = f"https://api.telegram.org/bot{bot_token}/sendMessage"
            text = f"🔔 NOESIS ALERT\n\n{message}"

            if data:
                text += f"\n\nData: {json.dumps(data, default=str)[:500]}"

            response = requests.post(
                url,
                json={"chat_id": chat_id, "text": text},
                timeout=10,
            )

            return {"success": response.status_code == 200}
        except ImportError:
            return {"success": False, "error": "requests not installed"}
        except Exception as e:
            return {"success": False, "error": str(e)}

    @classmethod
    def _send_email(
        cls, message: str, data: Optional[Dict[str, Any]], config: NotificationConfig
    ) -> Dict[str, Any]:
        """Envía alerta por email."""
        try:
            email_config = config.config.get("email", {})

            if not email_config.get("smtp_host") or not email_config.get("recipient"):
                return {"success": False, "error": "Email not configured"}

            import smtplib
            from email.mime.text import MIMEText

            body = f"NOESIS GUARDIAN ALERT\n\n{message}\n\n"
            if data:
                body += f"Data:\n{json.dumps(data, indent=2, default=str)}"

            msg = MIMEText(body)
            msg["Subject"] = f"🔔 NOESIS Alert: {message[:50]}"
            msg["From"] = email_config.get("username", "noesis@guardian.local")
            msg["To"] = email_config["recipient"]

            with smtplib.SMTP(email_config["smtp_host"], email_config["smtp_port"]) as server:
                if email_config.get("username") and email_config.get("password"):
                    server.starttls()
                    server.login(email_config["username"], email_config["password"])
                server.send_message(msg)

            return {"success": True}
        except Exception as e:
            return {"success": False, "error": str(e)}

    @classmethod
    def info(cls, message: str) -> None:
        """Log de información."""
        logger.info(message)

    @classmethod
    def warning(cls, message: str) -> None:
        """Log de advertencia."""
        logger.warning(message)

    @classmethod
    def error(cls, message: str) -> None:
        """Log de error."""
        logger.error(message)

    @classmethod
    def get_alert_history(cls, limit: int = 100) -> List[Dict[str, Any]]:
        """
        Obtiene el historial de alertas.

        Args:
            limit: Número máximo de alertas a retornar

        Returns:
            Lista de alertas recientes
        """
        config = cls._get_config()
        log_path = Path(config.config["log_file"]["path"])

        if not log_path.exists():
            return []

        alerts = []
        try:
            with open(log_path, "r", encoding="utf-8") as f:
                for line in f:
                    try:
                        alert = json.loads(line.strip())
                        alerts.append(alert)
                    except json.JSONDecodeError:
                        pass

            return alerts[-limit:]
        except Exception:
            return []


if __name__ == "__main__":
    print("=" * 60)
    print("NOESIS GUARDIAN — AI Notifier Demo")
    print("=" * 60)

    # Enviar alerta de prueba
    print("\n📤 Sending test alert...")
    result = Notifier.alert(
        "Test alert from NOESIS Guardian",
        {"test": True, "coherence": 0.95, "timestamp": datetime.now().isoformat()},
    )

    print("\n📊 Alert Result:")
    print(f"   Timestamp: {result['timestamp']}")
    for channel, status in result["channels"].items():
        print(f"   {channel}: {'✅' if status.get('success') else '❌'}")

    print("\n✅ Demo complete")
