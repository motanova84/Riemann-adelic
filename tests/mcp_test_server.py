#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Servidor MCP de prueba - network.checkResonance (Nivel B)."""

from __future__ import annotations

import json
from http.server import BaseHTTPRequestHandler, HTTPServer

from mcp_network.resonance import check_node_resonance


class MCPTestHandler(BaseHTTPRequestHandler):
    """JSON-RPC 2.0 test handler exposing network.checkResonance."""

    def do_POST(self) -> None:  # noqa: N802
        if self.path != "/jsonrpc":
            self.send_error(404)
            return

        content_length = int(self.headers.get("Content-Length", "0"))
        post_data = self.rfile.read(content_length)

        try:
            request = json.loads(post_data)
        except json.JSONDecodeError:
            self._send_json(
                {
                    "jsonrpc": "2.0",
                    "id": None,
                    "error": {"code": -32700, "message": "Parse error"},
                }
            )
            return

        if request.get("method") == "network.checkResonance":
            node = (request.get("params") or {}).get("node")
            result = check_node_resonance(node)
            response = {"jsonrpc": "2.0", "id": request.get("id"), "result": result}
        else:
            response = {
                "jsonrpc": "2.0",
                "id": request.get("id"),
                "error": {"code": -32601, "message": "Method not found"},
            }

        self._send_json(response)

    def _send_json(self, payload: dict) -> None:
        body = json.dumps(payload).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, _format: str, *_args: object) -> None:
        """Silence HTTP request logs for cleaner local test output."""
        return


if __name__ == "__main__":
    port = 8506
    server = HTTPServer(("127.0.0.1", port), MCPTestHandler)
    print(f"🚀 MCP Test Server escuchando en http://127.0.0.1:{port}/jsonrpc")
    print("Método expuesto: network.checkResonance")
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nServidor detenido.")
