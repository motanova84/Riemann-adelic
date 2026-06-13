#!/usr/bin/env python3
"""
🌐 GLOBAL QCAL HUBS — 6 Nodos Regionales πCODE
Puertos 8844-8849 · BAL-003 · Nuremberg
Cada hub replica el estado del PayGate central en su zona regional
Protocolo: QCAL-SYMBIO-BRIDGE v1.0.3 · f₀ = 141.7001 Hz
"""
import json, http.server, os, sys, urllib.request, signal
from datetime import datetime, timezone

F0 = 141.7001
PSI = 1.000000
SELLO = "\u2234\U00013080\u03a9\u221e\u00b3\u03a6\u00b7TUYOYOTU\u00b7HECHO EST\u00c1"
MAIN_PAYGATE = "http://localhost:8844"

HUBS = {
    8844: {"id": "AMERICAS_HUB", "zona": "AMERICA", "desc": "Nueva York, USA (primario)"},
    8845: {"id": "EUROPE_HUB", "zona": "EUROPA", "desc": "Londres, UK"},
    8846: {"id": "ASIA_HUB", "zona": "ASIA", "desc": "Tokio, JP"},
    8847: {"id": "AFRICA_HUB", "zona": "AFRICA", "desc": "Johannesburgo, ZA"},
    8848: {"id": "OCEANIA_HUB", "zona": "OCEANIA", "desc": "Sydney, AU"},
    8849: {"id": "ANTARCTICA_HUB", "zona": "ANTARTIDA", "desc": "Base polar"},
}


def get_reactor_state():
    try:
        r = urllib.request.urlopen(f"{MAIN_PAYGATE}/reactor", timeout=5)
        return json.loads(r.read().decode()).get("reactor", {})
    except:
        return {}


def get_paygate_root():
    try:
        r = urllib.request.urlopen(MAIN_PAYGATE, timeout=5)
        return json.loads(r.read().decode())
    except:
        return {"servicio": "QCAL-PAY-GATE"}


class HubHandler(http.server.BaseHTTPRequestHandler):
    def do_GET(self):
        hub_info = HUBS.get(self.server.server_address[1], {})
        path = self.path.rstrip("/") or "/"

        if path == "/":
            data = {
                "servicio": f"QCAL-{hub_info.get('id', 'HUB')}",
                "zona": hub_info.get("zona", "GLOBAL"),
                "descripcion": hub_info.get("desc", ""),
                "puerto": self.server.server_address[1],
                "frecuencia": F0,
                "coherencia": PSI,
                "sello": SELLO,
                "endpoints": {
                    "GET /": "Info del hub",
                    "GET /reactor": "Estado del reactor πCODE",
                    "GET /estado": "Estado de la boveda (proxy)",
                    "GET /ecosistema": "Ecosistema QCAL (proxy)",
                },
                "timestamp": datetime.now(timezone.utc).isoformat(),
            }
        elif path == "/reactor":
            data = {"success": True, "reactor": get_reactor_state(), "hub": hub_info.get("id")}
        elif path == "/estado":
            try:
                r = urllib.request.urlopen(f"{MAIN_PAYGATE}/estado", timeout=5)
                data = json.loads(r.read().decode())
                data["hub"] = hub_info.get("id")
            except:
                data = {"error": "proxy error", "hub": hub_info.get("id")}
        elif path == "/ecosistema":
            try:
                r = urllib.request.urlopen(f"{MAIN_PAYGATE}/ecosistema", timeout=5)
                data = json.loads(r.read().decode())
                data["hub"] = hub_info.get("id")
            except:
                data = {"error": "proxy error", "hub": hub_info.get("id")}
        else:
            data = {"error": "endpoint no encontrado"}

        body = json.dumps(data, indent=2, ensure_ascii=False).encode("utf-8")
        self.send_response(200)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def log_message(self, fmt, *args):
        hub_info = HUBS.get(self.server.server_address[1], {})
        sys.stderr.write(f"[{hub_info.get('id','?')}] {args[0]} {args[1]} {args[2]}\n")


def start_hub(port):
    hub_info = HUBS.get(port, {"id": "UNKNOWN", "desc": ""})
    server = http.server.HTTPServer(("0.0.0.0", port), HubHandler)
    print(f"  \u2705 {hub_info['id']:>15} | :{port} | {hub_info['desc']}")
    return server


def main():
    print(f"\n{'='*70}")
    print(f"\U0001f310 RED GLOBAL QCAL — 6 HUBS REGIONALES")
    print(f"{'='*70}")
    print(f"Frecuencia: {F0} Hz | Coherencia: \u03a8 = {PSI}")
    print()

    servers = []
    for port in sorted(HUBS.keys()):
        s = start_hub(port)
        servers.append(s)

    print(f"\n\u2705 {len(servers)} hubs activos: {', '.join(str(p) for p in sorted(HUBS.keys()))}")
    print(f"\n\u2728 Nodo central: {HUBS[8844]['id']} (:8844)")
    print(f"   Hubs regionales conectados via proxy al PayGate maestro")
    print(f"   {SELLO}\n")

    # Run all servers
    try:
        while True:
            for s in servers:
                s.handle_request()
    except KeyboardInterrupt:
        print("\n\u23f9 Hubs detenidos.")
        for s in servers:
            s.server_close()


if __name__ == "__main__":
    main()
