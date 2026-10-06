"""Opt-in UDP receiver with ordered sample clocks and immutable health snapshots."""

from dataclasses import dataclass, replace
import ipaddress
import socket
import threading
import time
from typing import Callable, Optional

from .protocol import MAX_DATAGRAM_BYTES, Packet, ProtocolError, decode_packet


@dataclass(frozen=True)
class ReceiverSnapshot:
    """Thread-safe health; freshness refers only to accepted, valid packets."""

    state: str = "stopped"
    last_valid_monotonic: Optional[float] = None
    packets_received: int = 0
    packets_rejected: int = 0
    gaps: int = 0
    last_error: Optional[str] = None
    bound_port: Optional[int] = None
    socket_receive_buffer_bytes: Optional[int] = None

    @property
    def available(self) -> bool:
        """Whether the receiver currently has a fresh successful stream."""
        return self.state == "receiving"


class UDPReceiver:
    """Receive packets without import-time sockets or background threads.

    ``on_gap(first_sample_index)`` resets/resynchronizes DSP before the first
    packet and after every sequence/sample gap. Rate changes are rejected.
    LAN binding requires ``allow_lan=True`` and an explicit expected sender.
    Receive buffering tolerates short processing stalls; the operating system
    may clamp the request, so snapshots report its actual socket buffer size.
    """

    def __init__(
        self,
        on_packet: Callable[[Packet], None],
        on_gap: Optional[Callable[[int], None]] = None,
        host: str = "127.0.0.1",
        port: int = 5005,
        expected_sender: Optional[str] = None,
        allow_lan: bool = False,
        freshness_seconds: float = 2.0,
        receive_buffer_bytes: int = 4 * 1024 * 1024,
    ) -> None:
        """Configure the stream, sender restriction, callbacks, and freshness."""
        bind_host = socket.gethostbyname(host)
        if not ipaddress.ip_address(bind_host).is_loopback and (
            not allow_lan or not expected_sender
        ):
            raise ValueError("LAN reception requires allow_lan and expected_sender")
        if not 0 <= port <= 65535 or not 0 < freshness_seconds < float("inf"):
            raise ValueError("invalid port or freshness interval")
        if (isinstance(receive_buffer_bytes, bool)
                or not isinstance(receive_buffer_bytes, int)
                or not MAX_DATAGRAM_BYTES <= receive_buffer_bytes <= 16 * 1024 * 1024):
            raise ValueError("receive buffer must be between 1400 bytes and 16 MiB")
        self._host, self._port = bind_host, port
        self._sender = socket.gethostbyname(expected_sender) if expected_sender else None
        self._on_packet, self._on_gap = on_packet, on_gap
        self._freshness = freshness_seconds
        self._receive_buffer_bytes = receive_buffer_bytes
        self._lock = threading.Lock()
        self._lifecycle_lock = threading.RLock()
        self._health = ReceiverSnapshot()
        self._socket: Optional[socket.socket] = None
        self._thread: Optional[threading.Thread] = None
        self._stop = threading.Event()

    def snapshot(self) -> ReceiverSnapshot:
        """Return an immutable health snapshot computed against monotonic time."""
        with self._lock:
            result = self._health
        if (result.state == "receiving" and result.last_valid_monotonic is not None
                and time.monotonic() - result.last_valid_monotonic > self._freshness):
            return replace(result, state="stale")
        return result

    def _update(self, **changes: object) -> None:
        """Publish a new health value under its dedicated lock."""
        with self._lock:
            self._health = replace(self._health, **changes)

    def _reject(self, reason: str) -> None:
        """Record invalid traffic without updating valid-packet freshness."""
        with self._lock:
            self._health = replace(
                self._health, packets_rejected=self._health.packets_rejected + 1,
                last_error=reason,
            )

    def start(self) -> bool:
        """Bind and start once; return false and expose error on bind failure."""
        with self._lifecycle_lock:
            if self._thread is not None and self._thread.is_alive():
                return True
            self._stop.clear()
            with self._lock:
                self._health = ReceiverSnapshot(state="starting")
            sock = None
            try:
                sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
                sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, self._receive_buffer_bytes)
                sock.bind((self._host, self._port))
                sock.settimeout(0.2)
            except OSError as exc:
                if sock is not None:
                    sock.close()
                self._update(state="error", last_error=str(exc))
                return False
            self._socket = sock
            self._update(
                state="waiting", bound_port=sock.getsockname()[1],
                socket_receive_buffer_bytes=sock.getsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF),
            )
            self._thread = threading.Thread(
                target=self._run, args=(sock,), name="qcal-exp01-udp", daemon=True,
            )
            self._thread.start()
            return True

    def stop(self) -> None:
        """Close the socket and join the worker; repeated stops are harmless."""
        with self._lifecycle_lock:
            self._stop.set()
            if self._socket is not None:
                self._socket.close()
                self._socket = None
            thread = self._thread
            if thread is not None and thread is not threading.current_thread():
                thread.join(timeout=2.0)
                if thread.is_alive():
                    self._update(state="error", last_error="receiver callback did not stop")
                    return
            self._thread = None
            self._update(state="stopped")

    def _run(self, sock: socket.socket) -> None:
        """Validate ordering and publish successful callbacks on the worker."""
        previous: Optional[Packet] = None
        needs_resync = True
        while not self._stop.is_set():
            try:
                if hasattr(sock, "recvmsg"):
                    data, _, flags, address = sock.recvmsg(MAX_DATAGRAM_BYTES)
                    if flags & socket.MSG_TRUNC:
                        self._reject("truncated datagram")
                        continue
                else:
                    data, address = sock.recvfrom(MAX_DATAGRAM_BYTES + 1)
                if self._sender is not None and address[0] != self._sender:
                    self._reject("unexpected sender")
                    continue
                packet = decode_packet(data)
                if previous is not None:
                    if packet.sample_rate != previous.sample_rate:
                        raise ProtocolError("sample rate changed")
                    if packet.sequence <= previous.sequence:
                        raise ProtocolError("duplicate or reordered sequence")
                    if packet.first_sample_index < previous.first_sample_index + previous.count:
                        raise ProtocolError("overlapping or reordered samples")
                gap = previous is not None and (
                    packet.sequence != previous.sequence + 1
                    or packet.first_sample_index != previous.first_sample_index + previous.count
                )
                previous = packet
                try:
                    if (needs_resync or gap) and self._on_gap is not None:
                        self._on_gap(packet.first_sample_index)
                    self._on_packet(packet)
                except Exception as exc:
                    # Failed DSP must resynchronize before processing another packet.
                    needs_resync = True
                    self._update(state="error", last_error=f"callback failed: {exc}")
                    continue
                needs_resync = False
                with self._lock:
                    self._health = replace(
                        self._health, state="receiving",
                        last_valid_monotonic=time.monotonic(),
                        packets_received=self._health.packets_received + 1,
                        gaps=self._health.gaps + int(gap), last_error=None,
                    )
            except socket.timeout:
                continue
            except ProtocolError as exc:
                self._reject(str(exc))
            except OSError as exc:
                if not self._stop.is_set():
                    self._update(state="error", last_error=str(exc))
                break
