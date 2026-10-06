"""Wire, lifecycle, gap, and real native synthetic-source checks."""

from dataclasses import FrozenInstanceError
from pathlib import Path
import socket
import struct
import subprocess
import sys
import time

import numpy as np
import pytest

from experiments.qcal_exp01.protocol import (
    HEADER, MAGIC, MAX_DATAGRAM_BYTES, MAX_SAMPLES, Packet, ProtocolError,
    decode_packet, encode_packet,
)
from experiments.qcal_exp01.receiver import UDPReceiver


def packet(sequence: int = 0, first: int = 0, rate: int = 1_000_000) -> Packet:
    """Create a small packet with distinguishable signed channel samples."""
    return Packet(sequence, first, rate, np.array([1, -2, 32767], dtype=np.int16),
                  np.array([-32768, 256, -257], dtype=np.int16))


def wait_for(predicate, timeout: float = 2.0) -> None:
    """Wait for a bounded asynchronous test condition."""
    deadline = time.monotonic() + timeout
    while not predicate():
        if time.monotonic() > deadline:
            pytest.fail("receiver condition timed out")
        time.sleep(0.005)


def test_little_endian_concatenated_channels() -> None:
    """Known bytes certify framing, signedness, endianness, and channel layout."""
    encoded = encode_packet(packet(7, 123))
    assert encoded[:HEADER.size] == HEADER.pack(MAGIC, 1, 0, 32, 7, 123, 1_000_000, 3)
    assert encoded[32:] == struct.pack("<6h", 1, -2, 32767, -32768, 256, -257)
    decoded = decode_packet(encoded)
    assert (decoded.sequence, decoded.first_sample_index, decoded.count) == (7, 123, 3)
    np.testing.assert_array_equal(decoded.channel_a, packet().channel_a)
    np.testing.assert_array_equal(decoded.channel_b, packet().channel_b)
    with pytest.raises(ValueError):
        decoded.channel_a[0] = 0
    with pytest.raises(ValueError):
        decoded.channel_a.flags.writeable = True


def test_big_endian_array_is_encoded_little_endian() -> None:
    """Input host-array byte order never changes the wire byte order."""
    source = packet()
    source = Packet(0, 0, 100_000, source.channel_a.astype(">i2"),
                    source.channel_b.astype(">i2"))
    assert encode_packet(source)[32:] == struct.pack("<6h", 1, -2, 32767, -32768, 256, -257)


@pytest.mark.parametrize("offset,replacement", [
    (0, b"BAD!"), (4, b"\x02"), (5, b"\x01"), (6, b"\x00\x20"),
    (24, struct.pack("<I", 999)), (28, struct.pack("<I", 0)),
    (28, struct.pack("<I", MAX_SAMPLES + 1)), (28, struct.pack("<I", 2**32 - 1)),
])
def test_malformed_header(offset: int, replacement: bytes) -> None:
    """Reject unsupported or unbounded header fields."""
    data = bytearray(encode_packet(packet()))
    data[offset:offset + len(replacement)] = replacement
    with pytest.raises(ProtocolError):
        decode_packet(data)


@pytest.mark.parametrize("data", [
    b"", b"QCL1", encode_packet(packet())[:-1], encode_packet(packet()) + b"\0",
    b"\0" * (MAX_DATAGRAM_BYTES + 1),
    struct.pack(">4sBBHQQII", MAGIC, 1, 0, 32, 0, 0, 1_000_000, 3) + b"\0" * 12,
])
def test_invalid_lengths_and_big_endian_header(data: bytes) -> None:
    """Truncation, trailing data, and big-endian headers are invalid."""
    with pytest.raises(ProtocolError):
        decode_packet(data)


@pytest.mark.parametrize("source", [
    Packet(-1, 0, 1_000_000, packet().channel_a, packet().channel_b),
    Packet(2**64, 0, 1_000_000, packet().channel_a, packet().channel_b),
    Packet(0, 2**64 - 1, 1_000_000, packet().channel_a, packet().channel_b),
    Packet(0, 0, 42, packet().channel_a, packet().channel_b),
    Packet(0, 0, 1_000_000, np.array([], dtype=np.int16), np.array([], dtype=np.int16)),
    Packet(0, 0, 1_000_000, packet().channel_a, packet().channel_b[:1]),
    Packet(0, 0, 1_000_000, np.array([1.0]), np.array([1.0])),
    Packet(0, 0, 1_000_000, np.zeros((2, 2), dtype=np.int16), packet().channel_b),
])
def test_encode_validation(source: Packet) -> None:
    """Encoding cannot emit frames outside the wire contract."""
    with pytest.raises(ProtocolError):
        encode_packet(source)


def test_maximum_payload() -> None:
    """The largest legal packet is within the explicit MTU-safe limit."""
    samples = np.zeros(MAX_SAMPLES, dtype=np.int16)
    data = encode_packet(Packet(0, 0, 1_000_000, samples, samples))
    assert len(data) == MAX_DATAGRAM_BYTES
    assert decode_packet(data).count == MAX_SAMPLES


def test_import_does_not_open_socket_or_start_thread() -> None:
    """Module import is inert even when acquisition operations are forbidden."""
    subprocess.run(
        [sys.executable, "-c",
         "import socket, threading\n"
         "def forbidden(*args, **kwargs):\n"
         "    raise AssertionError('import started acquisition')\n"
         "socket.socket = forbidden\n"
         "threading.Thread.start = forbidden\n"
         "import experiments.qcal_exp01.receiver\n"],
        check=True, capture_output=True, timeout=5,
    )


def test_receiver_ordering_gaps_freshness_and_restart() -> None:
    """Bad traffic never refreshes health; gaps resync at absolute indices."""
    events = []
    receiver = UDPReceiver(
        lambda p: events.append(("packet", p.first_sample_index)),
        lambda index: events.append(("reset", index)), port=0, freshness_seconds=0.05,
    )
    assert receiver.snapshot().state == "stopped"
    assert receiver.start()
    port = receiver.snapshot().bound_port
    assert receiver.start()
    assert receiver.snapshot().bound_port == port
    sender = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        def send(data: bytes) -> None:
            """Send one test datagram to the receiver's bound loopback port."""
            sender.sendto(data, ("127.0.0.1", port))
        send(encode_packet(packet(10, 100)))
        wait_for(lambda: receiver.snapshot().packets_received == 1)
        old = receiver.snapshot()
        with pytest.raises(FrozenInstanceError):
            old.state = "broken"
        send(encode_packet(packet(10, 100)))  # duplicate
        send(encode_packet(packet(9, 90)))  # reordered sequence
        send(encode_packet(packet(11, 102)))  # overlapping samples
        send(encode_packet(packet(11, 103, 100_000)))  # changed rate
        send(b"x" * 40_000)  # recvmsg must detect truncation, not accept a prefix
        wait_for(lambda: receiver.snapshot().packets_rejected == 5)
        assert receiver.snapshot().last_valid_monotonic == old.last_valid_monotonic
        wait_for(lambda: receiver.snapshot().state == "stale")
        send(encode_packet(packet(12, 106)))
        wait_for(lambda: receiver.snapshot().packets_received == 2)
        assert events == [("reset", 100), ("packet", 100), ("reset", 106), ("packet", 106)]
        assert receiver.snapshot().gaps == 1
        send(encode_packet(packet(13, 109)))
        wait_for(lambda: receiver.snapshot().packets_received == 3)
        assert events[-1] == ("packet", 109)
        assert receiver.snapshot().gaps == 1
    finally:
        sender.close()
        receiver.stop()
    assert receiver.snapshot().state == "stopped"
    assert receiver._thread is None
    assert receiver._socket is None
    receiver.stop()
    assert receiver.start()
    assert receiver.snapshot().packets_received == 0
    receiver.stop()


def test_lan_requires_explicit_opt_in_and_sender() -> None:
    """Wildcard/LAN binding is impossible with default configuration."""
    for options in ({}, {"allow_lan": True}, {"expected_sender": "127.0.0.1"}):
        with pytest.raises(ValueError):
            UDPReceiver(lambda p: None, host="0.0.0.0", **options)
    receiver = UDPReceiver(lambda p: None, host="0.0.0.0", allow_lan=True,
                           expected_sender="127.0.0.1", port=0)
    assert receiver.start()
    receiver.stop()


def test_wrong_sender_is_not_valid_health() -> None:
    """Traffic from a host other than the configured source is rejected."""
    receiver = UDPReceiver(lambda p: None, expected_sender="127.0.0.2", port=0)
    assert receiver.start()
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sender:
        sender.sendto(encode_packet(packet()), ("127.0.0.1", receiver.snapshot().bound_port))
        wait_for(lambda: receiver.snapshot().packets_rejected == 1)
    assert receiver.snapshot().state == "waiting"
    assert receiver.snapshot().last_valid_monotonic is None
    receiver.stop()


def test_bind_error_is_unavailable() -> None:
    """An occupied UDP port is an explicit unavailable state."""
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as occupied:
        occupied.bind(("127.0.0.1", 0))
        receiver = UDPReceiver(lambda p: None, port=occupied.getsockname()[1])
        assert not receiver.start()
        assert receiver.snapshot().state == "error"
        assert not receiver.snapshot().available
        assert receiver.snapshot().last_error
        receiver.stop()


def test_callback_error_requires_resynchronization() -> None:
    """DSP failure does not permit replay or claim successful fresh processing."""
    resets = []
    seen = []
    def consume(p: Packet) -> None:
        """Fail the first DSP operation only."""
        seen.append(p.sequence)
        if p.sequence == 0:
            raise RuntimeError("DSP unavailable")
    receiver = UDPReceiver(consume, resets.append, port=0)
    assert receiver.start()
    with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as sender:
        address = ("127.0.0.1", receiver.snapshot().bound_port)
        sender.sendto(encode_packet(packet()), address)
        wait_for(lambda: receiver.snapshot().state == "error")
        assert receiver.snapshot().last_valid_monotonic is None
        sender.sendto(encode_packet(packet()), address)
        wait_for(lambda: receiver.snapshot().packets_rejected == 1)
        sender.sendto(encode_packet(packet(1, 3)), address)
        wait_for(lambda: receiver.snapshot().packets_received == 1)
    assert seen == [0, 1]
    assert resets == [0, 3]
    receiver.stop()


def test_native_synthetic_decode() -> None:
    """Compile the actual C sender and verify its absolute-clock ADC counts."""
    native = Path(__file__).resolve().parents[1] / "experiments/qcal_exp01/native"
    subprocess.run(["make", "-C", str(native), "CC=gcc"], check=True, capture_output=True)
    try:
        with socket.socket(socket.AF_INET, socket.SOCK_DGRAM) as receiver:
            receiver.bind(("127.0.0.1", 0))
            receiver.settimeout(2.0)
            result = subprocess.run(
                [str(native / "qcal_daq_simulator"), "--port",
                 str(receiver.getsockname()[1]), "--packets", "3", "--x0", "0.01"],
                check=True, capture_output=True, text=True, timeout=5,
            )
            assert "SYNTHETIC (NOT DMA)" in result.stderr
            for sequence in range(3):
                data, _ = receiver.recvfrom(MAX_DATAGRAM_BYTES + 1)
                decoded = decode_packet(data)
                assert decoded.sequence == sequence
                assert decoded.first_sample_index == sequence * MAX_SAMPLES
                assert decoded.sample_rate == 1_000_000
                index = np.arange(decoded.count) + decoded.first_sample_index
                carrier = 2 * np.pi * (index % 10) / 10
                phase = 13.4034 * 0.01 * np.sin(2 * np.pi * 141.7001 * index / 1_000_000)
                np.testing.assert_array_equal(
                    decoded.channel_a, np.rint(12000 * np.cos(carrier)).astype(np.int16))
                np.testing.assert_array_equal(
                    decoded.channel_b, np.rint(12000 * np.cos(carrier + phase)).astype(np.int16))
    finally:
        subprocess.run(["make", "-C", str(native), "clean"], check=True, capture_output=True)
