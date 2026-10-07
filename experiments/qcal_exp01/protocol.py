"""Versioned, bounded UDP framing for two calibrated ADC-count channels.

Wire format is little endian: a 32-byte header followed by all channel A
samples, then all channel B samples (signed 16-bit, never interleaved).
"""

from dataclasses import dataclass
import struct

import numpy as np

MAGIC = b"QCL1"
VERSION = 1
HEADER = struct.Struct("<4sBBHQQII")
MAX_DATAGRAM_BYTES = 1400
MAX_SAMPLES = (MAX_DATAGRAM_BYTES - HEADER.size) // 4
SUPPORTED_SAMPLE_RATES = (100_000, 1_000_000)


class ProtocolError(ValueError):
    """A datagram violates the bounded version-one wire contract."""


@dataclass(frozen=True)
class Packet:
    """Two ADC channels with sequence and absolute sample-clock coordinates."""

    sequence: int
    first_sample_index: int
    sample_rate: int
    channel_a: np.ndarray
    channel_b: np.ndarray

    @property
    def count(self) -> int:
        """Return the number of samples in each channel."""
        return len(self.channel_a)


def _validate_coordinates(sequence: int, first: int, rate: int, count: int) -> None:
    """Validate bounded sample-clock coordinates before payload allocation."""
    if any(not isinstance(value, (int, np.integer)) for value in (sequence, first, rate, count)):
        raise ProtocolError("header coordinates must be integers")
    if not 0 <= sequence < 2**64 or not 0 <= first < 2**64:
        raise ProtocolError("sequence and sample index must fit uint64")
    if rate not in SUPPORTED_SAMPLE_RATES:
        raise ProtocolError("unsupported sample rate")
    if not 1 <= count <= MAX_SAMPLES or first + count > 2**64:
        raise ProtocolError("invalid sample count or sample-index overflow")


def encode_packet(packet: Packet) -> bytes:
    """Encode equal-length int16 channels into one bounded little-endian datagram."""
    channels = (np.asarray(packet.channel_a), np.asarray(packet.channel_b))
    if any(channel.ndim != 1 or channel.dtype.kind != "i" or channel.dtype.itemsize != 2
           for channel in channels):
        raise ProtocolError("channels must be one-dimensional signed int16 arrays")
    count = len(channels[0])
    if len(channels[1]) != count:
        raise ProtocolError("channel lengths differ")
    _validate_coordinates(packet.sequence, packet.first_sample_index, packet.sample_rate, count)
    header = HEADER.pack(MAGIC, VERSION, 0, HEADER.size, packet.sequence,
                         packet.first_sample_index, packet.sample_rate, count)
    return header + b"".join(channel.astype("<i2", copy=False).tobytes() for channel in channels)


def decode_packet(datagram: bytes) -> Packet:
    """Decode an exact-length datagram, returning immutable ADC sample buffers.

    Raises:
        ProtocolError: For unknown versions, rates, flags, invalid counts, or
            any short, oversized, or trailing payload.
    """
    if not HEADER.size <= len(datagram) <= MAX_DATAGRAM_BYTES:
        raise ProtocolError("invalid datagram length")
    magic, version, flags, size, sequence, first, rate, count = HEADER.unpack_from(datagram)
    if magic != MAGIC or version != VERSION or flags != 0 or size != HEADER.size:
        raise ProtocolError("unknown magic, version, flags, or header size")
    _validate_coordinates(sequence, first, rate, count)
    if len(datagram) != HEADER.size + count * 4:
        raise ProtocolError("payload length does not match sample count")
    # A bytes backing store prevents callers from enabling writes again.
    payload = bytes(datagram[HEADER.size:])
    samples = np.frombuffer(payload, dtype="<i2")
    return Packet(sequence, first, rate, samples[:count], samples[count:])
