"""
Tests for mcp_network.resonance
================================

Covers score_psi, classify_resonance, and check_node_resonance.
"""
from __future__ import annotations

import pytest

from mcp_network.resonance import (
    score_psi,
    classify_resonance,
    check_node_resonance,
    _PSI_COHERENT,
    _PSI_DRIFTING,
)
from mcp_network.registry import NODE_CATALOG

# ---------------------------------------------------------------------------
# Nodes used in the MCP-QCAL Bus
# ---------------------------------------------------------------------------
MCP_NODES = [
    "dramaturgo",
    "github-mcp-server",
    "auron-governor",
    "141-hz",
    "3d-navier-stokes",
    "interferometro-noesico",
    "biologia-cuantica-noesica",
]


# ===========================================================================
# score_psi
# ===========================================================================

class TestScorePsi:
    def test_spec_simulation_defaults(self):
        """12.4 ms + 0.018 rad → Ψ ≈ 0.893 which exceeds the 0.888 threshold."""
        psi = score_psi(12.4, 0.018, True, True)
        # Ψ = 1 − 0.5×(12.4/100) − 0.5×(0.018/0.2) = 1 − 0.062 − 0.045 = 0.893
        assert psi == pytest.approx(0.893, abs=1e-6)
        assert psi >= _PSI_COHERENT

    def test_perfect_conditions(self):
        """Zero latency and zero phase offset → Ψ = 1.0."""
        psi = score_psi(0.0, 0.0, True, True)
        assert psi == pytest.approx(1.0)

    def test_full_latency_penalty(self):
        """100 ms latency, zero phase → Ψ = 0.5."""
        psi = score_psi(100.0, 0.0, True, True)
        assert psi == pytest.approx(0.5)

    def test_full_phase_penalty(self):
        """Zero latency, 0.2 rad phase offset → Ψ = 0.5."""
        psi = score_psi(0.0, 0.2, True, True)
        assert psi == pytest.approx(0.5)
    def test_both_max_penalties(self):
        """Max latency + max phase → Ψ = 0.0."""
        psi = score_psi(100.0, 0.2, True, True)
        assert psi == pytest.approx(0.0)

    def test_heartbeat_failure_returns_zero(self):
        psi = score_psi(0.0, 0.0, False, True)
        assert psi == pytest.approx(0.0)

    def test_schema_failure_returns_zero(self):
        psi = score_psi(0.0, 0.0, True, False)
        assert psi == pytest.approx(0.0)

    def test_result_clamped_to_unit_interval(self):
        """Negative latency/phase should not exceed [0, 1]."""
        psi = score_psi(-50.0, -0.5, True, True)
        assert 0.0 <= psi <= 1.0

    def test_overcap_latency_clamped(self):
        """Latency >> 100 ms should still give Ψ ≥ 0.0."""
        psi = score_psi(1000.0, 0.0, True, True)
        assert psi == pytest.approx(0.5)  # phase penalty = 0, latency capped at 1

    def test_negative_phase_same_as_positive(self):
        """Phase offset uses abs(); sign should not matter."""
        assert score_psi(0.0, 0.1, True, True) == pytest.approx(
            score_psi(0.0, -0.1, True, True)
        )


# ===========================================================================
# classify_resonance
# ===========================================================================

class TestClassifyResonance:
    def test_offline_when_not_reachable(self):
        resonance, status = classify_resonance(1.0, False)
        assert resonance == "offline"
        assert status == "fail"

    def test_coherent_at_threshold(self):
        resonance, status = classify_resonance(_PSI_COHERENT, True)
        assert resonance == "coherent"
        assert status == "pass"

    def test_coherent_above_threshold(self):
        resonance, status = classify_resonance(1.0, True)
        assert resonance == "coherent"
        assert status == "pass"

    def test_drifting_at_lower_threshold(self):
        resonance, status = classify_resonance(_PSI_DRIFTING, True)
        assert resonance == "drifting"
        assert status == "warn"

    def test_drifting_just_below_coherent(self):
        resonance, status = classify_resonance(_PSI_COHERENT - 0.001, True)
        assert resonance == "drifting"
        assert status == "warn"

    def test_fault_below_drifting(self):
        resonance, status = classify_resonance(_PSI_DRIFTING - 0.001, True)
        assert resonance == "fault"
        assert status == "fail"

    def test_fault_at_zero_psi(self):
        resonance, status = classify_resonance(0.0, True)
        assert resonance == "fault"
        assert status == "fail"


# ===========================================================================
# check_node_resonance — schema
# ===========================================================================

class TestCheckNodeResonanceSchema:
    """Verify the returned dict always has the required keys and value types."""

    REQUIRED_KEYS = {
        "node", "status", "reachable", "latency_ms", "resonance",
        "psi", "phase_offset_rad", "frequency_hz", "timestamp",
        "checks", "error_code", "error_message",
    }
    CHECK_KEYS = {"transport", "schema", "heartbeat"}

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_all_keys_present(self, node):
        result = check_node_resonance(node)
        assert self.REQUIRED_KEYS <= result.keys()

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_checks_subkeys(self, node):
        result = check_node_resonance(node)
        assert self.CHECK_KEYS <= result["checks"].keys()

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_status_values(self, node):
        result = check_node_resonance(node)
        assert result["status"] in {"pass", "warn", "fail"}

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_resonance_values(self, node):
        result = check_node_resonance(node)
        assert result["resonance"] in {"coherent", "drifting", "offline", "fault"}

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_psi_in_unit_interval(self, node):
        result = check_node_resonance(node)
        assert 0.0 <= result["psi"] <= 1.0

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_node_field_matches_input(self, node):
        result = check_node_resonance(node)
        assert result["node"] == node

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_frequency_matches_catalog(self, node):
        result = check_node_resonance(node)
        assert result["frequency_hz"] == NODE_CATALOG[node]["frequency_hz"]

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_timestamp_is_iso_string(self, node):
        result = check_node_resonance(node)
        ts = result["timestamp"]
        assert isinstance(ts, str)
        # Must be parseable as ISO-8601
        from datetime import datetime
        datetime.fromisoformat(ts)


# ===========================================================================
# check_node_resonance — simulation mode (no overrides)
# ===========================================================================

class TestCheckNodeResonanceSimulation:
    @pytest.mark.parametrize("node", MCP_NODES)
    def test_known_nodes_are_reachable_by_default(self, node):
        result = check_node_resonance(node)
        assert result["reachable"] is True

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_known_nodes_pass_by_default(self, node):
        result = check_node_resonance(node)
        assert result["status"] == "pass"
        assert result["resonance"] == "coherent"

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_known_nodes_have_no_error(self, node):
        result = check_node_resonance(node)
        assert result["error_code"] is None
        assert result["error_message"] is None

    @pytest.mark.parametrize("node", MCP_NODES)
    def test_checks_all_ok_by_default(self, node):
        result = check_node_resonance(node)
        assert result["checks"]["transport"] == "ok"
        assert result["checks"]["schema"] == "ok"
        assert result["checks"]["heartbeat"] == "ok"

    def test_all_nodes_list_matches_catalog(self):
        """All 7 MCP_NODES must be present in NODE_CATALOG."""
        for node in MCP_NODES:
            assert node in NODE_CATALOG


# ===========================================================================
# check_node_resonance — override mode
# ===========================================================================

class TestCheckNodeResonanceOverrides:
    def test_unreachable_override(self):
        result = check_node_resonance("dramaturgo", reachable=False)
        assert result["reachable"] is False
        assert result["resonance"] == "offline"
        assert result["status"] == "fail"
        assert result["error_code"] == "NODE_UNREACHABLE"

    def test_high_latency_degrades_psi(self):
        result_fast = check_node_resonance("auron-governor", latency_ms=5.0)
        result_slow = check_node_resonance("auron-governor", latency_ms=90.0)
        assert result_slow["psi"] < result_fast["psi"]

    def test_large_phase_offset_degrades_psi(self):
        result_aligned = check_node_resonance("141-hz", phase_offset_rad=0.01)
        result_drifted = check_node_resonance("141-hz", phase_offset_rad=0.19)
        assert result_drifted["psi"] < result_aligned["psi"]

    def test_heartbeat_fail_gives_zero_psi(self):
        result = check_node_resonance("github-mcp-server", heartbeat_ok=False)
        assert result["psi"] == pytest.approx(0.0)
        assert result["checks"]["heartbeat"] == "fail"

    def test_schema_fail_gives_zero_psi(self):
        result = check_node_resonance("github-mcp-server", schema_ok=False)
        assert result["psi"] == pytest.approx(0.0)
        assert result["checks"]["schema"] == "fail"

    def test_transport_fail_recorded_in_checks(self):
        result = check_node_resonance("dramaturgo", transport_ok=False)
        assert result["checks"]["transport"] == "fail"

    def test_latency_ms_stored_rounded(self):
        result = check_node_resonance("3d-navier-stokes", latency_ms=12.456789)
        assert result["latency_ms"] == pytest.approx(12.457, abs=1e-3)

    def test_phase_offset_stored_rounded(self):
        result = check_node_resonance("interferometro-noesico", phase_offset_rad=0.123456789)
        assert result["phase_offset_rad"] == pytest.approx(0.123457, abs=1e-6)


# ===========================================================================
# check_node_resonance — unknown node
# ===========================================================================

class TestCheckNodeResonanceUnknown:
    def test_unknown_node_is_not_reachable(self):
        result = check_node_resonance("nonexistent-node")
        assert result["reachable"] is False
        assert result["resonance"] == "offline"
        assert result["status"] == "fail"

    def test_unknown_node_has_error_code(self):
        result = check_node_resonance("nonexistent-node")
        assert result["error_code"] == "UNKNOWN_NODE"
        assert "nonexistent-node" in result["error_message"]

    def test_unknown_node_frequency_is_zero(self):
        result = check_node_resonance("ghost")
        assert result["frequency_hz"] == 0.0


# ===========================================================================
# check_node_resonance — full bus sweep (integration)
# ===========================================================================

class TestCheckNodeResonanceBusSweep:
    def test_sweep_returns_seven_results(self):
        results = [check_node_resonance(n) for n in MCP_NODES]
        assert len(results) == 7

    def test_all_nodes_distinct_in_sweep(self):
        results = [check_node_resonance(n) for n in MCP_NODES]
        node_names = [r["node"] for r in results]
        assert len(set(node_names)) == 7

    def test_frequency_distribution(self):
        """Verify expected frequency assignments in the catalog."""
        assert NODE_CATALOG["dramaturgo"]["frequency_hz"] == pytest.approx(888.0)
        assert NODE_CATALOG["github-mcp-server"]["frequency_hz"] == pytest.approx(141.7001)
        assert NODE_CATALOG["auron-governor"]["frequency_hz"] == pytest.approx(50.0)
        assert NODE_CATALOG["141-hz"]["frequency_hz"] == pytest.approx(141.7001)
        assert NODE_CATALOG["3d-navier-stokes"]["frequency_hz"] == pytest.approx(141.7001)
        assert NODE_CATALOG["interferometro-noesico"]["frequency_hz"] == pytest.approx(283.4002)
        assert NODE_CATALOG["biologia-cuantica-noesica"]["frequency_hz"] == pytest.approx(70.85005)
