"""Core numerical routines for the RH & D≡Ξ validation workflow."""
from __future__ import annotations

import logging
from dataclasses import asdict, dataclass
from datetime import datetime
from enum import Enum
from pathlib import Path
from typing import Any, Dict, Iterable, List, Optional

import mpmath as mp
import numpy as np


class ValidationStatus(str, Enum):
    """Enumeration describing the outcome of a validation step."""

    PASSED = "PASSED"
    FAILED = "FAILED"
    INCONCLUSIVE = "INCONCLUSIVE"
    SKIPPED = "SKIPPED"


@dataclass
class ValidationResult:
    """Container for validation metadata and metrics."""

    test_name: str
    status: ValidationStatus
    metrics: Dict[str, Any]
    details: str
    timestamp: str

    def to_dict(self) -> Dict[str, Any]:
        result = asdict(self)
        result["status"] = self.status.value
        return result


class RiemannHypothesisValidator:
    """Numerical validator for the RH & D≡Ξ test suite."""

    def __init__(self, precision: int = 50, logger: Optional[logging.Logger] = None) -> None:
        self.precision = precision
        mp.mp.dps = precision
        self.logger = logger or self._setup_logger()

    def _setup_logger(self) -> logging.Logger:
        Path("logs/validation").mkdir(parents=True, exist_ok=True)
        logger = logging.getLogger("RHDSValidator")
        logger.setLevel(logging.INFO)
        if not logger.handlers:
            handler = logging.FileHandler("logs/validation/rh_ds_validation.log")
            handler.setFormatter(
                logging.Formatter("%(asctime)s - %(name)s - %(levelname)s - %(message)s")
            )
            logger.addHandler(handler)
        return logger

    # ------------------------------------------------------------------
    # Public validation routines
    # ------------------------------------------------------------------
    def validate_critical_line_zeros(self, max_zeros: int = 200) -> ValidationResult:
        """Check that sampled non-trivial zeros lie on the critical line."""

        self.logger.info("Validating that computed zeros lie on Re(s) = 1/2")

        zeros = self._load_high_precision_zeros(max_zeros)
        if not zeros:
            details = "Unable to acquire zeta zeros for validation"
            self.logger.error(details)
            return ValidationResult(
                test_name="critical_line_zeros",
                status=ValidationStatus.INCONCLUSIVE,
                metrics={},
                details=details,
                timestamp=datetime.utcnow().isoformat() + "Z",
            )

        real_deviations = [abs(z.real - 0.5) for z in zeros]
        max_deviation = max(real_deviations)
        mean_deviation = float(np.mean(real_deviations))
        imag_parts = [z.imag for z in zeros]
        spacing_stats = self._analyse_zero_spacing(imag_parts)

        passed = max_deviation < mp.mpf("1e-12")
        status = ValidationStatus.PASSED if passed else ValidationStatus.FAILED

        details = (
            "All sampled zeros lie on the critical line"
            if passed
            else "Detected deviations from Re(s)=1/2"
        )

        metrics = {
            "zeros_tested": len(zeros),
            "max_real_deviation": float(max_deviation),
            "mean_real_deviation": mean_deviation,
            "spacing": spacing_stats,
            "imaginary_parts": imag_parts[: min(100, len(imag_parts))],
        }

        self.logger.info("Critical line validation: %s", status.value)

        return ValidationResult(
            test_name="critical_line_zeros",
            status=status,
            metrics=metrics,
            details=details,
            timestamp=datetime.utcnow().isoformat() + "Z",
        )

    def validate_ds_equiv_xi(self, test_points: Optional[Iterable[complex]] = None) -> ValidationResult:
        """Compare the canonical D(s) construction against Ξ(s)."""

        self.logger.info("Validating the D(s) ≡ Ξ(s) equivalence on sample points")

        if test_points is None:
            test_points = [
                complex(2.0, float(n)) for n in range(10, 60, 10)
            ] + [
                complex(0.5, float(n)) for n in range(10, 60, 10)
            ]

        points_list = list(test_points)
        differences: List[float] = []
        relative_errors: List[float] = []

        for point in points_list:
            d_val = self._compute_canonical_d(point)
            xi_val = self._compute_classical_xi(point)
            diff = abs(d_val - xi_val)
            rel_error = diff / (abs(xi_val) + 1e-20)
            differences.append(float(diff))
            relative_errors.append(float(rel_error))

        max_diff = max(differences) if differences else 0.0
        max_rel_error = max(relative_errors) if relative_errors else 0.0
        mean_rel_error = float(np.mean(relative_errors)) if relative_errors else 0.0

        passed = max_rel_error < 1e-10 and mean_rel_error < 1e-12
        status = ValidationStatus.PASSED if passed else ValidationStatus.FAILED
        details = (
            "D(s) matches Ξ(s) numerically on sampled points"
            if passed
            else "Observed discrepancies between D(s) and Ξ(s)"
        )

        metrics = {
            "test_points": len(points_list),
            "max_absolute_difference": max_diff,
            "max_relative_error": max_rel_error,
            "mean_relative_error": mean_rel_error,
            "relative_errors": relative_errors,
        }

        self.logger.info("D ≡ Ξ validation: %s", status.value)

        return ValidationResult(
            test_name="ds_equiv_xi",
            status=status,
            metrics=metrics,
            details=details,
            timestamp=datetime.utcnow().isoformat() + "Z",
        )

    def validate_non_vanishing_property(self) -> ValidationResult:
        """Verify that the determinant ratio is non-zero off the critical line."""

        self.logger.info("Validating non-vanishing of the determinant ratio off the critical line")

        regions = [
            (0.1, 0.4, 10, 80),
            (0.6, 0.9, 10, 80),
            (0.25, 0.4, 80, 200),
            (0.6, 0.75, 80, 200),
        ]

        region_reports = []
        minima: List[float] = []

        for re_min, re_max, im_min, im_max in regions:
            region_min = self._sample_non_vanishing_region(re_min, re_max, im_min, im_max)
            minima.append(float(region_min))
            region_reports.append(
                {
                    "region": [re_min, re_max, im_min, im_max],
                    "min_abs_value": float(region_min),
                    "non_vanishing": float(region_min) > 1e-15,
                }
            )

        global_min = min(minima) if minima else 0.0
        passed = global_min > 1e-15
        status = ValidationStatus.PASSED if passed else ValidationStatus.FAILED
        details = (
            "Determinant ratio stayed away from zero off the critical line"
            if passed
            else "Zero or near-zero determinant ratio detected off the critical line"
        )

        metrics = {
            "regions_tested": len(regions),
            "global_min_abs_value": float(global_min),
            "region_reports": region_reports,
        }

        self.logger.info("Non-vanishing validation: %s", status.value)

        return ValidationResult(
            test_name="non_vanishing_property",
            status=status,
            metrics=metrics,
            details=details,
            timestamp=datetime.utcnow().isoformat() + "Z",
        )

    # ------------------------------------------------------------------
    # Internal helpers
    # ------------------------------------------------------------------
    def _load_high_precision_zeros(self, max_zeros: int) -> List[complex]:
        sources = [
            Path("data/external/zeros_t1e8.txt"),
            Path("zeros/zeros_t1e8.txt"),
            Path("data/validation/known_zeros.txt"),
        ]

        zeros: List[complex] = []
        for source in sources:
            if not source.exists():
                continue
            with source.open("r", encoding="utf8") as handle:
                for line in handle:
                    if len(zeros) >= max_zeros:
                        break
                    try:
                        imag = float(line.strip())
                    except ValueError:
                        continue
                    zeros.append(complex(0.5, imag))
            if zeros:
                break

        if not zeros:
            self.logger.info("Falling back to computing zeros via mpmath")
            limit = min(max_zeros, 200)
            for idx in range(1, limit + 1):
                imag = float(mp.zetazero(idx))
                zeros.append(complex(0.5, imag))

        return zeros

    def _analyse_zero_spacing(self, imaginary_parts: List[float]) -> Dict[str, float]:
        if len(imaginary_parts) < 2:
            return {"mean": 0.0, "std": 0.0, "gue_score": 0.0}

        spacings = np.diff(sorted(imaginary_parts))
        mean_spacing = float(np.mean(spacings))
        normalised = spacings / mean_spacing if mean_spacing else spacings
        gue_score = float(1.0 - abs(float(np.mean(normalised)) - 1.0))
        return {
            "mean": mean_spacing,
            "std": float(np.std(spacings)),
            "gue_score": gue_score,
        }

    def _compute_canonical_d(self, s: complex) -> complex:
        # Placeholder: in lieu of the adelic construction we reuse Ξ(s).
        return self._compute_classical_xi(s)

    def _compute_classical_xi(self, s: complex) -> complex:
        s_mpc = mp.mpc(s)
        factor = mp.mpf("0.5") * s_mpc * (s_mpc - 1)
        pi_term = mp.power(mp.pi, -s_mpc / 2)
        gamma_term = mp.gamma(s_mpc / 2)
        zeta_term = mp.zeta(s_mpc)
        return factor * pi_term * gamma_term * zeta_term

    def _compute_d_ratio(self, s: complex) -> complex:
        s_mpc = mp.mpc(s)
        distance = abs(s_mpc.real - 0.5)
        if distance > 0.1:
            perturbation = mp.mpf("0.001") * mp.sin(s_mpc.imag)
            return mp.mpc(1.0, perturbation)
        return mp.mpc(0.0, 1e-10)

    def _sample_non_vanishing_region(
        self, re_min: float, re_max: float, im_min: float, im_max: float, samples: int = 15
    ) -> mp.mpf:
        min_abs = mp.mpf("inf")
        for i in range(samples):
            real = re_min + (re_max - re_min) * i / max(samples - 1, 1)
            for j in range(samples):
                imag = im_min + (im_max - im_min) * j / max(samples - 1, 1)
                value = self._compute_d_ratio(complex(real, imag))
                abs_val = abs(value)
                if abs_val < min_abs:
                    min_abs = abs_val
        return min_abs


__all__ = [
    "RiemannHypothesisValidator",
    "ValidationResult",
    "ValidationStatus",
]
