"""
Example Test with QCAL Logging
================================

This test demonstrates the comprehensive logging features of the QCAL framework.
It shows how to use the qcal_logger fixture for detailed test execution logging.

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
ORCID: 0009-0002-1923-0773
"""

import pytest


class TestLoggingExample:
    """Example test class demonstrating QCAL logging."""
    
    def test_basic_logging(self, qcal_logger):
        """Basic test with simple logging."""
        qcal_logger.log_test_start(
            "test_basic_logging",
            "Demonstrates basic logging functionality"
        )
        
        # Perform test
        result = 2 + 2
        
        # Log the result
        qcal_logger.log_checkpoint("Addition completed")
        qcal_logger.log_metric("result", result, "")
        
        assert result == 4
        
        qcal_logger.log_success("Test passed successfully")
        qcal_logger.log_test_end("test_basic_logging", "passed")
    
    def test_validation_steps(self, qcal_logger):
        """Test with validation step logging."""
        qcal_logger.log_test_start(
            "test_validation_steps",
            "Demonstrates validation step logging"
        )
        
        # Step 1
        qcal_logger.log_validation_step(
            "Initialize parameters",
            step_number=1,
            total_steps=3,
            theory="Basic arithmetic"
        )
        x = 10
        qcal_logger.log_checkpoint("Parameters initialized", {"x": x})
        
        # Step 2
        qcal_logger.log_validation_step(
            "Perform computation",
            step_number=2,
            total_steps=3,
            theory="Multiplication theorem"
        )
        result = x * 2
        qcal_logger.log_metric("intermediate_result", result, "units")
        qcal_logger.log_checkpoint("Computation completed")
        
        # Step 3
        qcal_logger.log_validation_step(
            "Verify result",
            step_number=3,
            total_steps=3,
            theory="Equality verification"
        )
        assert result == 20
        qcal_logger.log_success("Result verified")
        
        qcal_logger.log_test_end("test_validation_steps", "passed")
    
    def test_with_metrics(self, qcal_logger):
        """Test demonstrating metric logging."""
        qcal_logger.log_test_start(
            "test_with_metrics",
            "Demonstrates comprehensive metric logging"
        )
        
        # QCAL constants
        base_frequency = 141.7001
        qcal_constant = 244.36
        precision = 30
        
        # Log QCAL metrics
        qcal_logger.log_metric("base_frequency", base_frequency, "Hz")
        qcal_logger.log_metric("qcal_constant", qcal_constant, "")
        qcal_logger.log_metric("precision", precision, "decimal places")
        
        # Compute coherence
        coherence = qcal_constant / base_frequency
        qcal_logger.log_metric("coherence_ratio", coherence, "")
        
        # Verify
        assert base_frequency > 0
        assert qcal_constant > 0
        
        qcal_logger.log_checkpoint("QCAL metrics verified")
        qcal_logger.log_success("All metrics within expected ranges")
        qcal_logger.log_test_end("test_with_metrics", "passed")
    
    def test_with_warnings(self, qcal_logger):
        """Test demonstrating warning logging."""
        qcal_logger.log_test_start(
            "test_with_warnings",
            "Demonstrates warning and debug logging"
        )
        
        # Debug information
        qcal_logger.debug("Starting computation with initial value")
        
        value = 100
        tolerance = 0.01
        
        # Warning for non-critical issue
        if value > 50:
            qcal_logger.log_warning(
                f"Value {value} exceeds recommended threshold of 50"
            )
        
        # Test still passes
        assert value > 0
        
        qcal_logger.log_checkpoint("Test completed with warnings")
        qcal_logger.log_test_end("test_with_warnings", "passed")
    
    def test_mathematical_validation(self, qcal_logger):
        """Test demonstrating mathematical proof validation logging."""
        qcal_logger.log_test_start(
            "test_mathematical_validation",
            "Mathematical proof validation example"
        )
        
        # Theorem: For all x, x² ≥ 0
        qcal_logger.log_validation_step(
            "Theorem Statement",
            step_number=1,
            total_steps=4,
            theory="Real number properties"
        )
        qcal_logger.log_checkpoint("Theorem: ∀x ∈ ℝ, x² ≥ 0")
        
        # Proof Step 1: Case x > 0
        qcal_logger.log_validation_step(
            "Case x > 0",
            step_number=2,
            total_steps=4,
            theory="Positive number multiplication"
        )
        x_positive = 5
        result_positive = x_positive ** 2
        assert result_positive > 0
        qcal_logger.log_metric("x_positive", x_positive, "")
        qcal_logger.log_metric("result_positive", result_positive, "")
        qcal_logger.log_checkpoint("Case x > 0 verified")
        
        # Proof Step 2: Case x < 0
        qcal_logger.log_validation_step(
            "Case x < 0",
            step_number=3,
            total_steps=4,
            theory="Negative number multiplication"
        )
        x_negative = -5
        result_negative = x_negative ** 2
        assert result_negative > 0
        qcal_logger.log_metric("x_negative", x_negative, "")
        qcal_logger.log_metric("result_negative", result_negative, "")
        qcal_logger.log_checkpoint("Case x < 0 verified")
        
        # Proof Step 3: Case x = 0
        qcal_logger.log_validation_step(
            "Case x = 0",
            step_number=4,
            total_steps=4,
            theory="Zero multiplication"
        )
        x_zero = 0
        result_zero = x_zero ** 2
        assert result_zero == 0
        qcal_logger.log_metric("x_zero", x_zero, "")
        qcal_logger.log_metric("result_zero", result_zero, "")
        qcal_logger.log_checkpoint("Case x = 0 verified")
        
        # Conclusion
        qcal_logger.log_success("Theorem proven: ∀x ∈ ℝ, x² ≥ 0 ✓")
        qcal_logger.log_test_end("test_mathematical_validation", "passed")


if __name__ == "__main__":
    # Run with: python -m pytest tests/test_logging_example.py -v
    pytest.main([__file__, "-v", "-s"])
