#!/usr/bin/env python3
"""
Unit tests for validate_lean_env.py

Tests the validation script functionality including:
- File validation
- Sorry counting
- Theorem detection
- Report generation
"""

import json
import os
import sys
import tempfile
import unittest
from pathlib import Path

# Add formalization/lean to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent / "formalization" / "lean"))

import validate_lean_env


class TestValidateLeanEnv(unittest.TestCase):
    """Test suite for validate_lean_env.py"""

    def setUp(self):
        """Set up test fixtures"""
        self.test_dir = tempfile.mkdtemp()
        self.test_dir_path = Path(self.test_dir)

    def tearDown(self):
        """Clean up test fixtures"""
        import shutil
        shutil.rmtree(self.test_dir, ignore_errors=True)

    def test_count_sorry_zero(self):
        """Test counting sorries when file has none"""
        test_file = self.test_dir_path / "test.lean"
        test_file.write_text("def myFunc := 42\ntheorem myTheorem : True := trivial")
        
        count = validate_lean_env.count_sorry(test_file)
        self.assertEqual(count, 0)

    def test_count_sorry_multiple(self):
        """Test counting multiple sorries"""
        test_file = self.test_dir_path / "test.lean"
        test_file.write_text("theorem a : True := sorry\ntheorem b : False := sorry\ntheorem c := sorry")
        
        count = validate_lean_env.count_sorry(test_file)
        self.assertEqual(count, 3)

    def test_count_sorry_with_word_boundaries(self):
        """Test that sorry is counted only as whole word"""
        test_file = self.test_dir_path / "test.lean"
        test_file.write_text("-- comment about sorry\ntheorem a : True := sorry\n-- sorryish")
        
        count = validate_lean_env.count_sorry(test_file)
        # Counts both occurrences of "sorry" as whole words (in comment and in code)
        self.assertEqual(count, 2)

    def test_count_sorry_missing_file(self):
        """Test counting sorries for missing file"""
        test_file = self.test_dir_path / "nonexistent.lean"
        
        count = validate_lean_env.count_sorry(test_file)
        self.assertEqual(count, -1)

    def test_validate_theorem_present(self):
        """Test theorem detection when present"""
        test_file = self.test_dir_path / "RH_final.lean"
        test_file.write_text("def RiemannHypothesis : Prop := ∀ s, s.re = 1/2")
        
        result = validate_lean_env.validate_theorem(test_file)
        self.assertTrue(result)

    def test_validate_theorem_alternative_name(self):
        """Test theorem detection with alternative naming"""
        test_file = self.test_dir_path / "RH_final.lean"
        test_file.write_text("theorem riemann_hypothesis_adelic : True := sorry")
        
        result = validate_lean_env.validate_theorem(test_file)
        self.assertTrue(result)

    def test_validate_theorem_absent(self):
        """Test theorem detection when absent"""
        test_file = self.test_dir_path / "RH_final.lean"
        test_file.write_text("def otherStuff := 42")
        
        result = validate_lean_env.validate_theorem(test_file)
        self.assertFalse(result)

    def test_validate_modules_structure(self):
        """Test module validation returns correct structure"""
        # Create test files
        (self.test_dir_path / "D_explicit.lean").write_text("theorem a := sorry")
        (self.test_dir_path / "de_branges.lean").write_text("def b := 42")
        
        # Temporarily override BASE_DIR
        original_base_dir = validate_lean_env.BASE_DIR
        validate_lean_env.BASE_DIR = self.test_dir_path
        
        try:
            results = validate_lean_env.validate_modules()
            
            # Check structure
            self.assertIn("D_explicit.lean", results)
            self.assertIn("de_branges.lean", results)
            
            # Check D_explicit.lean
            self.assertTrue(results["D_explicit.lean"]["exists"])
            self.assertEqual(results["D_explicit.lean"]["sorries"], 1)
            self.assertFalse(results["D_explicit.lean"]["verified"])
            
            # Check de_branges.lean
            self.assertTrue(results["de_branges.lean"]["exists"])
            self.assertEqual(results["de_branges.lean"]["sorries"], 0)
            self.assertTrue(results["de_branges.lean"]["verified"])
            
        finally:
            validate_lean_env.BASE_DIR = original_base_dir

    def test_run_command_success(self):
        """Test run_command with successful command"""
        code, out, err = validate_lean_env.run_command("echo 'test'")
        
        self.assertEqual(code, 0)
        self.assertEqual(out, "test")

    def test_run_command_failure(self):
        """Test run_command with failing command"""
        code, out, err = validate_lean_env.run_command("exit 1")
        
        self.assertNotEqual(code, 0)

    def test_get_lean_version_not_installed(self):
        """Test getting Lean version when not installed"""
        version = validate_lean_env.get_lean_version()
        
        # Should return error message when lean not in PATH
        self.assertIn("not installed", version.lower())


class TestValidateLeanEnvIntegration(unittest.TestCase):
    """Integration tests for validate_lean_env.py"""

    def test_actual_lean_files_exist(self):
        """Test that actual Lean files exist in repository"""
        lean_dir = Path(__file__).parent.parent / "formalization" / "lean"
        
        # Check for key files
        self.assertTrue((lean_dir / "RH_final.lean").exists())
        self.assertTrue((lean_dir / "RiemannAdelic" / "D_explicit.lean").exists())

    def test_validate_report_json_format(self):
        """Test that generated JSON report has correct format"""
        lean_dir = Path(__file__).parent.parent / "formalization" / "lean"
        report_path = lean_dir / "validation_report.json"
        
        if report_path.exists():
            with open(report_path, 'r') as f:
                report = json.load(f)
            
            # Check required fields
            self.assertIn("timestamp", report)
            self.assertIn("project", report)
            self.assertIn("lean_version", report)
            self.assertIn("build_success", report)
            self.assertIn("build_time_sec", report)
            self.assertIn("warnings", report)
            self.assertIn("errors", report)
            self.assertIn("modules", report)
            self.assertIn("theorem_detected", report)
            self.assertIn("summary", report)
            
            # Check summary structure
            self.assertIn("status", report["summary"])
            self.assertIn("message", report["summary"])


if __name__ == "__main__":
    unittest.main()
