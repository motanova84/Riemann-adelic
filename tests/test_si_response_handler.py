#!/usr/bin/env python3
"""
Tests for si_response_handler module.
"""

import pytest
from si_response_handler import handle_si_response


class TestSiResponseHandler:
    """Test cases for the si response handler."""
    
    def test_si_lowercase(self):
        """Test lowercase 'si' returns True."""
        assert handle_si_response("si") is True
    
    def test_si_with_accent(self):
        """Test 'sí' with accent returns True."""
        assert handle_si_response("sí") is True
    
    def test_si_uppercase(self):
        """Test uppercase 'SI' returns True."""
        assert handle_si_response("SI") is True
    
    def test_yes(self):
        """Test 'yes' returns True."""
        assert handle_si_response("yes") is True
    
    def test_yes_uppercase(self):
        """Test uppercase 'YES' returns True."""
        assert handle_si_response("YES") is True
    
    def test_single_y(self):
        """Test single 'y' returns True."""
        assert handle_si_response("y") is True
    
    def test_single_s(self):
        """Test single 's' returns True."""
        assert handle_si_response("s") is True
    
    def test_no(self):
        """Test 'no' returns False."""
        assert handle_si_response("no") is False
    
    def test_empty_string(self):
        """Test empty string returns False."""
        assert handle_si_response("") is False
    
    def test_whitespace(self):
        """Test string with only whitespace returns False."""
        assert handle_si_response("   ") is False
    
    def test_si_with_whitespace(self):
        """Test 'si' with surrounding whitespace returns True."""
        assert handle_si_response("  si  ") is True
    
    def test_non_string_input(self):
        """Test non-string input returns False."""
        assert handle_si_response(None) is False
        assert handle_si_response(123) is False
        assert handle_si_response([]) is False
    
    def test_mixed_case(self):
        """Test mixed case 'Si' returns True."""
        assert handle_si_response("Si") is True
        assert handle_si_response("sI") is True
        assert handle_si_response("Sí") is True


if __name__ == "__main__":
    pytest.main([__file__, "-v"])
