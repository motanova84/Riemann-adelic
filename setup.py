#!/usr/bin/env python
"""
Setup script for backward compatibility with older dependency detection tools.
The primary configuration is in pyproject.toml (PEP 517/518).
This file is provided for compatibility with tools that don't yet support pyproject.toml.
"""

from setuptools import setup

# All configuration is in pyproject.toml
# This file exists only for backward compatibility with tools that don't support PEP 517/518
setup()
