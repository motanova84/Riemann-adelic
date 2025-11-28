#!/usr/bin/env python3
"""
Riemann Zeta Zeros Fetching Script

This script fetches Odlyzko's verified Riemann zeta zeros data.
It serves as a root-level wrapper for the utils/fetch_odlyzko.py module.

Usage:
    python fetch_odlyzko.py --precision t1e8
    python fetch_odlyzko.py --height 1e8
    python fetch_odlyzko.py --min_zeros

Precision levels:
    t1e8  - Zeros up to T ~ 10^8 (default)
    t1e10 - Zeros up to T ~ 10^10
    t1e12 - Zeros up to T ~ 10^12
"""

import sys
import os
import importlib.util

# Import the fetch_odlyzko module directly to avoid triggering utils/__init__.py
# which has additional dependencies
_script_dir = os.path.dirname(os.path.abspath(__file__))
_module_path = os.path.join(_script_dir, 'utils', 'fetch_odlyzko.py')

spec = importlib.util.spec_from_file_location("fetch_odlyzko_module", _module_path)
fetch_module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(fetch_module)

if __name__ == "__main__":
    fetch_module.main()
