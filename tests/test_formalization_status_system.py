#!/usr/bin/env python3
"""
Test script to verify the formalization status tracking system.
"""

import json
import subprocess
import sys
from pathlib import Path


def test_counter_script():
    """Test that the counter script runs and produces valid output."""
    print("Testing count_formalization_status.py...")
    
    # Run the counter
    result = subprocess.run(
        [
            "python3", "scripts/count_formalization_status.py",
            "--json", "/tmp/test_status.json",
            "--markdown", "/tmp/test_status.md"
        ],
        capture_output=True,
        text=True
    )
    
    if result.returncode != 0:
        print(f"❌ Counter script failed to run: {result.stderr}")
        return False
    
    # Check JSON output
    if not Path("/tmp/test_status.json").exists():
        print("❌ JSON file was not created")
        return False
    
    # Validate JSON structure
    try:
        with open("/tmp/test_status.json") as f:
            data = json.load(f)
        
        required_keys = [
            "timestamp", "total_files", "sorry_count", "admit_count",
            "axiom_count", "total_incomplete", "top_files", "status_summary"
        ]
        
        for key in required_keys:
            if key not in data:
                print(f"❌ Missing key in JSON: {key}")
                return False
        
        # Validate data types
        if not isinstance(data["total_files"], int):
            print("❌ total_files is not an integer")
            return False
        
        if not isinstance(data["top_files"], list):
            print("❌ top_files is not a list")
            return False
        
    except json.JSONDecodeError as e:
        print(f"❌ Invalid JSON: {e}")
        return False
    
    # Check Markdown output
    if not Path("/tmp/test_status.md").exists():
        print("❌ Markdown file was not created")
        return False
    
    with open("/tmp/test_status.md") as f:
        md_content = f.read()
    
    if "## 📊 Estado de Formalización Lean 4" not in md_content:
        print("❌ Markdown file missing expected header")
        return False
    
    print("✅ Counter script test passed")
    return True


def test_readme_updater():
    """Test that the README updater script works."""
    print("\nTesting update_readme_status.py...")
    
    # Create a test README
    test_readme = "/tmp/test_readme.md"
    with open(test_readme, "w") as f:
        f.write("""# Test README

Some content here.

## Section 1

More content.

<!-- AUTO-GENERATED: Formalization Status - DO NOT EDIT MANUALLY -->
Old status here
<!-- END AUTO-GENERATED: Formalization Status -->

## Section 2

Final content.
""")
    
    # Run the updater
    result = subprocess.run(
        [
            "python3", "scripts/update_readme_status.py",
            "--status-json", "/tmp/test_status.json",
            "--readme", test_readme
        ],
        capture_output=True,
        text=True
    )
    
    if result.returncode != 0:
        print(f"❌ README updater script failed to run: {result.stderr}")
        return False
    
    # Check that README was updated
    with open(test_readme) as f:
        updated_content = f.read()
    
    if "Old status here" in updated_content:
        print("❌ README was not updated (old content still present)")
        return False
    
    if "AUTO-GENERATED: Formalization Status" not in updated_content:
        print("❌ README markers were removed")
        return False
    
    if "Estado de Formalización Lean 4" not in updated_content:
        print("❌ New status section was not added")
        return False
    
    print("✅ README updater test passed")
    return True


def test_readme_markers_in_actual_file():
    """Test that the actual README has the correct markers."""
    print("\nTesting actual README.md...")
    
    readme_path = "README.md"
    if not Path(readme_path).exists():
        print("⚠️  README.md not found (skipping test)")
        return True
    
    with open(readme_path) as f:
        content = f.read()
    
    if "<!-- AUTO-GENERATED: Formalization Status - DO NOT EDIT MANUALLY -->" not in content:
        print("⚠️  README.md missing start marker (may need initial update)")
        return True
    
    if "<!-- END AUTO-GENERATED: Formalization Status -->" not in content:
        print("❌ README.md missing end marker")
        return False
    
    # Check that there's content between markers
    import re
    pattern = r'<!-- AUTO-GENERATED: Formalization Status.*?-->(.*?)<!-- END AUTO-GENERATED: Formalization Status -->'
    match = re.search(pattern, content, re.DOTALL)
    
    if not match:
        print("❌ Could not find content between markers")
        return False
    
    section_content = match.group(1).strip()
    if len(section_content) < 100:
        print("❌ Auto-generated section seems too short")
        return False
    
    print("✅ Actual README.md test passed")
    return True


def test_data_files_exist():
    """Test that the data files were created."""
    print("\nTesting generated data files...")
    
    json_path = Path("data/formalization_status.json")
    md_path = Path("data/formalization_status.md")
    
    if not json_path.exists():
        print("❌ data/formalization_status.json does not exist")
        return False
    
    if not md_path.exists():
        print("❌ data/formalization_status.md does not exist")
        return False
    
    # Validate JSON
    try:
        with open(json_path) as f:
            data = json.load(f)
        
        if data["total_incomplete"] < 0:
            print("❌ Invalid total_incomplete value")
            return False
        
    except Exception as e:
        print(f"❌ Error reading JSON: {e}")
        return False
    
    print("✅ Data files test passed")
    return True


def main():
    """Run all tests."""
    print("=" * 60)
    print("  Formalization Status System Tests")
    print("=" * 60)
    print()
    
    tests = [
        test_counter_script,
        test_readme_updater,
        test_readme_markers_in_actual_file,
        test_data_files_exist,
    ]
    
    results = []
    for test in tests:
        try:
            results.append(test())
        except Exception as e:
            print(f"❌ Test failed with exception: {e}")
            results.append(False)
    
    print()
    print("=" * 60)
    print(f"  Results: {sum(results)}/{len(results)} tests passed")
    print("=" * 60)
    
    if all(results):
        print("\n✅ All tests passed!")
        return 0
    else:
        print("\n❌ Some tests failed")
        return 1


if __name__ == "__main__":
    sys.exit(main())
