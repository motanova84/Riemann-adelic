"""
🧠 Copilot Prompt:
Enhance this script to:
- Check if zeros_t1e8.txt already exists.
- If not, download from Odlyzko and decompress.
- Validate format (float per line).
- Move the cleaned file to zeros/ and print "✅ Ready".

Also suggest adding this step to a GitHub Action on first run.
"""

import requests
import gzip
import os
from pathlib import Path

def download_and_extract(url, out_txt):
    """Download and extract gzipped file from URL."""
    gz_path = out_txt + ".gz"
    print(f"🔽 Downloading: {url}")

    try:
        r = requests.get(url, stream=True, timeout=30)
        r.raise_for_status()

        with open(gz_path, 'wb') as f:
            for chunk in r.iter_content(chunk_size=8192):
                f.write(chunk)

        print("✅ Downloaded. Extracting...")

        with gzip.open(gz_path, 'rb') as gz_in:
            with open(out_txt, 'wb') as txt_out:
                txt_out.write(gz_in.read())

        os.remove(gz_path)
        print(f"📂 Saved to: {out_txt}")
        return True

    except Exception as e:
        print(f"❌ Error downloading {url}: {e}")
        if os.path.exists(gz_path):
            os.remove(gz_path)
        return False

def validate_zeros_file(filename):
    """Validate that zeros file contains valid floating point numbers."""
    if not os.path.exists(filename):
        return False, "File does not exist"

    try:
        valid_lines = 0
        invalid_lines = 0

        with open(filename, 'r') as f:
            for line_num, line in enumerate(f, 1):
                line = line.strip()
                if not line:  # Skip empty lines
                    continue

                try:
                    # Try to parse as float
                    float(line)
                    valid_lines += 1
                except ValueError:
                    invalid_lines += 1
                    if invalid_lines < 10:  # Only report first few errors
                        print(f"⚠️  Invalid line {line_num}: '{line}'")

                # Stop checking after reasonable number of lines
                if line_num > 1000:
                    break

        if invalid_lines > 0:
            return False, f"Found {invalid_lines} invalid lines out of {valid_lines + invalid_lines} checked"

        return True, f"Validated {valid_lines} zeros successfully"

    except Exception as e:
        return False, f"Error validating file: {e}"

def ensure_zeros_available():
    """Ensure that zeros files are available, downloading if necessary."""
    zeros_dir = Path("zeros")
    zeros_dir.mkdir(exist_ok=True)

    # Check main zeros file
    zeros_file = zeros_dir / "zeros_t1e8.txt"

    if zeros_file.exists():
        print(f"✅ Zeros file already exists: {zeros_file}")
        is_valid, msg = validate_zeros_file(zeros_file)
        if is_valid:
            print(f"✅ Validation passed: {msg}")
            return True
        else:
            print(f"❌ Validation failed: {msg}")
            print("🔄 Will attempt to re-download...")
            zeros_file.unlink()  # Delete invalid file

    # Try to download from known sources
    odlyzko_sources = [
        "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeros1",
        "https://www.dtc.umn.edu/~odlyzko/zeta_tables/zeta1.0e8_1e4_1e6.txt.gz"
    ]

    for url in odlyzko_sources:
        print(f"🔄 Attempting download from: {url}")
        if download_and_extract(url, str(zeros_file)):
            is_valid, msg = validate_zeros_file(zeros_file)
            if is_valid:
                print(f"✅ Successfully downloaded and validated: {msg}")
                return True
            else:
                print(f"❌ Downloaded file failed validation: {msg}")
                zeros_file.unlink()

    print("❌ Failed to download valid zeros file from all sources")
    return False

# Legacy function for backwards compatibility
def main():
    """Download zeros files (legacy interface)."""
    return ensure_zeros_available()

if __name__ == "__main__":
    success = main()
    if success:
        print("✅ Ready")
    else:
        print("❌ Failed to ensure zeros availability")
        exit(1)

