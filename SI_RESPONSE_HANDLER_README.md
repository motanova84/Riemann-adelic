# Si Response Handler

## Overview

A minimal Python module for handling affirmative responses in Spanish, particularly "si" (yes).

## Purpose

This module provides a simple, reusable function for processing user confirmations in Spanish. It's designed to handle various forms of affirmative responses including:

- "si" (Spanish for "yes")
- "sí" (with accent)
- "yes" (English)
- Single letter shortcuts: "y", "s"

## Usage

### Basic Example

```python
from si_response_handler import handle_si_response

# Check if a response is affirmative
if handle_si_response("si"):
    print("User confirmed!")
else:
    print("User declined.")
```

### Features

- **Case-insensitive**: Accepts "si", "Si", "SI", "SÍ", etc.
- **Whitespace handling**: Automatically trims leading/trailing whitespace
- **Multiple formats**: Supports both Spanish and English affirmative responses
- **Type safety**: Returns False for non-string inputs

## API Reference

### `handle_si_response(response: str) -> bool`

Checks if a response string represents an affirmative answer.

**Parameters:**
- `response` (str): The user's response string

**Returns:**
- `bool`: True if the response is affirmative, False otherwise

**Accepted affirmative responses:**
- "si", "sí" (Spanish)
- "yes" (English)
- "y" (yes shortcut)
- "s" (si shortcut)

**Examples:**
```python
>>> handle_si_response("si")
True
>>> handle_si_response("sí")
True
>>> handle_si_response("no")
False
>>> handle_si_response("  SI  ")
True
```

## Testing

Run the test suite:

```bash
python3 -m pytest tests/test_si_response_handler.py -v
```

Or run the module directly for a quick demo:

```bash
python3 si_response_handler.py
```

## Implementation Details

The handler:
1. Validates input type (returns False for non-strings)
2. Normalizes the input (lowercase, trimmed)
3. Checks against a list of known affirmative responses
4. Returns a boolean result

## Integration

This module is designed to be minimal and self-contained. It can be imported and used in any Python script that needs to process user confirmations, particularly in Spanish-language contexts.

## License

This module is part of the Riemann-Adelic project and follows the same licensing terms.
