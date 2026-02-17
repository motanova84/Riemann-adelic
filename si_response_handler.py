#!/usr/bin/env python3
"""
Simple response handler for "si" (yes) confirmations.

This module provides a minimal handler for processing affirmative responses
in Spanish, particularly "si" (yes).
"""


def handle_si_response(response: str) -> bool:
    """
    Handle a response and check if it's an affirmative "si" (yes).
    
    Args:
        response: The user's response string
        
    Returns:
        True if the response is affirmative (si/yes), False otherwise
        
    Examples:
        >>> handle_si_response("si")
        True
        >>> handle_si_response("sí")
        True
        >>> handle_si_response("SI")
        True
        >>> handle_si_response("no")
        False
    """
    if not isinstance(response, str):
        return False
    
    # Normalize the response
    normalized = response.strip().lower()
    
    # Check for affirmative responses in Spanish
    affirmative_responses = ["si", "sí", "yes", "y", "s"]
    
    return normalized in affirmative_responses


def main():
    """Main function for demonstration purposes."""
    test_responses = ["si", "sí", "SI", "yes", "no", ""]
    
    print("Testing si_response_handler:")
    print("-" * 40)
    for response in test_responses:
        result = handle_si_response(response)
        print(f"Response: '{response}' -> {result}")


if __name__ == "__main__":
    main()
