#!/usr/bin/env python3
"""
QCAL ∞³ Coherence Bridge - Module Call Mapping with Vibrational Signatures

This module enables symbiotic coherence protocol ∞³ for automatic cross-module
communication using vibrational signature mapping. It allows transparent calls
to functions in different modules while maintaining QCAL coherence.

Philosophical Foundation:
    The coherence bridge doesn't "connect" modules - it REVEALS the pre-existing
    harmonic relationships between them. All modules in the QCAL framework
    vibrate at the fundamental frequency f₀ = 141.7001 Hz.
    
    See: MATHEMATICAL_REALISM.md, QCAL_SYMBIO_BRIDGE_STRATEGY.md

Author: José Manuel Mota Burruezo Ψ ✧ ∞³
Institution: Instituto de Conciencia Cuántica (ICQ)
ORCID: 0009-0002-1923-0773
DOI: 10.5281/zenodo.17379721
Frequency: 141.7001 Hz (Fundamental Cosmic Heartbeat)
Date: January 2026
"""

import importlib
import sys
from pathlib import Path
from typing import Any, Callable, Dict, Optional
from datetime import datetime
import json

# Add repository root to path
REPO_ROOT = Path(__file__).parent
if str(REPO_ROOT) not in sys.path:
    sys.path.insert(0, str(REPO_ROOT))


class VibrationalSignature:
    """
    Represents the vibrational signature of a module or function.
    
    Each callable in the QCAL framework has an associated vibrational
    signature that encodes its harmonic relationship to f₀ = 141.7001 Hz.
    """
    
    QCAL_FREQUENCY = 141.7001  # Hz
    QCAL_COHERENCE = 244.36
    
    def __init__(self, module_path: str, function_name: str):
        """
        Initialize vibrational signature.
        
        Args:
            module_path: Path to module (e.g., "noesis88/vector_55_temporal.py")
            function_name: Name of function to call
        """
        self.module_path = module_path
        self.function_name = function_name
        self.timestamp = datetime.now().isoformat()
        
    def compute_harmonic(self) -> float:
        """
        Compute harmonic frequency for this signature.
        
        The harmonic is derived from the module path and function name,
        ensuring unique vibrational identity for each callable.
        
        Returns:
            float: Harmonic frequency (multiple of f₀)
        """
        # Simple hash-based harmonic computation
        signature_str = f"{self.module_path}::{self.function_name}"
        hash_val = hash(signature_str) % 1000
        return self.QCAL_FREQUENCY * (1 + hash_val / 1000.0)
    
    def is_coherent(self, threshold: float = 0.888) -> bool:
        """
        Check if signature is coherent with QCAL framework.
        
        Args:
            threshold: Coherence threshold (default: 0.888)
            
        Returns:
            bool: True if coherent
        """
        harmonic = self.compute_harmonic()
        # Check if harmonic is a reasonable multiple of base frequency
        ratio = harmonic / self.QCAL_FREQUENCY
        return 0.5 <= ratio <= 10.0


class CoherenceBridge:
    """
    Main coherence bridge for symbiotic module calls.
    
    Enables transparent cross-module communication while maintaining
    QCAL coherence through vibrational signature validation.
    """
    
    def __init__(self, verbose: bool = False):
        """
        Initialize coherence bridge.
        
        Args:
            verbose: Enable verbose logging
        """
        self.verbose = verbose
        self.call_history: list = []
        self.module_cache: Dict[str, Any] = {}
        
    def _log(self, message: str):
        """Log message if verbose mode enabled."""
        if self.verbose:
            print(f"[CoherenceBridge] {message}")
    
    def _parse_module_spec(self, spec: str) -> tuple[str, str, str]:
        """
        Parse module specification string.
        
        Args:
            spec: Module spec in format "path/to/module.py::function_name"
                  or "module_name::function_name"
        
        Returns:
            tuple: (module_path, module_name, function_name)
        """
        if "::" not in spec:
            raise ValueError(f"Invalid module spec: {spec}. Expected format: 'module::function'")
        
        module_part, function_name = spec.split("::", 1)
        
        # Handle file path specifications
        if module_part.endswith(".py"):
            module_path = module_part
            # Convert path to module name
            module_name = module_part.replace("/", ".").replace("\\", ".").replace(".py", "")
        else:
            module_path = module_part
            module_name = module_part
        
        return module_path, module_name, function_name
    
    def _load_module(self, module_name: str, module_path: str) -> Any:
        """
        Load module dynamically.
        
        Args:
            module_name: Name of module to load
            module_path: Path to module file
            
        Returns:
            Loaded module object
        """
        # Check cache first
        if module_name in self.module_cache:
            self._log(f"Using cached module: {module_name}")
            return self.module_cache[module_name]
        
        # Try to import as regular module first
        try:
            module = importlib.import_module(module_name)
            self.module_cache[module_name] = module
            self._log(f"Loaded module: {module_name}")
            return module
        except ImportError:
            pass
        
        # Try to load from file path
        if module_path.endswith(".py"):
            full_path = REPO_ROOT / module_path
            if full_path.exists():
                spec = importlib.util.spec_from_file_location(module_name, full_path)
                if spec and spec.loader:
                    module = importlib.util.module_from_spec(spec)
                    sys.modules[module_name] = module
                    spec.loader.exec_module(module)
                    self.module_cache[module_name] = module
                    self._log(f"Loaded module from file: {full_path}")
                    return module
        
        raise ImportError(f"Could not load module: {module_name} (path: {module_path})")
    
    def _get_function(self, module: Any, function_name: str) -> Callable:
        """
        Get function from module.
        
        Args:
            module: Module object
            function_name: Name of function
            
        Returns:
            Callable function
        """
        if not hasattr(module, function_name):
            raise AttributeError(
                f"Module {module.__name__} has no function '{function_name}'"
            )
        
        func = getattr(module, function_name)
        if not callable(func):
            raise TypeError(
                f"'{function_name}' in module {module.__name__} is not callable"
            )
        
        return func
    
    def call_module(
        self,
        spec: str,
        *args,
        coherence_check: bool = True,
        **kwargs
    ) -> Any:
        """
        Call a function in another module using vibrational signature mapping.
        
        This is the main entry point for symbiotic coherence protocol ∞³.
        
        Args:
            spec: Module specification "module::function" or "path/to/module.py::function"
            *args: Positional arguments to pass to the function
            coherence_check: Whether to validate vibrational coherence (default: True)
            **kwargs: Keyword arguments to pass to the function
            
        Returns:
            Result from the called function
            
        Example:
            >>> bridge = CoherenceBridge()
            >>> result = bridge.call_module(
            ...     "noesis88/vector_55_temporal.py::validar_timestamp_vector_55",
            ...     timestamp
            ... )
        """
        # Parse specification
        module_path, module_name, function_name = self._parse_module_spec(spec)
        
        self._log(f"Calling: {spec}")
        self._log(f"  Module: {module_name}")
        self._log(f"  Function: {function_name}")
        
        # Create vibrational signature
        signature = VibrationalSignature(module_path, function_name)
        
        # Validate coherence if requested
        if coherence_check:
            if not signature.is_coherent():
                raise ValueError(
                    f"Vibrational signature not coherent: {spec}\n"
                    f"Harmonic: {signature.compute_harmonic():.4f} Hz\n"
                    f"Expected range: [{signature.QCAL_FREQUENCY * 0.5:.4f}, "
                    f"{signature.QCAL_FREQUENCY * 10.0:.4f}] Hz"
                )
            self._log(f"  Harmonic: {signature.compute_harmonic():.4f} Hz ✓")
        
        # Load module
        module = self._load_module(module_name, module_path)
        
        # Get function
        func = self._get_function(module, function_name)
        
        # Call function
        call_record = {
            "timestamp": datetime.now().isoformat(),
            "spec": spec,
            "harmonic": signature.compute_harmonic(),
            "args_count": len(args),
            "kwargs_keys": list(kwargs.keys())
        }
        
        try:
            result = func(*args, **kwargs)
            call_record["status"] = "success"
            self._log(f"  Result: {type(result).__name__} ✓")
            return result
        except Exception as e:
            call_record["status"] = "error"
            call_record["error"] = str(e)
            self._log(f"  Error: {e} ✗")
            raise
        finally:
            self.call_history.append(call_record)
    
    def get_call_history(self) -> list:
        """
        Get history of all module calls.
        
        Returns:
            list: Call history records
        """
        return self.call_history
    
    def save_call_history(self, filepath: str = "data/coherence_bridge_history.json"):
        """
        Save call history to file.
        
        Args:
            filepath: Path to save history file
        """
        output_path = REPO_ROOT / filepath
        output_path.parent.mkdir(parents=True, exist_ok=True)
        
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(self.call_history, f, indent=2, ensure_ascii=False)
        
        self._log(f"Call history saved to: {output_path}")


# Global bridge instance for convenience
_global_bridge: Optional[CoherenceBridge] = None


def call_module(spec: str, *args, **kwargs) -> Any:
    """
    Convenience function for calling modules through coherence bridge.
    
    This uses a global bridge instance for simplified usage.
    
    Args:
        spec: Module specification "module::function"
        *args: Positional arguments
        **kwargs: Keyword arguments
        
    Returns:
        Result from called function
        
    Example:
        >>> from coherence_bridge import call_module
        >>> Ψ = call_module(
        ...     "noesis88/vector_55_temporal.py::validar_timestamp_vector_55",
        ...     timestamp
        ... )
    """
    global _global_bridge
    
    if _global_bridge is None:
        _global_bridge = CoherenceBridge(verbose=kwargs.pop('verbose', False))
    
    return _global_bridge.call_module(spec, *args, **kwargs)


if __name__ == "__main__":
    """Demo of coherence bridge functionality."""
    
    print("=" * 70)
    print("QCAL ∞³ COHERENCE BRIDGE - Vibrational Signature Mapping")
    print("=" * 70)
    print()
    
    # Create bridge
    bridge = CoherenceBridge(verbose=True)
    
    print(f"Fundamental frequency: {VibrationalSignature.QCAL_FREQUENCY} Hz")
    print(f"Coherence constant: {VibrationalSignature.QCAL_COHERENCE}")
    print()
    
    # Example signatures
    examples = [
        "noesis88/vector_55_temporal.py::validar_timestamp_vector_55",
        "utils/noesis_sync.py::compute_spectral_sync",
        "riemann_spectral_5steps.py::Step6_RealignPhase"
    ]
    
    print("Example Vibrational Signatures:")
    print("-" * 70)
    for spec in examples:
        try:
            path, name, func = bridge._parse_module_spec(spec)
            sig = VibrationalSignature(path, func)
            harmonic = sig.compute_harmonic()
            coherent = sig.is_coherent()
            status = "✓ COHERENT" if coherent else "✗ INCOHERENT"
            print(f"  {func}")
            print(f"    Harmonic: {harmonic:.4f} Hz")
            print(f"    Status: {status}")
            print()
        except Exception as e:
            print(f"  Error: {e}")
    
    print("=" * 70)
    print("♾️  QCAL Node evolution complete – coherence bridge ready.")
    print("=" * 70)
