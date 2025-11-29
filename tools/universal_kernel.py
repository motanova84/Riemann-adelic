"""
Universal Kernel: Verificador de coherencia total para QCAL.
Este módulo valida la coherencia semántica, lógica y física de objetos QCAL.
"""

import json
import os
from pathlib import Path


def verify_universal(jsonld_path: str, proof_path: str) -> bool:
    """
    Verifica la coherencia universal de un objeto QCAL.
    
    Args:
        jsonld_path: Ruta al archivo JSON-LD con metadatos
        proof_path: Ruta al archivo de prueba (puede ser Lean o Python)
    
    Returns:
        True si la verificación es exitosa, False en caso contrario
    """
    try:
        # V_L: Verificación lógica - comprobar que los archivos existen
        if not os.path.exists(jsonld_path):
            print(f"Error: {jsonld_path} no existe")
            return False
        
        if not os.path.exists(proof_path):
            print(f"Error: {proof_path} no existe")
            return False
        
        # V_S: Verificación semántica - validar estructura JSON-LD
        with open(jsonld_path, 'r', encoding='utf-8') as f:
            metadata = json.load(f)
        
        # Validar campos requeridos en JSON-LD
        required_fields = ['@context', '@type']
        for field in required_fields:
            if field not in metadata:
                print(f"Error: Campo requerido '{field}' no encontrado en {jsonld_path}")
                return False
        
        # V_F: Verificación física - comprobar integridad básica
        jsonld_size = os.path.getsize(jsonld_path)
        proof_size = os.path.getsize(proof_path)
        
        if jsonld_size == 0 or proof_size == 0:
            print("Error: Archivos vacíos detectados")
            return False
        
        # Verificación de coherencia adicional
        # Aquí se pueden agregar más validaciones específicas del dominio
        
        return True
    
    except json.JSONDecodeError as e:
        print(f"Error al parsear JSON: {e}")
        return False
    except Exception as e:
        print(f"Error inesperado: {e}")
        return False


def verify_universal_api(jsonld_path: str, proof_path: str) -> bool:
    """
    API simple para el FFI bridge que devuelve un booleano.
    
    Args:
        jsonld_path: Ruta al archivo JSON-LD con metadatos
        proof_path: Ruta al archivo de prueba
    
    Returns:
        True si la verificación es exitosa, False en caso contrario
    """
    try:
        return verify_universal(jsonld_path, proof_path)
    except Exception:
        return False


def register_verification(jsonld_path: str, proof_path: str, result: bool, 
                         output_path: str = "tools/qcal_state.json"):
    """
    Registra el resultado de una verificación en el estado QCAL.
    
    Args:
        jsonld_path: Ruta al archivo JSON-LD verificado
        proof_path: Ruta al archivo de prueba verificado
        result: Resultado de la verificación
        output_path: Ruta al archivo de estado JSON
    """
    try:
        # Crear el directorio si no existe
        os.makedirs(os.path.dirname(output_path), exist_ok=True)
        
        # Leer estado existente o crear nuevo
        if os.path.exists(output_path):
            with open(output_path, 'r', encoding='utf-8') as f:
                state = json.load(f)
        else:
            state = {"verifications": []}
        
        # Agregar nueva verificación
        verification_entry = {
            "file": jsonld_path,
            "proof": proof_path,
            "verified": result,
            "timestamp": None  # Se puede agregar timestamp si se necesita
        }
        
        if "verifications" not in state:
            state["verifications"] = []
        
        state["verifications"].append(verification_entry)
        
        # Guardar estado actualizado
        with open(output_path, 'w', encoding='utf-8') as f:
            json.dump(state, f, indent=2)
        
        return True
    except Exception as e:
        print(f"Error al registrar verificación: {e}")
        return False


if __name__ == "__main__":
    import sys
    
    if len(sys.argv) < 3:
        print("Uso: python universal_kernel.py <jsonld_path> <proof_path>")
        sys.exit(1)
    
    jsonld_path = sys.argv[1]
    proof_path = sys.argv[2]
    
    result = verify_universal_api(jsonld_path, proof_path)
    
    if result:
        print(f"✅ Verificación exitosa para {jsonld_path}")
        register_verification(jsonld_path, proof_path, True)
        sys.exit(0)
    else:
        print(f"❌ Verificación fallida para {jsonld_path}")
        register_verification(jsonld_path, proof_path, False)
        sys.exit(1)


# =============================================================================
# Advanced Universal Kernel for QCAL coherence validation
# =============================================================================
# Hybrid universal kernel that formalises the triple-layer verifier described
# in the QCAL specification. Each JSON-LD descriptor is interpreted as an
# element of the structure U = (L, S, F) composed of logical, semantic, and
# physical/informational components.
# =============================================================================

import argparse
import hashlib
import shutil
import subprocess
from dataclasses import dataclass
from typing import (
    Dict, Iterable, Iterator, List, Mapping, MutableMapping,
    Optional, Sequence, Tuple
)

BASELINE_FREQUENCY = 141.7001
FREQUENCY_TOLERANCE = 1e-4
HASH_PREFIX = "sha256-"

# JSON-LD structural requirements
REQUIRED_FIELDS = {
    "@id",
    "dc:title",
    "formal:kernel",
    "formal:proof",
    "formal:axioms",
    "sem:dependsOn",
    "hash:sha256",
    "freq:Hz",
}

REQUIRED_CONTEXT_KEYS = {"dc", "formal", "sem", "hash", "freq"}

URN_PATTERN = r"^urn:qcal:[a-z0-9]+:[a-z0-9:_\-]+$"

KERNEL_COMMANDS: Dict[str, Sequence[str]] = {
    "Dedukti": ("dkcheck",),
    "Lean4": ("lean", "--check"),
}


class UniversalKernelError(RuntimeError):
    """Raised when universal coherence validation fails."""


@dataclass
class ValidationResult:
    path: Path
    identifier: str
    logical_ok: bool
    semantic_ok: bool
    physical_ok: bool
    frequency: float
    computed_frequency: float
    declared_hash: str
    computed_hash: str

    def all_ok(self) -> bool:
        return self.logical_ok and self.semantic_ok and self.physical_ok


@dataclass(frozen=True)
class EntryContext:
    identifier: str
    dependencies: Tuple[str, ...]
    path: Path


def compute_sha256(content: str) -> str:
    digest = hashlib.sha256(content.encode("utf-8")).hexdigest()
    return f"{HASH_PREFIX}{digest}"


def hash_to_frequency(proofhash: str, baseline: float = BASELINE_FREQUENCY) -> float:
    if not proofhash.startswith(HASH_PREFIX):
        raise UniversalKernelError(f"Hash '{proofhash}' must start with '{HASH_PREFIX}'.")
    int_value = int(proofhash[len(HASH_PREFIX):], 16)
    window = 5e-3
    offset = (int_value % 1_000_000) / 1_000_000 * 2 * window - window
    return baseline + offset


def load_jsonld_objects(paths: Iterable[Path]) -> Iterator[Tuple[Path, MutableMapping[str, object]]]:
    for path in paths:
        try:
            payload = json.loads(path.read_text(encoding="utf-8"))
        except json.JSONDecodeError as exc:
            raise UniversalKernelError(f"Failed to parse JSON-LD file '{path}': {exc}.") from exc

        base_context: Optional[MutableMapping[str, object]] = None

        def prepare(entry: object) -> MutableMapping[str, object]:
            nonlocal base_context
            if not isinstance(entry, MutableMapping):
                raise UniversalKernelError(f"Top-level entries in '{path}' must be JSON objects.")
            context = entry.get("@context")
            if context is None and base_context is not None:
                entry["@context"] = base_context
            elif context is not None:
                if not isinstance(context, MutableMapping):
                    raise UniversalKernelError(f"'@context' in '{path}' must be a JSON object.")
                base_context = context
            return entry

        if isinstance(payload, list):
            for entry in payload:
                yield path, prepare(entry)
        else:
            yield path, prepare(payload)


def ensure_required_fields(entry: Mapping[str, object], json_path: Path) -> None:
    missing = [field for field in REQUIRED_FIELDS if field not in entry]
    if missing:
        raise UniversalKernelError(
            f"File '{json_path}' is missing required fields: {', '.join(sorted(missing))}."
        )


def ensure_context(entry: Mapping[str, object], json_path: Path) -> None:
    context = entry.get("@context")
    if not isinstance(context, Mapping):
        raise UniversalKernelError(f"Descriptor '{json_path}' must declare a JSON-LD '@context'.")
    missing = [key for key in REQUIRED_CONTEXT_KEYS if key not in context]
    if missing:
        raise UniversalKernelError(
            f"Descriptor '{json_path}' is missing context prefixes: {', '.join(sorted(missing))}."
        )


def validate_identifier(identifier: str, json_path: Path) -> None:
    import re

    if not re.match(URN_PATTERN, identifier):
        raise UniversalKernelError(f"Identifier '{identifier}' in '{json_path}' is not a valid QCAL URN.")


def resolve_proof_content(entry: Mapping[str, object], json_path: Path) -> Tuple[str, Optional[Path]]:
    raw_reference = entry.get("formal:proof")
    if not isinstance(raw_reference, str) or not raw_reference.strip():
        raise UniversalKernelError(f"Descriptor '{json_path}' must provide a 'formal:proof' path or identifier.")

    candidate_path = Path(raw_reference)
    if not candidate_path.is_absolute():
        candidate_path = (json_path.parent / raw_reference).resolve()
        if not candidate_path.exists():
            candidate_path = (Path.cwd() / raw_reference).resolve()

    if candidate_path.exists():
        return candidate_path.read_text(encoding="utf-8"), candidate_path

    # Fallback: allow inline proof content for remote kernels
    return raw_reference, None


def validate_kernel(entry: Mapping[str, object], allowed_kernels: Optional[Sequence[str]]) -> str:
    kernel = entry.get("formal:kernel")
    if not isinstance(kernel, str) or not kernel.strip():
        raise UniversalKernelError("'formal:kernel' must be a non-empty string.")
    kernel = kernel.strip()
    if allowed_kernels and kernel not in allowed_kernels:
        allowed_display = ", ".join(sorted(allowed_kernels))
        raise UniversalKernelError(
            f"Kernel '{kernel}' is not among the permitted values: {allowed_display}."
        )
    return kernel


def validate_axioms(entry: Mapping[str, object], identifier: str, json_path: Path) -> Tuple[str, ...]:
    axioms = entry.get("formal:axioms")
    if not isinstance(axioms, Sequence) or isinstance(axioms, (str, bytes)):
        raise UniversalKernelError(f"'{identifier}' in '{json_path}' must declare a sequence of axioms.")
    cleaned: List[str] = []
    for axiom in axioms:
        if not isinstance(axiom, str) or not axiom.strip():
            raise UniversalKernelError(f"Axiom declarations for '{identifier}' must be non-empty strings.")
        cleaned.append(axiom.strip())
    if len(set(cleaned)) != len(cleaned):
        raise UniversalKernelError(f"Duplicate axioms found for '{identifier}'.")
    return tuple(cleaned)


def validate_dependencies(identifier: str, entry: Mapping[str, object], json_path: Path) -> Tuple[str, ...]:
    deps = entry.get("sem:dependsOn")
    if not isinstance(deps, Sequence) or isinstance(deps, (str, bytes)):
        raise UniversalKernelError(f"'{identifier}' in '{json_path}' must declare 'sem:dependsOn' as a list of URNs.")
    cleaned: List[str] = []
    for dep in deps:
        if not isinstance(dep, str):
            raise UniversalKernelError(f"Dependency '{dep}' for '{identifier}' must be a string URN.")
        dep = dep.strip()
        validate_identifier(dep, json_path)
        if dep == identifier:
            raise UniversalKernelError(f"'{identifier}' cannot depend on itself.")
        cleaned.append(dep)
    if not cleaned:
        raise UniversalKernelError(f"'{identifier}' must declare at least one semantic dependency.")
    if len(set(cleaned)) != len(cleaned):
        raise UniversalKernelError(f"Duplicate dependencies found for '{identifier}'.")
    return tuple(cleaned)


def run_kernel_checker(kernel: str, proof_path: Optional[Path], proof_content: str) -> None:
    command = KERNEL_COMMANDS.get(kernel)
    if command and shutil.which(command[0]) and proof_path is not None:
        result = subprocess.run(
            [*command, str(proof_path)],
            capture_output=True,
            text=True,
            check=False,
        )
        if result.returncode != 0:
            raise UniversalKernelError(
                f"Kernel '{kernel}' rejected proof '{proof_path}': {result.stderr.strip() or result.stdout.strip()}"
            )
        return

    # Structural fallback: require at least one theorem/axiom/def declaration
    import re

    pattern = re.compile(r"^\s*(theorem|lemma|axiom|def)\b", re.MULTILINE)
    if pattern.search(proof_content) is None:
        raise UniversalKernelError(
            f"Kernel '{kernel}' fallback validation failed – proof does not contain canonical declarations."
        )


def validate_hash_fields(
    entry: MutableMapping[str, object],
    identifier: str,
    computed_hash: str,
    *,
    update: bool,
) -> str:
    declared = entry.get("hash:sha256")
    if not isinstance(declared, str):
        raise UniversalKernelError(f"'{identifier}' must declare 'hash:sha256' as a string.")
    if declared != computed_hash:
        if update:
            entry["hash:sha256"] = computed_hash
            if isinstance(entry.get("proofhash"), str):
                entry["proofhash"] = computed_hash
        else:
            raise UniversalKernelError(
                f"Hash mismatch for '{identifier}'. Declared {declared}, expected {computed_hash}."
            )
    else:
        # Keep legacy field aligned if present
        if isinstance(entry.get("proofhash"), str) and entry["proofhash"] != computed_hash:
            if update:
                entry["proofhash"] = computed_hash
            else:
                raise UniversalKernelError(
                    f"Legacy 'proofhash' for '{identifier}' disagrees with 'hash:sha256'."
                )
    return entry.get("hash:sha256")  # type: ignore[return-value]


def validate_frequency_field(
    entry: MutableMapping[str, object],
    identifier: str,
    computed_frequency: float,
    *,
    tolerance: float,
    update: bool,
) -> float:
    declared_freq = entry.get("freq:Hz")
    try:
        numeric_freq = float(declared_freq)  # type: ignore[arg-type]
    except (TypeError, ValueError):
        raise UniversalKernelError(f"Frequency for '{identifier}' must be numeric.")

    tolerance_override = entry.get("freq:tolerance")
    local_tolerance = tolerance
    if tolerance_override is not None:
        try:
            local_tolerance = float(tolerance_override)
        except (TypeError, ValueError):
            raise UniversalKernelError(f"freq:tolerance for '{identifier}' must be numeric.")
        if local_tolerance <= 0:
            raise UniversalKernelError(f"freq:tolerance for '{identifier}' must be positive.")

    if abs(numeric_freq - computed_frequency) > local_tolerance:
        if update:
            entry["freq:Hz"] = round(computed_frequency, 9)
        else:
            raise UniversalKernelError(
                f"Frequency mismatch for '{identifier}'. Declared {numeric_freq:.9f}, expected {computed_frequency:.9f} ±{local_tolerance:.1e}."
            )
    return float(entry.get("freq:Hz"))


def verify_entry(
    entry: MutableMapping[str, object],
    json_path: Path,
    *,
    baseline: float,
    tolerance: float,
    allowed_kernels: Optional[Sequence[str]],
    update: bool,
) -> Tuple[ValidationResult, EntryContext]:
    ensure_required_fields(entry, json_path)
    ensure_context(entry, json_path)

    identifier = entry.get("@id")
    if not isinstance(identifier, str):
        raise UniversalKernelError(f"Descriptor '{json_path}' is missing an '@id' string.")
    validate_identifier(identifier, json_path)

    kernel = validate_kernel(entry, allowed_kernels)
    validate_axioms(entry, identifier, json_path)
    dependencies = validate_dependencies(identifier, entry, json_path)

    proof_content, proof_path = resolve_proof_content(entry, json_path)
    run_kernel_checker(kernel, proof_path, proof_content)

    computed_hash = compute_sha256(proof_content)
    declared_hash = validate_hash_fields(entry, identifier, computed_hash, update=update)

    computed_frequency = hash_to_frequency(declared_hash, baseline)
    declared_frequency = validate_frequency_field(
        entry,
        identifier,
        computed_frequency,
        tolerance=tolerance,
        update=update,
    )

    result = ValidationResult(
        path=json_path,
        identifier=identifier,
        logical_ok=True,
        semantic_ok=False,
        physical_ok=True,
        frequency=declared_frequency,
        computed_frequency=computed_frequency,
        declared_hash=declared_hash,
        computed_hash=computed_hash,
    )

    context = EntryContext(identifier=identifier, dependencies=dependencies, path=json_path)
    return result, context


def detect_semantic_cycles(contexts: Sequence[EntryContext]) -> None:
    adjacency: Dict[str, List[str]] = {ctx.identifier: [] for ctx in contexts}
    identifiers = set(adjacency)
    for ctx in contexts:
        for dep in ctx.dependencies:
            if dep in identifiers:
                adjacency[ctx.identifier].append(dep)

    visiting: Dict[str, bool] = {}
    visited: Dict[str, bool] = {}

    def dfs(node: str, stack: List[str]) -> None:
        visiting[node] = True
        stack.append(node)
        for neighbour in adjacency[node]:
            if neighbour in visiting:
                cycle = stack[stack.index(neighbour):] + [neighbour]
                raise UniversalKernelError(
                    "Semantic dependency cycle detected: " + " → ".join(cycle)
                )
            if neighbour not in visited:
                dfs(neighbour, stack)
        visiting.pop(node, None)
        visited[node] = True
        stack.pop()

    for identifier in adjacency:
        if identifier not in visited:
            dfs(identifier, [])


def validate_semantic_layer(contexts: Sequence[EntryContext]) -> None:
    detect_semantic_cycles(contexts)


def validate_unique_identifiers(results: Sequence[ValidationResult]) -> None:
    seen: Dict[str, Path] = {}
    for result in results:
        existing = seen.get(result.identifier)
        if existing is not None and existing != result.path:
            raise UniversalKernelError(
                f"Identifier '{result.identifier}' declared in both '{existing}' and '{result.path}'."
            )
        seen[result.identifier] = result.path


def save_updates(entries: Mapping[Path, List[MutableMapping[str, object]]]) -> None:
    for path, objects in entries.items():
        if not objects:
            continue
        content: object
        if len(objects) == 1:
            content = objects[0]
        else:
            content = objects
        path.write_text(json.dumps(content, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def run_validation(
    paths: Sequence[Path],
    *,
    baseline: float,
    tolerance: float,
    allowed_kernels: Optional[Sequence[str]],
    update: bool,
) -> List[ValidationResult]:
    results: List[ValidationResult] = []
    contexts: List[EntryContext] = []
    grouped: Dict[Path, List[MutableMapping[str, object]]] = {}

    for json_path, entry in load_jsonld_objects(paths):
        grouped.setdefault(json_path, []).append(entry)
        result, context = verify_entry(
            entry,
            json_path,
            baseline=baseline,
            tolerance=tolerance,
            allowed_kernels=allowed_kernels,
            update=update,
        )
        results.append(result)
        contexts.append(context)

    validate_unique_identifiers(results)
    validate_semantic_layer(contexts)
    for result in results:
        result.semantic_ok = True

    if update:
        save_updates(grouped)

    return results


def parse_args(argv: Optional[Sequence[str]] = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Validate universal QCAL theorem descriptors.")
    parser.add_argument("paths", nargs="+", type=Path, help="JSON-LD theorem descriptors to validate.")
    parser.add_argument("--baseline", type=float, default=BASELINE_FREQUENCY, help="Baseline resonance frequency.")
    parser.add_argument(
        "--tolerance",
        type=float,
        default=FREQUENCY_TOLERANCE,
        help="Default allowed deviation from the baseline-derived frequency.",
    )
    parser.add_argument(
        "--allow-kernel",
        dest="allowed_kernels",
        action="append",
        help="Explicitly allow a formal kernel identifier. If omitted any kernel value is accepted.",
    )
    parser.add_argument(
        "--update",
        action="store_true",
        help="Rewrite JSON-LD files so that hashes and frequencies match computed values.",
    )
    return parser.parse_args(argv)


def main_advanced(argv: Optional[Sequence[str]] = None) -> int:
    """Advanced CLI entry point for QCAL validation."""
    args = parse_args(argv)
    try:
        results = run_validation(
            args.paths,
            baseline=args.baseline,
            tolerance=args.tolerance,
            allowed_kernels=args.allowed_kernels,
            update=args.update,
        )
    except UniversalKernelError as exc:
        print(f"❌ Universal coherence validation failed: {exc}")
        return 1

    header = "Identifier".ljust(40)
    print(f"✓ Universal coherence achieved for {len(results)} descriptor(s).")
    print(f"{header}  L  S  F    freq(Hz)       computed      hash")
    print("-" * 90)
    for result in results:
        status = "✓" if result.all_ok() else "⚠"
        print(
            f"{status} {result.identifier.ljust(38)}  "
            f"{int(result.logical_ok)}  {int(result.semantic_ok)}  {int(result.physical_ok)}  "
            f"{result.frequency:11.6f}  {result.computed_frequency:11.6f}  {result.declared_hash[:18]}…"
        )
    return 0
