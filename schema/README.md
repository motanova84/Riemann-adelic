# Metadata Schema Directory

This directory contains JSON-LD metadata schemas for the mathematical archive system.

## Purpose

The metadata schemas provide semantic annotations for mathematical objects (theorems, proofs, definitions, axioms) using standard vocabularies:

- **Dublin Core (dc)**: Basic metadata (title, creator, date, description)
- **Schema.org**: Structured data for discoverability
- **FOAF**: Person/author information
- **MSC 2010**: Mathematics Subject Classification
- **Custom namespace**: Project-specific fields (checksum, dependencies, formalization)

## Files

### `metadata_example.jsonld`

A comprehensive example showing all required and optional fields for a theorem metadata entry.

**Required fields:**
- `@context`: JSON-LD context with vocabularies
- `@id`: Unique identifier (URN)
- `@type`: Type of mathematical object (theorem, proof, definition, axiom)
- `dc:title`: Human-readable title
- `dc:creator`: Author information
- `dc:date`: Creation/formalization date

**Recommended fields:**
- `checksum`: SHA-256 hash for integrity verification
- `dependencies`: List of required theorems/axioms
- `formalizedIn`: Proof system information
- `verifiedBy`: Verification kernel information
- `dc:subject`: Keywords and topics
- `msc:classification`: MSC 2010 codes

## Usage

### Validating Metadata

Use the validation script to check metadata files:

```bash
python tools/verify_metadata.py schema/metadata_example.jsonld
```

### Creating New Metadata

1. Copy the example file:
   ```bash
   cp schema/metadata_example.jsonld schema/my_theorem.jsonld
   ```

2. Edit the fields with your theorem's information

3. Generate a checksum for your artifact:
   ```bash
   sha256sum formalization/lean/MyTheorem.lean
   ```

4. Validate the metadata:
   ```bash
   python tools/verify_metadata.py schema/my_theorem.jsonld
   ```

## Best Practices

1. **Unique IDs**: Use consistent URN format: `urn:jmmotaburr:riemann-adelic:{category}:{name}`
2. **Checksums**: Always include SHA-256 checksums for verifiability
3. **Dependencies**: List all formal dependencies with proper @id references
4. **MSC Codes**: Include appropriate Mathematics Subject Classification codes
5. **Versioning**: Include version information in the metadata
6. **License**: Specify license for reuse (MIT recommended for code, CC BY 4.0 for content)

## Integration with CI/CD

The CI workflow automatically validates all metadata files on push/PR:

```yaml
- name: Validate metadata
  run: |
    python tools/verify_metadata.py schema/*.jsonld
```

## Further Reading

- [JSON-LD Specification](https://www.w3.org/TR/json-ld/)
- [Dublin Core Metadata Initiative](https://www.dublincore.org/)
- [Schema.org](https://schema.org/)
- [MSC 2010 Classification](https://msc2010.org/)
