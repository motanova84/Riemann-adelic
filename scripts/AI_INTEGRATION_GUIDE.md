# AI Integration Guide for Phoenix Solver

## Overview

This guide explains how to integrate AI services (Noesis, Sabio, GPT-4, Claude) with the Phoenix Solver for automated proof generation.

## Architecture

```
Phoenix Solver → AI Service → Lean Compiler → Validation
     ↓              ↓             ↓              ↓
  Context      Generate       Type-check     Coherence
  Prompt        Proof         Proof          Check
```

## Integration Options

### Option 1: GitHub Copilot / Noesis Integration

#### Prerequisites
- GitHub Copilot Workspace access
- Noesis API credentials
- Repository access permissions

#### Implementation

Add this method to `scripts/phoenix_solver.py`:

```python
async def generate_proof_with_noesis(self, prompt: str) -> Optional[str]:
    """Generate proof using Noesis API.
    
    Args:
        prompt: Quantum engineering prompt
        
    Returns:
        Generated Lean proof code or None
    """
    import aiohttp
    
    async with aiohttp.ClientSession() as session:
        async with session.post(
            'https://api.github.com/copilot/noesis/v1/generate',
            headers={
                'Authorization': f'Bearer {NOESIS_API_KEY}',
                'Content-Type': 'application/json'
            },
            json={
                'prompt': prompt,
                'model': 'noesis-lean4',
                'max_tokens': 2000,
                'temperature': 0.2  # Low temp for rigorous proofs
            }
        ) as response:
            if response.status == 200:
                data = await response.json()
                return data.get('proof')
            else:
                print(f"Noesis API error: {response.status}")
                return None
```

### Option 2: OpenAI GPT-4 Integration

#### Prerequisites
- OpenAI API key
- GPT-4 API access

#### Implementation

```python
def generate_proof_with_gpt4(self, prompt: str) -> Optional[str]:
    """Generate proof using GPT-4.
    
    Args:
        prompt: Quantum engineering prompt
        
    Returns:
        Generated Lean proof code or None
    """
    from openai import OpenAI
    
    client = OpenAI(api_key=os.getenv('OPENAI_API_KEY'))
    
    response = client.chat.completions.create(
        model="gpt-4-turbo-preview",
        messages=[
            {
                "role": "system",
                "content": "You are an expert in Lean4 theorem proving. "
                          "Generate rigorous, compilable Lean4 proofs."
            },
            {
                "role": "user",
                "content": prompt
            }
        ],
        temperature=0.2,
        max_tokens=2000
    )
    
    proof_code = response.choices[0].message.content
    
    # Extract Lean code from markdown if present
    import re
    lean_match = re.search(r'```lean\n(.*?)\n```', proof_code, re.DOTALL)
    if lean_match:
        return lean_match.group(1)
    
    return proof_code
```

### Option 3: Anthropic Claude Integration

#### Prerequisites
- Anthropic API key
- Claude API access

#### Implementation

```python
def generate_proof_with_claude(self, prompt: str) -> Optional[str]:
    """Generate proof using Claude.
    
    Args:
        prompt: Quantum engineering prompt
        
    Returns:
        Generated Lean proof code or None
    """
    import anthropic
    
    client = anthropic.Anthropic(api_key=os.getenv('ANTHROPIC_API_KEY'))
    
    message = client.messages.create(
        model="claude-3-opus-20240229",
        max_tokens=2000,
        temperature=0.2,
        system="You are an expert in Lean4 theorem proving and formal verification. "
               "Generate rigorous, compilable Lean4 proofs that maintain QCAL coherence.",
        messages=[
            {
                "role": "user",
                "content": prompt
            }
        ]
    )
    
    proof_code = message.content[0].text
    
    # Extract Lean code
    import re
    lean_match = re.search(r'```lean\n(.*?)\n```', proof_code, re.DOTALL)
    if lean_match:
        return lean_match.group(1)
    
    return proof_code
```

## Modified `resolve_sorry` Method

Update the `resolve_sorry` method in `PhoenixSolver` class:

```python
def resolve_sorry(self, sorry: SorryStatement, ai_service: str = 'gpt4') -> ResolutionResult:
    """Attempt to resolve a single sorry statement.
    
    Args:
        sorry: The sorry statement to resolve
        ai_service: AI service to use ('noesis', 'gpt4', 'claude')
        
    Returns:
        ResolutionResult with resolution status
    """
    print(f"\n{'='*70}")
    print(f"Resolving sorry in {sorry.file_path}:{sorry.line_number}")
    print(f"Lemma: {sorry.lemma_name}")
    print(f"{'='*70}")
    
    # Step 1: Build mathematical context
    print("\n1️⃣ Extracting mathematical context...")
    context = self.harvester.build_context_for_sorry(sorry)
    
    # Step 2: Generate quantum engineering prompt
    print("2️⃣ Generating quantum engineering prompt...")
    prompt = self.harvester.generate_quantum_prompt(sorry, context)
    
    # Save prompt for reference
    prompt_file = REPO_ROOT / "data" / "prompts" / f"{sorry.lemma_name}_prompt.md"
    prompt_file.parent.mkdir(parents=True, exist_ok=True)
    prompt_file.write_text(prompt)
    print(f"   Prompt saved to: {prompt_file}")
    
    # Step 3: Generate proof using AI
    print(f"\n3️⃣ Generating proof with {ai_service.upper()}...")
    
    proof_code = None
    try:
        if ai_service == 'noesis':
            proof_code = asyncio.run(self.generate_proof_with_noesis(prompt))
        elif ai_service == 'gpt4':
            proof_code = self.generate_proof_with_gpt4(prompt)
        elif ai_service == 'claude':
            proof_code = self.generate_proof_with_claude(prompt)
        else:
            print(f"   ⚠️  Unknown AI service: {ai_service}")
            return ResolutionResult(
                sorry=sorry,
                success=False,
                error_message=f"Unknown AI service: {ai_service}"
            )
    except Exception as e:
        print(f"   ❌ AI generation failed: {e}")
        return ResolutionResult(
            sorry=sorry,
            success=False,
            error_message=f"AI generation error: {str(e)}"
        )
    
    if not proof_code:
        print("   ❌ No proof generated")
        return ResolutionResult(
            sorry=sorry,
            success=False,
            error_message="AI service returned no proof"
        )
    
    # Step 4: Validate proof in sandbox
    print("\n4️⃣ Validating proof in Lean sandbox...")
    compilation_result = self.sandbox.validate_proof(proof_code, max_iterations=5)
    
    if compilation_result.success:
        print("   ✅ Proof compiles successfully!")
        
        # Step 5: Apply proof to actual file
        success = self._apply_proof_to_file(sorry, proof_code)
        
        return ResolutionResult(
            sorry=sorry,
            success=success,
            proof_code=proof_code,
            compilation_result=compilation_result,
            iterations=1
        )
    else:
        print("   ❌ Proof failed to compile")
        print(self.sandbox.extract_error_feedback(compilation_result))
        
        return ResolutionResult(
            sorry=sorry,
            success=False,
            proof_code=proof_code,
            compilation_result=compilation_result,
            iterations=1,
            error_message="Proof compilation failed"
        )

def _apply_proof_to_file(self, sorry: SorryStatement, proof_code: str) -> bool:
    """Apply generated proof to the actual Lean file.
    
    Args:
        sorry: SorryStatement to replace
        proof_code: Generated proof code
        
    Returns:
        True if successful, False otherwise
    """
    file_path = self.repo_root / sorry.file_path
    
    try:
        # Read file
        content = file_path.read_text()
        lines = content.split('\n')
        
        # Replace sorry on the specific line
        if sorry.line_number - 1 < len(lines):
            line = lines[sorry.line_number - 1]
            
            # Replace 'sorry' with generated proof
            # This is simplified - real implementation needs careful parsing
            updated_line = line.replace('sorry', proof_code.strip())
            lines[sorry.line_number - 1] = updated_line
            
            # Write back
            updated_content = '\n'.join(lines)
            file_path.write_text(updated_content)
            
            print(f"   ✅ Applied proof to {file_path}")
            return True
        else:
            print(f"   ❌ Line number out of range")
            return False
            
    except Exception as e:
        print(f"   ❌ Error applying proof: {e}")
        return False
```

## Environment Setup

### 1. Create `.env` file:

```bash
# .env
NOESIS_API_KEY=your_noesis_key_here
OPENAI_API_KEY=your_openai_key_here
ANTHROPIC_API_KEY=your_anthropic_key_here

# Default AI service (noesis, gpt4, claude)
PHOENIX_AI_SERVICE=gpt4
```

### 2. Install required packages:

```bash
pip install python-dotenv openai anthropic aiohttp
```

### 3. Load environment in phoenix_solver.py:

```python
from dotenv import load_dotenv
import os

load_dotenv()

NOESIS_API_KEY = os.getenv('NOESIS_API_KEY')
OPENAI_API_KEY = os.getenv('OPENAI_API_KEY')
ANTHROPIC_API_KEY = os.getenv('ANTHROPIC_API_KEY')
```

## Usage with AI Integration

```bash
# Using default AI service from .env
python scripts/phoenix_solver.py --max-sorrys 10

# Specify AI service
python scripts/phoenix_solver.py --ai-service gpt4 --max-sorrys 10

# Priority file with AI
python scripts/phoenix_solver.py \
    --priority-file RIGOROUS_UNIQUENESS_EXACT_LAW.lean \
    --ai-service claude \
    --batch-size 5
```

## Iterative Correction Loop

For proofs that don't compile on first try:

```python
def resolve_sorry_with_iteration(self, sorry: SorryStatement, 
                                 max_iterations: int = 5) -> ResolutionResult:
    """Resolve sorry with iterative correction.
    
    Args:
        sorry: SorryStatement to resolve
        max_iterations: Maximum correction attempts
        
    Returns:
        ResolutionResult
    """
    context = self.harvester.build_context_for_sorry(sorry)
    prompt = self.harvester.generate_quantum_prompt(sorry, context)
    
    for iteration in range(max_iterations):
        print(f"\n   Iteration {iteration + 1}/{max_iterations}")
        
        # Generate proof
        proof_code = self.generate_proof_with_ai(prompt)
        
        # Validate
        result = self.sandbox.validate_proof(proof_code)
        
        if result.success:
            return ResolutionResult(
                sorry=sorry,
                success=True,
                proof_code=proof_code,
                compilation_result=result,
                iterations=iteration + 1
            )
        
        # Extract errors and create correction prompt
        error_feedback = self.sandbox.extract_error_feedback(result)
        
        # Enhance prompt with error feedback
        prompt = f"{prompt}\n\n## Previous Attempt Failed\n\n{error_feedback}\n\nPlease generate a corrected proof."
    
    return ResolutionResult(
        sorry=sorry,
        success=False,
        error_message=f"Failed after {max_iterations} iterations"
    )
```

## Best Practices

### 1. Prompt Engineering

- Include full QCAL context (C, f₀, Ψ)
- Reference related Python implementations
- Provide related theorems from same file
- Specify available Mathlib tactics
- Include error messages from previous attempts

### 2. Rate Limiting

```python
import time

def generate_with_rate_limit(self, prompt, service='gpt4'):
    """Generate proof with rate limiting."""
    # Wait between requests
    time.sleep(2)
    
    return self.generate_proof_with_ai(prompt, service)
```

### 3. Cost Management

```python
# Track API costs
self.stats['api_calls'] = 0
self.stats['tokens_used'] = 0

def track_api_usage(self, response):
    """Track API usage for cost management."""
    self.stats['api_calls'] += 1
    if hasattr(response, 'usage'):
        self.stats['tokens_used'] += response.usage.total_tokens
```

### 4. Caching

```python
from functools import lru_cache

@lru_cache(maxsize=100)
def get_cached_proof(self, lemma_name: str, theorem_hash: str):
    """Cache generated proofs to avoid duplicate API calls."""
    cache_file = REPO_ROOT / "data" / "proof_cache" / f"{lemma_name}_{theorem_hash}.lean"
    if cache_file.exists():
        return cache_file.read_text()
    return None
```

## Testing

Test AI integration with a simple sorry:

```bash
# Create test file
echo 'theorem simple_test : 1 + 1 = 2 := by sorry' > test.lean

# Test generation
python scripts/phoenix_solver.py --test-proof test.lean
```

## Monitoring

Add logging for AI interactions:

```python
import logging

logging.basicConfig(
    filename='data/logs/phoenix_solver.log',
    level=logging.INFO,
    format='%(asctime)s - %(levelname)s - %(message)s'
)

# Log each resolution
logging.info(f"Resolving {sorry.lemma_name} with {ai_service}")
logging.info(f"Prompt length: {len(prompt)} chars")
logging.info(f"Proof generated: {len(proof_code)} chars")
logging.info(f"Compilation: {'✅ Success' if success else '❌ Failed'}")
```

## Safety Checks

Before deploying with AI:

1. ✅ Test on dry-run mode
2. ✅ Validate with small batch size (1-5)
3. ✅ Monitor coherence after each batch
4. ✅ Keep backup of original files
5. ✅ Use git for version control
6. ✅ Review AI-generated proofs manually

---

**Status**: Ready for Integration  
**Recommended**: Start with GPT-4 or Claude (more reliable than auto-generated)  
**Next Step**: Set up API credentials and test with 1-2 simple sorrys
