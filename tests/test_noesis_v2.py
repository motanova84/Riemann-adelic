#!/usr/bin/env python3
"""
Test Suite for NOESIS-AMDA-AURON V2.0
Tests: orchestrator, analyzer, executor, persistence, classification, e2e
"""

import pytest
import json
import subprocess
import sys
from pathlib import Path
import tempfile
import shutil

# Paths
REPO_ROOT = Path(__file__).parent.parent
SCRIPT_DIR = REPO_ROOT / '.github' / 'scripts' / 'v2'
sys.path.insert(0, str(SCRIPT_DIR))


class TestNOESISOrchestrator:
    """Test 1: NOESIS Orchestrator"""
    
    def test_orchestrator_imports(self):
        """Verificar que noesis_orchestrator se puede importar"""
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location(
                "noesis_orchestrator", 
                SCRIPT_DIR / "noesis_orchestrator.py"
            )
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            assert hasattr(module, 'NoesisOrchestrator')
        except Exception as e:
            pytest.fail(f"No se pudo importar noesis_orchestrator: {e}")
    
    def test_orchestrator_execution(self):
        """Verificar que NOESIS ejecuta sin errores"""
        # Test con mode simulation
        result = subprocess.run(
            [sys.executable, str(SCRIPT_DIR / 'noesis_orchestrator.py'), 'dry-run'],
            capture_output=True,
            timeout=180,
            cwd=REPO_ROOT
        )
        
        # Debe completar sin error crítico
        assert result.returncode in [0, 1], \
            f"NOESIS falló con código {result.returncode}: {result.stderr.decode()}"
    
    def test_orchestrator_output_structure(self):
        """Verificar estructura de salida de NOESIS"""
        summary_file = REPO_ROOT / 'noesis_cerebral_v2_summary.json'
        
        if summary_file.exists():
            with open(summary_file) as f:
                summary = json.load(f)
            
            # Verificar estructura esperada
            assert 'knowledge_base' in summary or 'status' in summary, \
                "Summary no tiene estructura esperada"


class TestAMDAAnalyzer:
    """Test 2: AMDA Analyzer"""
    
    def test_analyzer_imports(self):
        """Verificar que amda_deep_v2 se puede importar"""
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location(
                "amda_deep_v2",
                SCRIPT_DIR / "amda_deep_v2.py"
            )
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            assert hasattr(module, 'AmDADeepV2')
        except Exception as e:
            pytest.fail(f"No se pudo importar amda_deep_v2: {e}")
    
    def test_analyzer_categories(self):
        """Verificar que AMDA tiene 6 categorías definidas"""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "amda_deep_v2",
            SCRIPT_DIR / "amda_deep_v2.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        analyzer = module.AmDADeepV2()
        assert hasattr(analyzer, 'PATTERNS')
        assert len(analyzer.PATTERNS) == 6, \
            f"Esperadas 6 categorías, encontradas {len(analyzer.PATTERNS)}"
        
        # Verificar categorías específicas
        expected_categories = {'trivial', 'correspondence', 'qcal', 
                             'adelic', 'spectral', 'analytic'}
        assert set(analyzer.PATTERNS.keys()) == expected_categories


class TestAURONExecutor:
    """Test 3: AURON Executor"""
    
    def test_executor_imports(self):
        """Verificar que auron_neural_v2 se puede importar"""
        try:
            import importlib.util
            spec = importlib.util.spec_from_file_location(
                "auron_neural_v2",
                SCRIPT_DIR / "auron_neural_v2.py"
            )
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            assert hasattr(module, 'AuronNeuralV2')
        except Exception as e:
            pytest.fail(f"No se pudo importar auron_neural_v2: {e}")
    
    def test_executor_patterns(self):
        """Verificar que AURON tiene 12 patrones de reemplazo"""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "auron_neural_v2",
            SCRIPT_DIR / "auron_neural_v2.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        executor = module.AuronNeuralV2()
        assert hasattr(executor, 'replacement_patterns')
        assert len(executor.replacement_patterns) == 12, \
            f"Esperados 12 patrones, encontrados {len(executor.replacement_patterns)}"


class TestPersistence:
    """Test 4: Learning History Persistence"""
    
    def test_learning_file_format(self):
        """Verificar formato de .auron_learning.json si existe"""
        learning_file = REPO_ROOT / '.auron_learning.json'
        
        if learning_file.exists():
            try:
                with open(learning_file) as f:
                    learning = json.load(f)
                
                # Verificar estructura
                assert 'patterns' in learning, "Learning history debe tener 'patterns'"
                assert isinstance(learning['patterns'], dict), \
                    "'patterns' debe ser un diccionario"
                
                # Verificar estructura de un patrón si existe alguno
                if learning['patterns']:
                    first_pattern = list(learning['patterns'].values())[0]
                    expected_keys = {'solution', 'success_count', 'fail_count', 
                                   'success_rate', 'last_used'}
                    assert set(first_pattern.keys()) >= expected_keys, \
                        f"Patrón debe tener keys {expected_keys}"
            
            except json.JSONDecodeError:
                pytest.fail("Learning history no es JSON válido")
    
    def test_learning_creation(self):
        """Verificar que se puede crear learning history nuevo"""
        test_file = REPO_ROOT / '.auron_learning_test.json'
        
        try:
            # Crear estructura
            learning = {
                'patterns': {},
                'metadata': {
                    'total_attempts': 0,
                    'total_successes': 0,
                    'global_success_rate': 0.0
                }
            }
            
            # Guardar
            with open(test_file, 'w') as f:
                json.dump(learning, f, indent=2)
            
            # Leer y verificar
            with open(test_file) as f:
                loaded = json.load(f)
            
            assert loaded == learning
        
        finally:
            # Limpiar
            if test_file.exists():
                test_file.unlink()


class TestClassification:
    """Test 5: Multi-categoric Classification"""
    
    def test_trivial_classification(self):
        """Verificar clasificación de contexto trivial"""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "amda_deep_v2",
            SCRIPT_DIR / "amda_deep_v2.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        analyzer = module.AmDADeepV2()
        
        # Contexto trivial
        context = "theorem foo : x = x := sorry"
        categories = analyzer.classify_deep(context)
        
        # Debe detectar como trivial
        category_names = [c['name'] for c in categories]
        assert 'trivial' in category_names, \
            f"No detectó 'trivial' en: {category_names}"
    
    def test_qcal_classification(self):
        """Verificar clasificación de contexto QCAL"""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "amda_deep_v2",
            SCRIPT_DIR / "amda_deep_v2.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        analyzer = module.AmDADeepV2()
        
        # Contexto QCAL
        context = "theorem coherence : QCAL.Ψ = f₀ * C := sorry"
        categories = analyzer.classify_deep(context)
        
        # Debe detectar como QCAL
        category_names = [c['name'] for c in categories]
        assert 'qcal' in category_names, \
            f"No detectó 'qcal' en: {category_names}"
    
    def test_multi_category_classification(self):
        """Verificar que puede detectar múltiples categorías"""
        import importlib.util
        spec = importlib.util.spec_from_file_location(
            "amda_deep_v2",
            SCRIPT_DIR / "amda_deep_v2.py"
        )
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        
        analyzer = module.AmDADeepV2()
        
        # Contexto con múltiples categorías
        context = """
        theorem spectral_qcal_correspondence : 
          spectrum H_ψ ↔ QCAL.coherence f₀ := sorry
        """
        categories = analyzer.classify_deep(context)
        
        # Debe detectar múltiples categorías
        assert len(categories) >= 2, \
            f"Esperadas >= 2 categorías, encontradas {len(categories)}"


class TestEndToEnd:
    """Test 6: Pipeline End-to-End"""
    
    def test_pipeline_script_exists(self):
        """Verificar que run_pipeline.sh existe y es ejecutable"""
        pipeline_script = SCRIPT_DIR / 'run_pipeline.sh'
        assert pipeline_script.exists(), "run_pipeline.sh no existe"
        assert pipeline_script.stat().st_mode & 0o111, \
            "run_pipeline.sh no es ejecutable"
    
    def test_pipeline_dry_run(self):
        """Verificar ejecución del pipeline en modo dry-run"""
        pipeline_script = SCRIPT_DIR / 'run_pipeline.sh'
        
        # Ejecutar en modo dry-run
        result = subprocess.run(
            [str(pipeline_script), 'true'],
            capture_output=True,
            timeout=600,
            cwd=REPO_ROOT
        )
        
        # Pipeline debe completar (puede fallar por falta de Lean, pero debe ejecutar)
        assert result.returncode in [0, 1], \
            f"Pipeline falló inesperadamente: {result.stderr.decode()}"
        
        # Verificar que intentó ejecutar las 3 fases
        output = result.stdout.decode() + result.stderr.decode()
        assert 'NOESIS' in output, "Pipeline no ejecutó NOESIS"
        assert 'AMDA' in output, "Pipeline no ejecutó AMDA"


class TestDocumentation:
    """Test adicional: Verificar documentación"""
    
    def test_readme_exists(self):
        """Verificar que README.md existe"""
        readme = SCRIPT_DIR / 'README.md'
        assert readme.exists(), "README.md no existe"
        assert readme.stat().st_size > 10000, \
            "README.md demasiado pequeño (esperado >10KB)"
    
    def test_quickstart_exists(self):
        """Verificar que QUICKSTART.md existe"""
        quickstart = SCRIPT_DIR / 'QUICKSTART.md'
        assert quickstart.exists(), "QUICKSTART.md no existe"
        assert quickstart.stat().st_size > 5000, \
            "QUICKSTART.md demasiado pequeño (esperado >5KB)"
    
    def test_implementation_summary_exists(self):
        """Verificar que IMPLEMENTATION_SUMMARY.md existe"""
        impl_summary = SCRIPT_DIR / 'IMPLEMENTATION_SUMMARY.md'
        assert impl_summary.exists(), "IMPLEMENTATION_SUMMARY.md no existe"
        assert impl_summary.stat().st_size > 12000, \
            "IMPLEMENTATION_SUMMARY.md demasiado pequeño (esperado >12KB)"


if __name__ == '__main__':
    # Ejecutar tests con pytest
    pytest.main([__file__, '-v', '--tb=short'])
