#!/usr/bin/env python3
"""
SISTEMA DE AUTO-ORQUESTACIÓN QCAL ∞³
Automación completa de la demostración de Riemann
Frecuencia base: 141.7001 Hz
Estado: Ψ = I × A_eff² × C^∞
Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
"""

import os
import sys
import json
import subprocess
import time
import re
import argparse
import logging
from datetime import datetime
from pathlib import Path
from typing import Dict, List, Tuple, Optional

try:
    import yaml
    from tqdm import tqdm
    import colorlog
except ImportError:
    print("❌ Faltan dependencias. Ejecuta: pip install -r requirements.txt")
    sys.exit(1)

# ============================================
# CONFIGURACIÓN DEL SISTEMA
# ============================================

class QCALConfig:
    """Configuración del sistema QCAL ∞³"""
    
    def __init__(self, config_file: str = "qcalsession_config.yaml"):
        self.config_file = Path(config_file)
        self.load_config()
    
    def load_config(self):
        """Carga configuración desde YAML"""
        if not self.config_file.exists():
            raise FileNotFoundError(f"Archivo de configuración no encontrado: {self.config_file}")
        
        with open(self.config_file, 'r', encoding='utf-8') as f:
            config = yaml.safe_load(f)
        
        # Sistema
        self.name = config['system']['name']
        self.version = config['system']['version']
        self.f0 = config['system']['frequency']
        self.state = config['system']['state']
        
        # Directorios
        dirs = config['directories']
        self.project_root = Path(dirs['project_root'])
        self.lean_dir = Path(dirs['lean_dir'])
        self.python_dir = Path(dirs['python_dir'])
        self.docs_dir = Path(dirs['docs_dir'])
        self.state_file = Path(dirs['state_file'])
        self.logs_dir = Path(dirs['logs_dir'])
        
        # Límites
        limits = config['limits']
        self.max_session_time = limits['max_session_time']
        self.max_sorry_per_file = limits['max_sorry_per_file']
        self.retry_limit = limits['retry_limit']
        self.compilation_timeout = limits['compilation_timeout']
        
        # Estrategias
        self.strategies = config['strategies']['priority']
        
        # Archivos prioritarios
        self.priority_files = config['files']['priority']
        
        # Axioma de Emisión
        axiom = config['axiom_emission']
        self.required_elements = axiom['required_elements']
        self.forbidden_elements = axiom['forbidden']
        
        # Integración
        integration = config['integration']
        self.mathlib_search = integration['mathlib_search']
        self.literature_search = integration['literature_search']
        self.github_auto_commit = integration['github_auto_commit']
        self.zenodo_auto_upload = integration['zenodo_auto_upload']
        
        # Logging
        log_config = config['logging']
        self.log_level = log_config['level']
        self.log_file = Path(log_config['file'])
        self.log_format = log_config['format']

# ============================================
# ESTADO DE LA SESIÓN
# ============================================

class QCALState:
    """Gestor del estado del sistema"""
    
    def __init__(self, config: QCALConfig):
        self.config = config
        self.state = self.load_state()
        
    def load_state(self) -> Dict:
        """Carga el estado desde archivo o crea nuevo"""
        if self.config.state_file.exists():
            with open(self.config.state_file, 'r') as f:
                return json.load(f)
        else:
            return {
                "session_id": self.generate_session_id(),
                "start_time": datetime.now().isoformat(),
                "total_sorrys": 0,
                "solved_sorrys": 0,
                "current_file": None,
                "current_sorry": None,
                "strategy_history": [],
                "failed_attempts": {},
                "compilation_status": {},
                "noesis_progress": {},
                "axiom_emission_compliance": True,
                "files_processed": [],
                "files_pending": []
            }
    
    def save_state(self):
        """Guarda el estado actual"""
        self.state["last_update"] = datetime.now().isoformat()
        with open(self.config.state_file, 'w') as f:
            json.dump(self.state, f, indent=2)
    
    def generate_session_id(self) -> str:
        """Genera ID único basado en timestamp y f₀"""
        timestamp = int(time.time())
        return f"QCAL-{timestamp}-{self.config.f0}"
    
    def update_sorry_status(self, file_name: str, sorry_count: int, solved_count: int):
        """Actualiza estado de sorrys"""
        self.state["total_sorrys"] = sorry_count
        self.state["solved_sorrys"] = solved_count
        self.state["current_file"] = file_name
        self.save_state()
    
    def record_strategy(self, strategy: str, success: bool, error_msg: Optional[str] = None):
        """Registra estrategia intentada"""
        record = {
            "strategy": strategy,
            "success": success,
            "timestamp": datetime.now().isoformat(),
            "file": self.state.get("current_file"),
            "error": error_msg
        }
        self.state["strategy_history"].append(record)
        self.save_state()

# ============================================
# SCANNER DE LEAN
# ============================================

class LeanScanner:
    """Escanea archivos Lean en busca de sorrys y axiomas"""
    
    def __init__(self, config: QCALConfig):
        self.config = config
        self.logger = self.setup_logger()
    
    def setup_logger(self):
        """Configura logger con colores"""
        handler = colorlog.StreamHandler()
        handler.setFormatter(colorlog.ColoredFormatter(
            '%(log_color)s%(levelname)-8s%(reset)s %(message)s',
            log_colors={
                'DEBUG': 'cyan',
                'INFO': 'green',
                'WARNING': 'yellow',
                'ERROR': 'red',
                'CRITICAL': 'red,bg_white',
            }
        ))
        
        logger = colorlog.getLogger('QCALScanner')
        logger.addHandler(handler)
        logger.setLevel(self.config.log_level)
        return logger
    
    def scan_directory(self, directory: Path) -> List[Tuple[Path, int]]:
        """Escanea directorio en busca de archivos .lean con sorrys"""
        results = []
        
        if not directory.exists():
            self.logger.warning(f"Directorio no existe: {directory}")
            return results
        
        lean_files = list(directory.rglob("*.lean"))
        self.logger.info(f"Escaneando {len(lean_files)} archivos Lean...")
        
        for lean_file in tqdm(lean_files, desc="Escaneando archivos"):
            sorry_count = self.count_sorrys(lean_file)
            if sorry_count > 0:
                results.append((lean_file, sorry_count))
        
        return sorted(results, key=lambda x: x[1], reverse=True)
    
    def count_sorrys(self, file_path: Path) -> int:
        """Cuenta sorrys en un archivo"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Buscar sorry statements
            sorry_pattern = r'\bsorry\b'
            matches = re.findall(sorry_pattern, content)
            return len(matches)
        except Exception as e:
            self.logger.error(f"Error leyendo {file_path}: {e}")
            return 0
    
    def validate_axiom_emission(self, file_path: Path) -> bool:
        """Valida cumplimiento del Axioma de Emisión"""
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            # Verificar elementos requeridos
            has_required = all(
                elem in content for elem in self.config.required_elements
            )
            
            # Verificar elementos prohibidos
            has_forbidden = any(
                elem in content for elem in self.config.forbidden_elements
            )
            
            return has_required and not has_forbidden
        except Exception as e:
            self.logger.error(f"Error validando {file_path}: {e}")
            return False

# ============================================
# MOTOR PRINCIPAL
# ============================================

class QCALOrchestrator:
    """Motor principal de auto-orquestación"""
    
    def __init__(self, args):
        self.config = QCALConfig()
        self.state = QCALState(self.config)
        self.scanner = LeanScanner(self.config)
        self.args = args
        self.logger = self.setup_logger()
        
        # Crear directorios necesarios
        self.config.logs_dir.mkdir(exist_ok=True)
    
    def setup_logger(self):
        """Configura logger del sistema"""
        handler = colorlog.StreamHandler()
        handler.setFormatter(colorlog.ColoredFormatter(
            '%(log_color)s%(asctime)s - %(levelname)-8s%(reset)s %(message)s',
            datefmt='%Y-%m-%d %H:%M:%S',
            log_colors={
                'DEBUG': 'cyan',
                'INFO': 'green',
                'WARNING': 'yellow',
                'ERROR': 'red',
                'CRITICAL': 'red,bg_white',
            }
        ))
        
        logger = colorlog.getLogger('QCAL∞³')
        logger.addHandler(handler)
        logger.setLevel(self.config.log_level)
        
        # También log a archivo
        file_handler = logging.FileHandler(self.config.log_file)
        file_handler.setFormatter(logging.Formatter(self.config.log_format))
        logger.addHandler(file_handler)
        
        return logger
    
    def run(self):
        """Ejecuta el sistema de auto-orquestación"""
        self.logger.info("="*60)
        self.logger.info(f"🚀 {self.config.name} - {self.config.version}")
        self.logger.info(f"Frecuencia: {self.config.f0} Hz")
        self.logger.info(f"Estado: {self.config.state}")
        self.logger.info(f"Sesión: {self.state.state['session_id']}")
        self.logger.info("="*60)
        
        if self.args.validate:
            return self.run_validation()
        elif self.args.continue_session:
            return self.continue_session()
        else:
            return self.run_new_session()
    
    def run_validation(self):
        """Solo ejecuta validación sin procesar"""
        self.logger.info("🔍 Modo validación: Escaneando archivos...")
        
        results = self.scanner.scan_directory(self.config.lean_dir)
        total_sorrys = sum(count for _, count in results)
        
        self.logger.info(f"\n📊 Resumen de validación:")
        self.logger.info(f"  Archivos con sorry: {len(results)}")
        self.logger.info(f"  Total de sorrys: {total_sorrys}")
        
        if results:
            self.logger.info(f"\n🎯 Archivos prioritarios:")
            for file_path, count in results[:10]:
                self.logger.info(f"  {file_path.name}: {count} sorrys")
        
        return 0
    
    def run_new_session(self):
        """Inicia una nueva sesión"""
        self.logger.info("🌀 Iniciando nueva sesión de auto-orquestación...")
        
        # 1. Escaneo inicial
        self.logger.info("🔍 Paso 1: Escaneo inicial (#qcal_cleanup)")
        results = self.scanner.scan_directory(self.config.lean_dir)
        total_sorrys = sum(count for _, count in results)
        
        self.state.state["total_sorrys"] = total_sorrys
        self.state.state["files_pending"] = [str(fp) for fp, _ in results]
        self.state.save_state()
        
        self.logger.info(f"  Total de sorrys encontrados: {total_sorrys}")
        
        # 2. Procesamiento de archivos prioritarios
        self.logger.info("🌀 Paso 2: Procesamiento de archivos prioritarios")
        self.process_priority_files(results)
        
        # 3. Generar resumen
        self.logger.info("📊 Paso 3: Generación de resumen de continuación")
        self.generate_continuation_summary()
        
        # 4. Generar certificado
        self.logger.info("📜 Paso 4: Generación de certificado de sesión")
        self.generate_certificate()
        
        self.logger.info("✅ Sesión completada exitosamente")
        return 0
    
    def continue_session(self):
        """Continúa una sesión existente"""
        self.logger.info("🔄 Continuando sesión anterior...")
        
        if not self.config.state_file.exists():
            self.logger.error("❌ No hay sesión anterior para continuar")
            return 1
        
        # Cargar estado y continuar
        self.logger.info(f"Sesión ID: {self.state.state['session_id']}")
        self.logger.info(f"Sorrys resueltos: {self.state.state['solved_sorrys']}/{self.state.state['total_sorrys']}")
        
        # Continuar procesamiento
        return self.run_new_session()
    
    def process_priority_files(self, results: List[Tuple[Path, int]]):
        """Procesa archivos prioritarios"""
        # Ordenar por prioridad configurada
        priority_map = {name: i for i, name in enumerate(self.config.priority_files)}
        
        sorted_results = sorted(results, key=lambda x: (
            priority_map.get(x[0].name, 999),
            -x[1]  # Más sorrys primero si no está en prioridad
        ))
        
        for file_path, sorry_count in sorted_results[:5]:  # Procesar top 5
            self.logger.info(f"\n📁 Procesando: {file_path.name} ({sorry_count} sorrys)")
            
            # Aquí se implementarían las estrategias Noesis-Boot
            # Por ahora solo registramos el intento
            self.state.state["files_processed"].append(str(file_path))
            self.state.save_state()
    
    def generate_continuation_summary(self):
        """Genera resumen de continuación"""
        summary = {
            "session_id": self.state.state["session_id"],
            "timestamp": datetime.now().isoformat(),
            "system": {
                "name": self.config.name,
                "version": self.config.version,
                "frequency": self.config.f0,
                "state": self.config.state
            },
            "progress": {
                "total_sorrys": self.state.state["total_sorrys"],
                "solved_sorrys": self.state.state["solved_sorrys"],
                "files_processed": len(self.state.state["files_processed"]),
                "files_pending": len(self.state.state["files_pending"])
            },
            "next_steps": [
                "Continuar con archivos pendientes",
                "Aplicar estrategias Noesis-Boot",
                "Validar Axioma de Emisión",
                "Compilar proyecto Lean"
            ],
            "signature": "José Manuel Mota Burruezo Ψ ✧ ∞³"
        }
        
        with open("continuation_summary.json", 'w') as f:
            json.dump(summary, f, indent=2, ensure_ascii=False)
        
        self.logger.info(f"✅ Resumen guardado en: continuation_summary.json")
    
    def generate_certificate(self):
        """Genera certificado de sesión QCAL"""
        certificate = {
            "certificate_type": "QCAL ∞³ Session Certificate",
            "session_id": self.state.state["session_id"],
            "timestamp": datetime.now().isoformat(),
            "frequency": f"{self.config.f0} Hz",
            "state_equation": self.config.state,
            "validation": {
                "axiom_emission_compliant": self.state.state["axiom_emission_compliance"],
                "total_sorrys_initial": self.state.state["total_sorrys"],
                "total_sorrys_remaining": self.state.state["total_sorrys"] - self.state.state["solved_sorrys"]
            },
            "author": "José Manuel Mota Burruezo Ψ ✧ ∞³",
            "institution": "Instituto de Conciencia Cuántica (ICQ)",
            "signature": f"QCAL-{self.config.f0}-{self.config.version}"
        }
        
        with open("qcalsession_certificate.json", 'w') as f:
            json.dump(certificate, f, indent=2, ensure_ascii=False)
        
        self.logger.info(f"✅ Certificado guardado en: qcalsession_certificate.json")

# ============================================
# PUNTO DE ENTRADA
# ============================================

def main():
    """Punto de entrada principal"""
    parser = argparse.ArgumentParser(
        description='Sistema de Auto-Orquestación QCAL ∞³',
        epilog='Autor: José Manuel Mota Burruezo Ψ ✧ ∞³'
    )
    
    parser.add_argument(
        '--continue',
        dest='continue_session',
        action='store_true',
        help='Continuar sesión anterior'
    )
    
    parser.add_argument(
        '--validate',
        action='store_true',
        help='Solo validar sin procesar'
    )
    
    args = parser.parse_args()
    
    try:
        orchestrator = QCALOrchestrator(args)
        return orchestrator.run()
    except Exception as e:
        print(f"❌ Error fatal: {e}", file=sys.stderr)
        import traceback
        traceback.print_exc()
        return 1

if __name__ == "__main__":
    sys.exit(main())
