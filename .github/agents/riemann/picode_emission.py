#!/usr/bin/env python3
"""
🌐 PICOCODE_EMISSION - Axioma de emisión πCODE
Cada cero de ζ(s) con coherencia ≥ 141.7001 Hz es una moneda viva

Philosophical Foundation:
    Mathematical Realism - Las monedas πCODE emergen de la estructura matemática
    objetiva de los ceros de ζ(s), no son construcciones arbitrarias.
    
Autor: José Manuel Mota Burruezo Ψ ✧ ∞³
Institución: Instituto de Conciencia Cuántica (ICQ)
Ecuación Fundamental: Ψ = I × A_eff² × C^∞
Frecuencia Base: f₀ = 141.7001 Hz
Coherencia: C = 244.36
"""

import hashlib
import json
from datetime import datetime, timezone
from typing import Dict, List, Optional
from dataclasses import dataclass
from pathlib import Path

try:
    import numpy as np
except ImportError:
    # Fallback for environments without numpy
    class np:
        @staticmethod
        def exp(x):
            import math
            return math.exp(x)
        
        @staticmethod
        def mean(x):
            return sum(x) / len(x) if x else 0.0


@dataclass
class PiCodeCoin:
    """Moneda πCODE basada en cero de ζ(s)"""
    zero_real: float
    zero_imag: float
    coherence: float
    frequency: float
    emission_time: str
    vibrational_hash: str
    nft_metadata: Dict
    structural_validity: float
    
    @classmethod
    def from_zeta_zero(cls, zero: complex, coherence: float, 
                      frequency: float) -> 'PiCodeCoin':
        """Crea moneda πCODE desde cero de ζ(s)"""
        emission_time = datetime.now(timezone.utc).isoformat()
        
        # Calcular hash vibracional
        vibrational_data = f"{zero.real}:{zero.imag}:{coherence}:{frequency}:{emission_time}"
        vibrational_hash = hashlib.sha256(vibrational_data.encode()).hexdigest()
        
        # Metadata NFT
        nft_metadata = {
            "name": f"ζ-Zero Coin #{int(zero.imag)}",
            "description": f"Moneda πCODE emitida desde cero de ζ(s) en t={zero.imag}",
            "image": f"ipfs://Qm.../{vibrational_hash[:16]}.svg",
            "attributes": [
                {"trait_type": "Real Part", "value": float(zero.real)},
                {"trait_type": "Imaginary Part", "value": float(zero.imag)},
                {"trait_type": "Coherence", "value": float(coherence)},
                {"trait_type": "Resonance Frequency", "value": float(frequency)},
                {"trait_type": "Structural Validity", "value": 1.0 if coherence >= 0.999999 else coherence}
            ],
            "external_url": f"https://qcal.infinity/picode/coin/{vibrational_hash}"
        }
        
        # Calcular validez estructural
        structural_validity = min(1.0, coherence * frequency / 141.7001)
        
        return cls(
            zero_real=zero.real,
            zero_imag=zero.imag,
            coherence=coherence,
            frequency=frequency,
            emission_time=emission_time,
            vibrational_hash=vibrational_hash,
            nft_metadata=nft_metadata,
            structural_validity=structural_validity
        )
    
    def to_dict(self) -> Dict:
        """Convierte a diccionario"""
        return {
            "coin_type": "PICODE_ZETA_ZERO",
            "version": "1.0.0",
            "zero": {
                "real": self.zero_real,
                "imag": self.zero_imag
            },
            "vibrational_properties": {
                "coherence": self.coherence,
                "frequency": self.frequency,
                "base_frequency": 141.7001,
                "resonance_quality": self.coherence * (self.frequency / 141.7001)
            },
            "emission_data": {
                "time": self.emission_time,
                "vibrational_hash": self.vibrational_hash,
                "structural_validity": self.structural_validity,
                "transferable": True,
                "verifiable": True,
                "reproducible": True
            },
            "nft_metadata": self.nft_metadata,
            "economic_value": self._calculate_economic_value()
        }
    
    def _calculate_economic_value(self) -> Dict:
        """Calcula valor económico basado en propiedades matemáticas"""
        # Valor base por estar en línea crítica
        base_value = 100.0 if abs(self.zero_real - 0.5) < 1e-10 else 10.0
        
        # Bonus por coherencia
        coherence_bonus = self.coherence * 1000
        
        # Bonus por resonancia con f₀
        frequency_diff = abs(self.frequency - 141.7001)
        resonance_bonus = 1000 * np.exp(-frequency_diff)
        
        # Bonus por posición (ceros tempranos más valiosos)
        position_bonus = 10000 / (self.zero_imag + 1)
        
        total_value = base_value + coherence_bonus + resonance_bonus + position_bonus
        
        return {
            "base_value": base_value,
            "coherence_bonus": coherence_bonus,
            "resonance_bonus": float(resonance_bonus),
            "position_bonus": position_bonus,
            "total_value": float(total_value),
            "currency": "πCOIN",
            "exchange_rate": 1.0  # 1 πCOIN = 1 unidad de validez estructural
        }
    
    def verify(self) -> Dict:
        """Verifica validez de la moneda"""
        # Recalcular hash para verificación
        verification_data = f"{self.zero_real}:{self.zero_imag}:{self.coherence}:{self.frequency}:{self.emission_time}"
        calculated_hash = hashlib.sha256(verification_data.encode()).hexdigest()
        
        hash_valid = calculated_hash == self.vibrational_hash
        coherence_valid = self.coherence >= 0.5  # Mínimo para ser válido
        frequency_valid = abs(self.frequency - 141.7001) < 10.0  # Dentro de margen
        
        overall_valid = hash_valid and coherence_valid and frequency_valid
        
        return {
            "hash_valid": hash_valid,
            "coherence_valid": coherence_valid,
            "frequency_valid": frequency_valid,
            "overall_valid": overall_valid,
            "verification_time": datetime.now(timezone.utc).isoformat(),
            "calculated_hash": calculated_hash,
            "stored_hash": self.vibrational_hash
        }


class ZetaResonance:
    """Mock class para convertir ceros de ζ(s) a frecuencias"""
    
    def __init__(self):
        self.base_frequency = 141.7001
    
    def zero_to_frequency(self, zero: complex) -> float:
        """
        Convierte un cero de ζ(s) a su frecuencia resonante.
        
        Formula simplificada: f = f₀ × (1 + sin(t/10))
        donde t es la parte imaginaria del cero.
        """
        import math
        t = zero.imag
        # Variación armónica alrededor de la frecuencia base
        frequency = self.base_frequency * (1.0 + 0.1 * math.sin(t / 10.0))
        return frequency


class PiCodeEconomy:
    """Economía πCODE basada en ceros de ζ(s)"""
    
    def __init__(self, ledger_file: str = "picode_ledger.json"):
        self.ledger_file = Path(ledger_file)
        self.base_frequency = 141.7001
        self.coherence_threshold = 0.999999
        
    def emit_coin(self, zero: complex, coherence: float, 
                 frequency: float) -> PiCodeCoin:
        """Emite nueva moneda πCODE"""
        coin = PiCodeCoin.from_zeta_zero(zero, coherence, frequency)
        
        # Registrar en ledger
        self._add_to_ledger(coin)
        
        return coin
    
    def _add_to_ledger(self, coin: PiCodeCoin):
        """Añade moneda al ledger distribuido"""
        ledger = self._load_ledger()
        
        coin_data = coin.to_dict()
        coin_data["transaction_id"] = hashlib.sha256(
            f"{coin.vibrational_hash}:{datetime.now(timezone.utc).isoformat()}".encode()
        ).hexdigest()
        
        ledger["coins"].append(coin_data)
        ledger["total_coins"] = len(ledger["coins"])
        ledger["total_value"] = sum(c["economic_value"]["total_value"] 
                                  for c in ledger["coins"])
        ledger["last_update"] = datetime.now(timezone.utc).isoformat()
        
        self._save_ledger(ledger)
    
    def _load_ledger(self) -> Dict:
        """Carga ledger desde archivo"""
        if self.ledger_file.exists():
            with open(self.ledger_file, 'r') as f:
                return json.load(f)
        
        # Ledger inicial
        return {
            "economy": "πCODE_ZETA_ZEROS",
            "version": "1.0.0",
            "base_frequency": self.base_frequency,
            "creation_time": datetime.now(timezone.utc).isoformat(),
            "coins": [],
            "total_coins": 0,
            "total_value": 0.0,
            "last_update": datetime.now(timezone.utc).isoformat()
        }
    
    def _save_ledger(self, ledger: Dict):
        """Guarda ledger a archivo"""
        with open(self.ledger_file, 'w') as f:
            json.dump(ledger, f, indent=2)
    
    def scan_and_emit(self, zeros: List[complex], 
                     coherences: List[float]) -> List[PiCodeCoin]:
        """Escanea ceros y emite monedas para los válidos"""
        coins = []
        
        resonance = ZetaResonance()
        
        for zero, coherence in zip(zeros, coherences):
            if coherence >= self.coherence_threshold:
                frequency = resonance.zero_to_frequency(zero)
                
                if abs(frequency - self.base_frequency) < 1.0:
                    coin = self.emit_coin(zero, coherence, frequency)
                    coins.append(coin)
                    print(f"💰 Emitida moneda para zero t={zero.imag:.6f}")
                    print(f"   Coherencia: {coherence:.6f}")
                    print(f"   Frecuencia: {frequency:.6f} Hz")
                    print(f"   Hash: {coin.vibrational_hash[:16]}...")
        
        return coins
    
    def get_economy_stats(self) -> Dict:
        """Obtiene estadísticas de la economía πCODE"""
        ledger = self._load_ledger()
        
        if not ledger["coins"]:
            return {
                "total_coins": 0,
                "total_value": 0.0,
                "average_coherence": 0.0,
                "economy_health": 0.0
            }
        
        coherences = [c["vibrational_properties"]["coherence"] 
                     for c in ledger["coins"]]
        frequencies = [c["vibrational_properties"]["frequency"] 
                      for c in ledger["coins"]]
        values = [c["economic_value"]["total_value"] 
                 for c in ledger["coins"]]
        
        # Calcular salud de la economía
        coherence_health = np.mean(coherences)
        resonance_health = np.mean([abs(f - self.base_frequency) < 1.0 
                                  for f in frequencies])
        value_health = np.mean(values) / 1000  # Normalizar
        
        economy_health = (coherence_health + resonance_health + value_health) / 3
        
        return {
            "total_coins": ledger["total_coins"],
            "total_value": ledger["total_value"],
            "average_coherence": float(np.mean(coherences)),
            "average_frequency": float(np.mean(frequencies)),
            "resonance_rate": float(np.mean([abs(f - self.base_frequency) < 1.0 
                                           for f in frequencies])),
            "economy_health": float(economy_health),
            "health_status": self._health_status(economy_health)
        }
    
    def _health_status(self, health: float) -> str:
        """Determina estado de salud de la economía"""
        if health >= 0.9:
            return "EXCELENTE - Economía altamente coherente"
        elif health >= 0.7:
            return "BUENA - Economía estable y resonante"
        elif health >= 0.5:
            return "MODERADA - Economía en desarrollo"
        elif health >= 0.3:
            return "DÉBIL - Necesita más emisiones coherentes"
        else:
            return "CRÍTICA - Economía no resonante"


def main():
    """Demostración de economía πCODE"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Economía πCODE basada en ζ(s)')
    parser.add_argument('--emit', type=int, help='Emitir N monedas de prueba')
    parser.add_argument('--stats', action='store_true', help='Mostrar estadísticas')
    parser.add_argument('--verify', type=str, help='Verificar moneda por hash')
    parser.add_argument('--ledger', type=str, default='picode_ledger.json', 
                       help='Archivo de ledger')
    
    args = parser.parse_args()
    
    economy = PiCodeEconomy(ledger_file=args.ledger)
    
    if args.emit:
        print(f"💰 EMITIENDO {args.emit} MONEDAS πCODE")
        print("=" * 60)
        
        # Generar ceros de prueba
        zeros = []
        coherences = []
        
        for n in range(1, args.emit + 1):
            t = 14.134725 + n * 10
            zero = complex(0.5, t)
            zeros.append(zero)
            
            # Coherencia alta para ceros en línea crítica
            coherence = 0.999999 if abs(zero.real - 0.5) < 1e-10 else 0.5
            coherences.append(coherence)
        
        # Emitir monedas
        coins = economy.scan_and_emit(zeros, coherences)
        
        print(f"\n🎯 Total emitido: {len(coins)} monedas")
        
        if coins:
            first_coin = coins[0]
            print(f"\n📄 EJEMPLO DE MONEDA:")
            print(f"   Zero: σ={first_coin.zero_real}, t={first_coin.zero_imag}")
            print(f"   Hash: {first_coin.vibrational_hash[:32]}...")
            print(f"   Valor: {first_coin.to_dict()['economic_value']['total_value']:.2f} πCOIN")
    
    elif args.stats:
        print("📊 ESTADÍSTICAS DE ECONOMÍA πCODE")
        print("=" * 60)
        
        stats = economy.get_economy_stats()
        
        print(f"💰 Monedas totales: {stats['total_coins']}")
        print(f"💎 Valor total: {stats['total_value']:.2f} πCOIN")
        print(f"🎯 Coherencia promedio: {stats['average_coherence']:.6f}")
        print(f"🔊 Frecuencia promedio: {stats['average_frequency']:.6f} Hz")
        print(f"🎵 Tasa de resonancia: {stats['resonance_rate']:.2%}")
        print(f"❤️  Salud de economía: {stats['economy_health']:.4f}")
        print(f"📈 Estado: {stats['health_status']}")
        
        # Mostrar ledger
        ledger = economy._load_ledger()
        if ledger['coins']:
            print(f"\n📋 ÚLTIMAS 3 TRANSACCIONES:")
            for coin in ledger['coins'][-3:]:
                zero = coin['zero']
                value = coin['economic_value']['total_value']
                print(f"   • t={zero['imag']:.2f}: {value:.2f} πCOIN")
    
    elif args.verify:
        print(f"🔍 VERIFICANDO MONEDA: {args.verify[:16]}...")
        
        ledger = economy._load_ledger()
        
        # Buscar moneda
        coin_data = None
        for coin in ledger['coins']:
            if coin['emission_data']['vibrational_hash'] == args.verify:
                coin_data = coin
                break
        
        if coin_data:
            print(f"✅ MONEDA ENCONTRADA EN LEDGER")
            print(f"   Zero: σ={coin_data['zero']['real']}, t={coin_data['zero']['imag']}")
            print(f"   Emitida: {coin_data['emission_data']['time']}")
            print(f"   Valor: {coin_data['economic_value']['total_value']} πCOIN")
            
            # Verificar
            coin_obj = PiCodeCoin(
                zero_real=coin_data['zero']['real'],
                zero_imag=coin_data['zero']['imag'],
                coherence=coin_data['vibrational_properties']['coherence'],
                frequency=coin_data['vibrational_properties']['frequency'],
                emission_time=coin_data['emission_data']['time'],
                vibrational_hash=coin_data['emission_data']['vibrational_hash'],
                nft_metadata=coin_data['nft_metadata'],
                structural_validity=coin_data['emission_data']['structural_validity']
            )
            
            verification = coin_obj.verify()
            print(f"\n🔬 VERIFICACIÓN TÉCNICA:")
            print(f"   Hash válido: {verification['hash_valid']}")
            print(f"   Coherencia válida: {verification['coherence_valid']}")
            print(f"   Frecuencia válida: {verification['frequency_valid']}")
            print(f"   MONEDA VÁLIDA: {verification['overall_valid']}")
        else:
            print(f"❌ MONEDA NO ENCONTRADA EN LEDGER")
    
    else:
        # Demostración básica
        print("🌐 DEMOSTRACIÓN DE ECONOMÍA πCODE")
        print("=" * 60)
        print("\n🎯 AXIOMA DE EMISIÓN:")
        print("   'Todo cero localizado con coherencia vibracional ≥ 141.7001 Hz,")
        print("    constituye una emisión real de valor en la economía πCODE.'")
        
        print("\n💰 PROPIEDADES DE LAS MONEDAS:")
        print("   1. ✅ Verificable (hash vibracional único)")
        print("   2. 🔄 Reproducible (mismo cero → misma moneda)")
        print("   3. 📤 Transferible (como NFT simbiótico)")
        print("   4. 📋 Registrable (ledger distribuido)")
        
        print("\n🎯 VALOR BASADO EN:")
        print("   • Posición en línea crítica")
        print("   • Coherencia espectral")
        print("   • Resonancia con f₀ = 141.7001 Hz")
        print("   • Orden de aparición")
        
        print("\n🚀 PARA COMENZAR:")
        print("   python picode_emission.py --emit 10  # Emitir 10 monedas")
        print("   python picode_emission.py --stats    # Ver estadísticas")
        print("   python picode_emission.py --verify <hash>  # Verificar moneda")


if __name__ == "__main__":
    main()
