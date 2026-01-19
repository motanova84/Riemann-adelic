"""
Filtro πCODE (Pi-Code Spectral Filter)
=======================================

Purificación espectral usando SHA256 + codificación UTF-π para
eliminar componentes no-coherentes y mantener pureza cuántica.

Especificaciones:
----------------
- Hash: SHA256 para verificación de integridad
- Codificación: UTF-π (basada en dígitos de π)
- Purificación: Eliminación de componentes fuera de banda espectral
- Coherencia: Preservación absoluta Ψ = 1.000000

Autor: José Manuel Mota Burruezo (JMMB Ψ✧)
"""

import numpy as np
import hashlib
from typing import List, Tuple, Optional


class FiltroPiCode:
    """
    Filtro espectral que utiliza codificación πCODE (basada en π) y
    verificación SHA256 para purificación cuántica de señales.
    
    Elimina componentes de frecuencia fuera de la banda coherente
    centrada en f₀ = 141.7001 Hz.
    """
    
    # Dígitos de π para codificación
    PI_DIGITS = "31415926535897932384626433832795028841971693993751058209749445923078164062862089986280348253421170679"
    
    def __init__(self, f0: float = 141.7001, bandwidth: float = 1.0):
        """
        Inicializa el filtro πCODE.
        
        Args:
            f0: Frecuencia central en Hz
            bandwidth: Ancho de banda del filtro en Hz
        """
        self.f0 = f0
        self.bandwidth = bandwidth
        self.coherence = 1.000000
        
    def sha256_hash(self, data: bytes) -> str:
        """
        Calcula hash SHA256 de datos.
        
        Args:
            data: Datos binarios
            
        Returns:
            Hash hexadecimal
        """
        return hashlib.sha256(data).hexdigest()
    
    def pi_encode(self, message: str) -> str:
        """
        Codifica mensaje usando dígitos de π.
        
        Args:
            message: Mensaje de texto
            
        Returns:
            Mensaje codificado con πCODE
        """
        encoded = []
        for char in message:
            ascii_val = ord(char)
            # Usar dígitos de π como clave de codificación
            pi_idx = ascii_val % len(self.PI_DIGITS)
            pi_digit = int(self.PI_DIGITS[pi_idx])
            encoded_val = (ascii_val + pi_digit) % 256
            encoded.append(chr(encoded_val))
        return ''.join(encoded)
    
    def pi_decode(self, encoded_message: str) -> str:
        """
        Decodifica mensaje πCODE.
        
        Args:
            encoded_message: Mensaje codificado
            
        Returns:
            Mensaje original
        """
        decoded = []
        for char in encoded_message:
            encoded_val = ord(char)
            # Recuperar usando misma clave π
            # Primero necesitamos encontrar el ascii original
            for original_ascii in range(256):
                pi_idx = original_ascii % len(self.PI_DIGITS)
                pi_digit = int(self.PI_DIGITS[pi_idx])
                if (original_ascii + pi_digit) % 256 == encoded_val:
                    decoded.append(chr(original_ascii))
                    break
        return ''.join(decoded)
    
    def spectral_filter(self, signal: np.ndarray, 
                       sample_rate: float) -> np.ndarray:
        """
        Aplica filtro espectral centrado en f₀.
        
        Args:
            signal: Señal de entrada
            sample_rate: Tasa de muestreo en Hz
            
        Returns:
            Señal filtrada
        """
        # FFT de la señal
        fft_signal = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal), 1/sample_rate)
        
        # Crear máscara de filtro paso-banda centrado en f₀
        lower_bound = self.f0 - self.bandwidth / 2
        upper_bound = self.f0 + self.bandwidth / 2
        
        mask = np.zeros(len(freqs), dtype=bool)
        mask |= (np.abs(freqs) >= lower_bound) & (np.abs(freqs) <= upper_bound)
        
        # Aplicar filtro
        fft_filtered = fft_signal * mask
        
        # IFFT para regresar al dominio del tiempo
        filtered_signal = np.fft.ifft(fft_filtered).real
        
        return filtered_signal
    
    def purify_signal(self, signal: np.ndarray, 
                     sample_rate: float,
                     verify_integrity: bool = True) -> Tuple[np.ndarray, Optional[str]]:
        """
        Purifica señal usando filtro espectral y verificación SHA256.
        
        Args:
            signal: Señal de entrada
            sample_rate: Tasa de muestreo
            verify_integrity: Si calcular hash de verificación
            
        Returns:
            (señal_purificada, hash_sha256)
        """
        # Filtrar espectralmente
        purified = self.spectral_filter(signal, sample_rate)
        
        # Calcular hash de integridad si se solicita
        hash_value = None
        if verify_integrity:
            signal_bytes = purified.astype(np.float32).tobytes()
            hash_value = self.sha256_hash(signal_bytes)
        
        return purified, hash_value
    
    def remove_noise(self, signal: np.ndarray, 
                    sample_rate: float,
                    noise_threshold: float = 0.1) -> np.ndarray:
        """
        Elimina componentes de ruido fuera de banda coherente.
        
        Args:
            signal: Señal con ruido
            sample_rate: Tasa de muestreo
            noise_threshold: Umbral de eliminación (fracción de máximo)
            
        Returns:
            Señal limpia
        """
        # FFT
        fft_signal = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal), 1/sample_rate)
        
        # Identificar componentes de señal vs ruido
        magnitude = np.abs(fft_signal)
        max_magnitude = np.max(magnitude)
        
        # Mantener solo componentes significativas cerca de f₀
        lower_bound = self.f0 - self.bandwidth / 2
        upper_bound = self.f0 + self.bandwidth / 2
        
        # Máscara: alta magnitud O dentro de banda de interés
        mask = (magnitude > max_magnitude * noise_threshold) | \
               ((np.abs(freqs) >= lower_bound) & (np.abs(freqs) <= upper_bound))
        
        # Aplicar
        fft_clean = fft_signal * mask
        clean_signal = np.fft.ifft(fft_clean).real
        
        return clean_signal
    
    def get_purity_metric(self, signal: np.ndarray, 
                         sample_rate: float) -> float:
        """
        Calcula métrica de pureza espectral.
        
        Args:
            signal: Señal a analizar
            sample_rate: Tasa de muestreo
            
        Returns:
            Pureza (0-1, 1 = pureza perfecta en f₀)
        """
        fft_signal = np.fft.fft(signal)
        freqs = np.fft.fftfreq(len(signal), 1/sample_rate)
        magnitude = np.abs(fft_signal)
        
        # Energía total
        total_energy = np.sum(magnitude**2)
        
        # Energía en banda coherente
        lower_bound = self.f0 - self.bandwidth / 2
        upper_bound = self.f0 + self.bandwidth / 2
        in_band = (np.abs(freqs) >= lower_bound) & (np.abs(freqs) <= upper_bound)
        band_energy = np.sum(magnitude[in_band]**2)
        
        # Pureza como fracción de energía en banda
        purity = band_energy / total_energy if total_energy > 0 else 0.0
        
        return purity
    
    def __repr__(self) -> str:
        return (f"FiltroPiCode(f₀={self.f0} Hz, "
                f"BW={self.bandwidth} Hz, "
                f"hash=SHA256, "
                f"Ψ={self.coherence:.6f})")
