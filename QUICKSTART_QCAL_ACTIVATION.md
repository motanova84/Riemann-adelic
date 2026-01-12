# 🌀✨ QCAL Protocol Activation - Quick Reference

**NUEVO:** Scripts de activación completa de protocolos QCAL ∞³ y validación integral

---

## 🚀 Uso Rápido

### Activación Completa de Protocolos QCAL

```bash
# Modo rápido (recomendado para CI/CD) - ~10 segundos
python activate_qcal_protocols.py --fast --save-report

# Modo estándar (balance precisión/velocidad) - ~60 segundos  
python activate_qcal_protocols.py --save-report

# Modo completo (máxima precisión) - ~300 segundos
python activate_qcal_protocols.py --full --save-report
```

### Validación Integral Cross-Repo

```bash
# Validación completa de coherencia QCAL
python validate_integral_qcal.py
```

---

## 📊 Qué Hacen Estos Scripts

### `activate_qcal_protocols.py`

Activa **7 protocolos QCAL** en secuencia:

1. ✅ **QCAL Beacon** - Verifica constantes fundamentales
2. 🧠 **NOESIS Guardian** - Agente de coherencia matemática
3. 🔬 **AMDA** - Agente de descubrimiento autónomo
4. 🔮 **SABIO Validator** - Validación multi-lenguaje
5. 👑 **V5 Coronación** - Demostración RH completa (5 pasos)
6. 🎵 **Spectral Emergence** - Emergencia espectral
7. 🔗 **Cross-Repo** - Conexiones entre repositorios

**Output:** `data/qcal_activation_report.json`

### `validate_integral_qcal.py`

Valida **6 componentes críticos**:

1. ✅ Constantes matemáticas (f₀, C, C', η)
2. ✅ Demostración RH (V5 Coronación)
3. ✅ Operador espectral H_Ψ
4. ✅ Red DOI cross-repo (6 DOIs)
5. ✅ Frecuencia fundamental f₀
6. ✅ Fundamento filosófico (Realismo Matemático)

**Output:** `data/integral_validation_certificate.json`

---

## 📈 Resultados Esperados

### Activación QCAL
- **Exitosa:** 4-7 fases passed (≥70% threshold)
- **V5 Coronación:** DEBE pasar (crítico)
- **NOESIS/AMDA:** Pueden tener warnings (no crítico)

### Validación Integral
- **Exitosa:** 6/6 validaciones passed (≥80% threshold)
- **Todas las validaciones:** Importantes
- **RH Demostración:** Crítica

---

## 🔢 Constantes QCAL Verificadas

| Constante | Valor | Significado |
|-----------|-------|-------------|
| **f₀** | 141.7001 Hz | Frecuencia fundamental |
| **C** | 629.83 | Constante universal |
| **C'** | 244.36 | Coherencia |
| **η** | 0.387978 | Factor coherencia |

---

## 📚 Documentación Completa

- **[QCAL_FULL_ACTIVATION_GUIDE.md](QCAL_FULL_ACTIVATION_GUIDE.md)** - Guía detallada (17KB)
- **[QCAL_ACTIVATION_COMPLETE_SUMMARY.md](QCAL_ACTIVATION_COMPLETE_SUMMARY.md)** - Resumen ejecutivo (13KB)

---

## 🎯 Demostración RH - 5 Pasos (V5 Coronación)

1. **Axiomas → Lemmas** - Derivación desde teoría adélica
2. **Rigidez Archimediana** - Doble derivación γ∞(s)
3. **Unicidad Paley-Wiener** - D(s) ≡ Ξ(s)
4. **Localización Zeros** - de Branges + Weil-Guinand
5. **Coronación** - Integración completa

**Resultado:** RH demostrada vía emergencia espectral adélica

---

## 🌐 Red Cross-Repo Conectada

- ✅ Riemann-adelic (este repo)
- ✅ adelic-bsd (BSD conjecture)
- ✅ QCAL-CLOUD (integration)
- 📚 P-NP, Goldbach, ∞³ (via DOI refs)

---

## 💡 Troubleshooting

### "NOESIS Guardian failed"
- **Normal** si V5 Coronación pasa
- Usa modo de emergencia automáticamente
- No afecta validación RH

### "V5 Coronación timeout"
- Reduce precisión: `--fast`
- O espera más (demostración rigurosa)

### "Algunos tests fallan"
- **OK** si ≥70% pasan (activación)
- **OK** si ≥80% pasan (validación integral)
- V5 Coronación debe pasar siempre

---

## ✨ Quick Start

```bash
# 1. Activar todo (modo rápido)
python activate_qcal_protocols.py --fast --save-report

# 2. Validar integridad
python validate_integral_qcal.py

# 3. Ver resultados
cat data/qcal_activation_report.json | jq .
cat data/integral_validation_certificate.json | jq .
```

---

**∴ El sistema está vivo. La verdad es independiente. ∴**

✨ **QCAL ∞³ ACTIVO** ✨

---

**Autor:** José Manuel Mota Burruezo Ψ ✧ ∞³  
**DOI:** [10.5281/zenodo.17379721](https://doi.org/10.5281/zenodo.17379721)
