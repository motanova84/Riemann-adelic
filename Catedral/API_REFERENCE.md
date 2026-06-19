# 📡 API Reference — πCODE Spectral Liquidity Engine v7.2

## PiCodeSpectralCathedral

Versión: 7.2.0
Solidity: ^0.8.19
Licencia: MIT

---

## Constantes

- F0 = 1417001 (f₀ × 10⁴)
- PHI = 161803398875 (Φ × 10¹¹)
- GAMMA = 61803398875 (γ × 10¹¹)
- TAU_C = 999999
- TAU_S = 1000000
- TAU_T = 2000
- SPECTRAL_STATES = 13

---

## Estructuras

### SpectralState

```solidity
struct SpectralState {
  uint8 n;
  uint256 E_n_magnitude;   // |E_n| × 10⁶
  uint256 coherence;        // C_n × 10⁶
  uint256 lifetime;         // τ_n × 10⁶
  uint256 capacity;         // L_n en πCODE
  string interpretation;
}
```

### LiquidityPosition

```solidity
struct LiquidityPosition {
  bytes32 contractId;
  uint8 spectralState;
  address owner;
  uint256 principal;
  uint256 lockPeriod;
  uint256 createdAt;
  uint256 coherenceAtCreation;
  bool claimed;
}
```

---

## Funciones de Lectura

### spectralStates
`function spectralStates(uint8 index) external view returns (SpectralState memory)`

### positions
`function positions(bytes32 contractId) external view returns (LiquidityPosition memory)`

### ownerPositions
`function ownerPositions(address owner) external view returns (bytes32[] memory)`

### totalLiquidityByState
`function totalLiquidityByState(uint8 state) external view returns (uint256)`

### currentValue
`function currentValue(bytes32 contractId) external view returns (uint256)`

Fórmula: `valor = principal + (principal × |E_n| × C_n² × días) / (30 × 10¹²)`

### computeSystemCoherence
`function computeSystemCoherence() external view returns (uint256)`

Fórmula: Ψ_sistema = Σ(C_n × liquidez_n) / liquidez_total

### validateCoherence
`function validateCoherence(uint8 n) external view returns (uint256)`

Fórmula: Ψ(B_n) = min(C_n/τ_C, S_n/τ_S, 1−T_n/τ_T)

---

## Funciones de Escritura

### createPosition
`function createPosition(uint8 spectralState, uint256 lockPeriodDays) external payable returns (bytes32)`

### spectralTransition
`function spectralTransition(bytes32 contractId, uint8 newState) external`

### claim
`function claim(bytes32 contractId) external`

---

## Funciones Administrativas (onlyDirector)

- `emitGuardianPulse()`
- `deactivateCathedral()` / `reactivateCathedral()`
- `transferDirector(address newDirector)`

---

## Eventos

- `CathedralActivated(uint256 timestamp, bytes32 crystalHash)`
- `PositionCreated(bytes32 indexed contractId, uint8 indexed spectralState, address indexed owner, uint256 principal, uint256 maturity)`
- `CoherenceValidated(bytes32 indexed contractId, uint256 psi, bool accepted)`
- `SpectralTransition(bytes32 indexed contractId, uint8 fromState, uint8 toState, uint256 newValue)`
- `GuardianPulse(uint256 indexed pulseNumber, uint256 coherence, uint256 totalLiquidity)`
- `ClaimExecuted(bytes32 indexed contractId, address indexed owner, uint256 value)`

---

## Estados Espectrales Precalculados

| n | |E_n| (×10⁶) | Coherencia (×10⁶) | Vida (×10⁶) | Capacidad (πCODE) | Interpretación |
|---|------------|------------------|------------|------------------|----------------|
| 0 | 1118034 | 447214 | 1000000 | 1250000 | FUNDAMENTAL |
| 1 | 2003902 | 62378 | 500000 | 4015625 | PRIMARIO |
| 2 | 3000514 | 18515 | 333333 | 9003086 | ARMÓNICO |
| 3 | 4000122 | 7812 | 250000 | 16000977 | EXPANSIVO |
| 4 | 5000040 | 4000 | 200000 | 25000400 | ESTABILIZADOR |
| 5 | 6000016 | 2315 | 166666 | 36000193 | COLECTIVO |
| 6 | 7000007 | 1458 | 142857 | 49000104 | ADÉLICO |
| 7 | 8000004 | 977 | 125000 | 64000061 | SOBERANO |
| 8 | 9000002 | 686 | 111111 | 81000038 | FLASH |
| 9 | 10000001 | 500 | 100000 | 100000025 | ARBITRAGE |
| 10 | 11000001 | 376 | 90909 | 121000017 | EQUILIBRIO |
| 11 | 12000001 | 289 | 83333 | 144000012 | PATRIMONIO |
| 12 | 13000000 | 228 | 76923 | 169000009 | LIBERTAD |

---

## Referencias

- [Lean 4 Formalization](SPECTRAL_MONOTONICITY_v7_2.lean)
- [Whitepaper QCAL](https://github.com/motanova84/noesis88)
- [RFC PoCΨ v1.0]

---

∴𓂀Ω∞³Φ · TUYOYOTU · HECHO ESTÁ
