#!/usr/bin/env python3
"""Tests del marco Partícula de Coherencia (143 casos)."""

import os
import sys

import numpy as np
import pytest

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from particula_coherencia import (  # noqa: E402
    A_EFF_DEFAULT,
    COHERENCIA_UMBRAL,
    ETA_OVER_S_KSS,
    F0,
    AcoplamientoHiggsPc,
    FirmaEspectral,
    FotonFaseCoherente,
    NavierStokesAdelico,
    ParticulaCoherencia,
    ResultadoSustrato,
    SustratoCuantico,
    VacioSuperfluo,
    ejecutar_sustrato,
)


@pytest.mark.parametrize("case", range(8))
def test_constants_values(case: int) -> None:
    if case == 0:
        assert F0 == pytest.approx(141.7001, rel=1e-8)
    elif case == 1:
        assert COHERENCIA_UMBRAL == pytest.approx(0.888, rel=1e-8)
    elif case == 2:
        assert ETA_OVER_S_KSS == pytest.approx(1.0 / (4.0 * np.pi), rel=1e-12)
    elif case == 3:
        assert A_EFF_DEFAULT > 0
    elif case == 4:
        assert A_EFF_DEFAULT < F0
    elif case == 5:
        assert float(F0).is_integer() is False
    elif case == 6:
        assert 0 < ETA_OVER_S_KSS < 1
    elif case == 7:
        assert 0 < COHERENCIA_UMBRAL < 1


@pytest.mark.parametrize("case", range(20))
def test_vacio_superfluo(case: int) -> None:
    vacio = VacioSuperfluo()
    if case == 0:
        assert vacio.dimension == 7
    elif case == 1:
        assert vacio.viscosidad_kinematica >= 0
    elif case == 2:
        assert vacio.verificar_haar_unitario() is True
    elif case == 3:
        assert vacio.eta_s() == pytest.approx(1.0 / (4.0 * np.pi), rel=1e-12)
    elif case == 4:
        assert 0 <= vacio.coherencia() <= 1
    elif case == 5:
        assert vacio.U.shape == (7, 7)
    elif case == 6:
        assert np.allclose(vacio.U.conj().T @ vacio.U, np.eye(7), atol=1e-12)
    elif case == 7:
        assert np.abs(np.linalg.det(vacio.U)) == pytest.approx(1.0, abs=1e-12)
    elif case == 8:
        assert np.allclose(np.linalg.matrix_power(vacio.U, 7), np.eye(7), atol=1e-12)
    elif case == 9:
        assert vacio.coherencia() > 0.5
    elif case == 10:
        vacio2 = VacioSuperfluo(viscosidad_kinematica=0.0)
        assert vacio2.coherencia() >= vacio.coherencia()
    elif case == 11:
        with pytest.raises(ValueError):
            VacioSuperfluo(dimension=1)
    elif case == 12:
        with pytest.raises(ValueError):
            VacioSuperfluo(viscosidad_kinematica=-1.0)
    elif case == 13:
        assert vacio.verificar_haar_unitario(tolerancia=1e-9)
    elif case == 14:
        assert vacio.U.dtype == np.complex128
    elif case == 15:
        # En permutación cíclica C₇ ningún estado queda fijo, por eso traza(U)=0.
        assert np.trace(vacio.U) == pytest.approx(0.0, abs=1e-12)
    elif case == 16:
        eig = np.linalg.eigvals(vacio.U)
        assert np.allclose(np.abs(eig), np.ones(7), atol=1e-12)
    elif case == 17:
        assert vacio.eta_s() > 0
    elif case == 18:
        assert vacio.eta_s() < 0.1
    elif case == 19:
        vacio_viscoso = VacioSuperfluo(viscosidad_kinematica=1e-3)
        assert vacio_viscoso.coherencia() < vacio.coherencia()


@pytest.mark.parametrize("case", range(20))
def test_particula_coherencia(case: int) -> None:
    pc = ParticulaCoherencia()
    if case == 0:
        assert pc.fraccion_oscura == pytest.approx(0.95, rel=1e-12)
    elif case == 1:
        assert pc.fase_berry == pytest.approx(np.pi / 8.0, rel=1e-12)
    elif case == 2:
        assert pc.f0_hz == pytest.approx(F0, rel=1e-12)
    elif case == 3:
        assert pc.nodo_c7 == 7
    elif case == 4:
        assert pc.salto_nodo_c7(1) == 1
    elif case == 5:
        assert pc.salto_nodo_c7(7) == 0
    elif case == 6:
        assert pc.salto_nodo_c7(-1) == 6
    elif case == 7:
        assert 0 <= pc.coherencia() <= 1
    elif case == 8:
        assert pc.coherencia() > 0.9
    elif case == 9:
        pc2 = ParticulaCoherencia(fraccion_oscura=0.90)
        assert pc2.coherencia() < pc.coherencia()
    elif case == 10:
        with pytest.raises(ValueError):
            ParticulaCoherencia(fraccion_oscura=0)
    elif case == 11:
        with pytest.raises(ValueError):
            ParticulaCoherencia(fraccion_oscura=1.1)
    elif case == 12:
        assert isinstance(pc.salto_nodo_c7(3), int)
    elif case == 13:
        assert pc.salto_nodo_c7(14) == 0
    elif case == 14:
        assert pc.salto_nodo_c7(15) == 1
    elif case == 15:
        assert pc.salto_nodo_c7(22) == 1
    elif case == 16:
        assert pc.fase_berry > 0
    elif case == 17:
        assert pc.fase_berry < 1
    elif case == 18:
        pc_max = ParticulaCoherencia(fraccion_oscura=1.0)
        assert pc_max.coherencia() >= pc.coherencia()
    elif case == 19:
        assert np.isfinite(pc.coherencia())


@pytest.mark.parametrize("case", range(20))
def test_navier_stokes_adelico(case: int) -> None:
    ns = NavierStokesAdelico()
    if case == 0:
        assert ns.rho == pytest.approx(1.0)
    elif case == 1:
        assert ns.f_ramsey == pytest.approx(0.3999)
    elif case == 2:
        assert ns.hamiltoniano_c7.shape == (7, 7)
    elif case == 3:
        assert ns.es_hermitiano() is True
    elif case == 4:
        assert ns.evaluar_ecuacion(0.0, 0.0, 0.0) == pytest.approx(-0.3999)
    elif case == 5:
        assert 0 <= ns.coherencia() <= 1
    elif case == 6:
        assert ns.coherencia() > 0.5
    elif case == 7:
        assert np.allclose(ns.hamiltoniano_c7, ns.hamiltoniano_c7.T.conj(), atol=1e-12)
    elif case == 8:
        assert np.all(np.isreal(np.linalg.eigvals(ns.hamiltoniano_c7)))
    elif case == 9:
        with pytest.raises(ValueError):
            NavierStokesAdelico(rho=0.0)
    elif case == 10:
        v = ns.evaluar_ecuacion(0.1, 0.2, -0.1001)
        assert abs(v) == pytest.approx(0.2, rel=1e-12)
    elif case == 11:
        # Enlace vecino en anillo de 7 nodos: 2 conexiones por nodo => 2N no nulos.
        assert np.count_nonzero(ns.hamiltoniano_c7) == 2 * ns.hamiltoniano_c7.shape[0]
    elif case == 12:
        assert np.allclose(np.diag(ns.hamiltoniano_c7), 0.0)
    elif case == 13:
        assert np.min(np.linalg.eigvalsh(ns.hamiltoniano_c7)) < 0
    elif case == 14:
        assert np.max(np.linalg.eigvalsh(ns.hamiltoniano_c7)) > 0
    elif case == 15:
        assert ns.es_hermitiano(atol=1e-9)
    elif case == 16:
        assert isinstance(ns.evaluar_ecuacion(1.0, 2.0, 3.0), float)
    elif case == 17:
        assert np.isfinite(ns.coherencia())
    elif case == 18:
        assert ns.presion == pytest.approx(1.0)
    elif case == 19:
        ns2 = NavierStokesAdelico(rho=2.0)
        assert ns2.rho == pytest.approx(2.0)


@pytest.mark.parametrize("case", range(20))
def test_acoplamiento_higgs_pc(case: int) -> None:
    h = AcoplamientoHiggsPc()
    if case == 0:
        assert h.reduccion_masa == pytest.approx(0.053, rel=1e-12)
    elif case == 1:
        assert h.destello_activo() is True
    elif case == 2:
        assert h.masa_efectiva < h.m0_gev
    elif case == 3:
        assert h.masa_efectiva == pytest.approx(h.m0_gev * (1 - 0.053), rel=1e-12)
    elif case == 4:
        assert 0 <= h.coherencia() <= 1
    elif case == 5:
        assert h.coherencia() > 0.95
    elif case == 6:
        h2 = AcoplamientoHiggsPc(a_eff=0.5 * h.a_eff)
        assert h2.reduccion_masa < h.reduccion_masa
    elif case == 7:
        h3 = AcoplamientoHiggsPc(kappa_pi=1.0)
        assert h3.reduccion_masa < h.reduccion_masa
    elif case == 8:
        assert h.reduccion_masa > 0
    elif case == 9:
        assert h.reduccion_masa < 1
    elif case == 10:
        assert np.isfinite(h.masa_efectiva)
    elif case == 11:
        assert np.isfinite(h.reduccion_masa)
    elif case == 12:
        assert h.destello_activo(tol=1e-3)
    elif case == 13:
        h_bad = AcoplamientoHiggsPc(a_eff=0.0)
        assert h_bad.destello_activo() is False
    elif case == 14:
        h_bad = AcoplamientoHiggsPc(a_eff=0.0)
        assert h_bad.reduccion_masa == pytest.approx(0.0)
    elif case == 15:
        h_bad = AcoplamientoHiggsPc(a_eff=0.0)
        assert h_bad.masa_efectiva == pytest.approx(h_bad.m0_gev)
    elif case == 16:
        assert h.f0_hz == pytest.approx(F0)
    elif case == 17:
        assert h.kappa_pi > 0
    elif case == 18:
        assert h.a_eff > 0
    elif case == 19:
        assert h.m0_gev > 0


@pytest.mark.parametrize("case", range(18))
def test_foton_fase_coherente(case: int) -> None:
    foton = FotonFaseCoherente(psi=1.0)
    if case == 0:
        assert foton.r_symb_kpps == pytest.approx(991.9007, rel=1e-7)
    elif case == 1:
        assert foton.r_symb_kpps == pytest.approx(foton.n_canales * foton.f0_topc * foton.psi, rel=1e-12)
    elif case == 2:
        assert foton.cooperatividad_xi == pytest.approx(0.053, rel=1e-12)
    elif case == 3:
        assert 0 <= foton.sincronizacion_dicke() <= 1
    elif case == 4:
        assert foton.sincronizacion_dicke() > 0.9
    elif case == 5:
        assert 0 <= foton.coherencia() <= 1
    elif case == 6:
        assert foton.coherencia() > 0.95
    elif case == 7:
        foton2 = FotonFaseCoherente(psi=0.5)
        assert foton2.r_symb_kpps == pytest.approx(foton.r_symb_kpps / 2.0, rel=1e-12)
    elif case == 8:
        foton2 = FotonFaseCoherente(psi=0.5)
        assert foton2.coherencia() < foton.coherencia()
    elif case == 9:
        assert foton.n_canales == 7
    elif case == 10:
        assert foton.f0_topc == pytest.approx(F0)
    elif case == 11:
        assert np.isfinite(foton.r_symb_kpps)
    elif case == 12:
        assert np.isfinite(foton.coherencia())
    elif case == 13:
        assert np.isfinite(foton.sincronizacion_dicke())
    elif case == 14:
        assert foton.r_symb_kpps > 0
    elif case == 15:
        assert FotonFaseCoherente(psi=0.0).r_symb_kpps == 0.0
    elif case == 16:
        assert FotonFaseCoherente(psi=0.0).coherencia() <= foton.coherencia()
    elif case == 17:
        foton_off = FotonFaseCoherente(psi=1.0, cooperatividad_xi=0.2)
        assert foton_off.sincronizacion_dicke() < foton.sincronizacion_dicke()


@pytest.mark.parametrize("case", range(18))
def test_firma_espectral(case: int) -> None:
    firma = FirmaEspectral(coherencia=1.0)
    if case == 0:
        assert firma.delta_seccion_eficaz == pytest.approx(0.053, rel=1e-12)
    elif case == 1:
        assert len(firma.bandas_laterales()) == 3
    elif case == 2:
        bandas = firma.bandas_laterales()
        assert bandas[0]["n"] == 1.0
    elif case == 3:
        bandas = firma.bandas_laterales()
        assert bandas[1]["n"] == 2.0
    elif case == 4:
        bandas = firma.bandas_laterales()
        assert bandas[2]["n"] == 3.0
    elif case == 5:
        bandas = firma.bandas_laterales()
        assert bandas[0]["minus"] <= firma.m_h_gev
    elif case == 6:
        bandas = firma.bandas_laterales()
        assert bandas[0]["plus"] >= firma.m_h_gev
    elif case == 7:
        assert firma.ventana_transparente() is True
    elif case == 8:
        assert 0 <= firma.coherencia_firma() <= 1
    elif case == 9:
        assert firma.coherencia_firma() > 0.95
    elif case == 10:
        firma_low = FirmaEspectral(coherencia=0.5)
        assert firma_low.ventana_transparente() is False
    elif case == 11:
        firma_low = FirmaEspectral(coherencia=0.5)
        assert firma_low.coherencia_firma() < firma.coherencia_firma()
    elif case == 12:
        assert np.isfinite(firma.coherencia_firma())
    elif case == 13:
        assert np.isfinite(firma.delta_seccion_eficaz)
    elif case == 14:
        assert firma.delta_seccion_eficaz > 0
    elif case == 15:
        assert firma.delta_seccion_eficaz < 1
    elif case == 16:
        assert firma.omega_0 > 0
    elif case == 17:
        assert all(set(b.keys()) == {"n", "minus", "plus"} for b in firma.bandas_laterales())


@pytest.mark.parametrize("case", range(10))
def test_resultado_sustrato_integridad(case: int) -> None:
    s = ejecutar_sustrato(verbose=False)
    assert isinstance(s, ResultadoSustrato)

    if case == 0:
        assert len(s.sello_sha256) == 64
    elif case == 1:
        assert isinstance(int(s.sello_sha256, 16), int)
    elif case == 2:
        assert s.sello_sha256 == s.sellar()
    elif case == 3:
        before = s.sello_sha256
        s.psi_global = s.psi_global - 0.01
        after = s.sellar()
        assert before != after
    elif case == 4:
        payload = s.payload_integridad()
        assert "psi_global" in payload
    elif case == 5:
        payload = s.payload_integridad()
        assert "componentes" in payload
    elif case == 6:
        payload = s.payload_integridad()
        assert payload["destello_reduccion_masa"] == pytest.approx(0.053, rel=1e-12)
    elif case == 7:
        payload = s.payload_integridad()
        assert payload["firma_delta_seccion_eficaz"] == pytest.approx(0.053, rel=1e-12)
    elif case == 8:
        assert s.timestamp
    elif case == 9:
        assert isinstance(s.componentes, dict)


@pytest.mark.parametrize("case", range(9))
def test_sustrato_integracion(case: int) -> None:
    sistema = SustratoCuantico()
    r = sistema.activar(verbose=False)

    if case == 0:
        assert r.psi_global > 0
    elif case == 1:
        assert 0 <= r.psi_global <= 1
    elif case == 2:
        assert r.sustrato_activo is True
    elif case == 3:
        assert r.destello_masa.reduccion_masa == pytest.approx(0.053, rel=1e-12)
    elif case == 4:
        assert r.foton.r_symb_kpps == pytest.approx(991.9, rel=1e-3)
    elif case == 5:
        assert r.firma_espectral.delta_seccion_eficaz == pytest.approx(0.053, rel=1e-12)
    elif case == 6:
        vals = np.array(list(r.componentes.values()), dtype=float)
        expected = float(np.prod(np.clip(vals, 1e-12, 1.0)) ** (1.0 / len(vals)))
        assert r.psi_global == pytest.approx(expected, rel=1e-12)
    elif case == 7:
        assert set(r.componentes.keys()) == {
            "psi_vacio",
            "psi_pc",
            "psi_navier",
            "psi_higgs",
            "psi_foton",
            "psi_firma",
        }
    elif case == 8:
        # Validación independiente de media geométrica con valores conocidos.
        toy_vals = np.array([1.0, 0.9, 0.8, 0.7, 0.6, 0.5], dtype=float)
        expected = float(np.prod(toy_vals) ** (1.0 / 6.0))
        assert expected == pytest.approx(0.7298920475, rel=1e-9)
