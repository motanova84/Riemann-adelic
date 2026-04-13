/**
 * FFI Bridge: Python-Lean C Extension
 * ====================================
 * 
 * This C library provides the bridge layer between Python and Lean,
 * enabling Lean code to call Python functions through the Python C API.
 * 
 * Architecture:
 *   Lean code → C extern functions → Python C API → Python functions
 * 
 * Compilation:
 *   gcc -shared -fPIC -I/usr/include/python3.11 -o libffi_bridge.so ffi_bridge.c -lpython3.11
 *   
 *   Or use the provided Makefile:
 *   make
 * 
 * Author: José Manuel Mota Burruezo Ψ ✧ ∞³
 * Institution: Instituto de Conciencia Cuántica (ICQ)
 * ORCID: 0009-0002-1923-0773
 * 
 * QCAL ∞³ Active · 141.7001 Hz · Ψ = I × A_eff² × C^∞
 * DOI: 10.5281/zenodo.17379721
 */

#include <Python.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>

/* Global state */
static int python_initialized = 0;
static PyObject *ffi_module = NULL;

/**
 * Initialize Python interpreter and load the FFI wrapper module.
 * This should be called once before any FFI functions.
 */
static void ensure_python_initialized() {
    if (python_initialized) {
        return;
    }
    
    /* Initialize Python */
    Py_Initialize();
    
    /* Add current directory and parent to Python path */
    PyRun_SimpleString("import sys");
    PyRun_SimpleString("sys.path.insert(0, '.')");
    PyRun_SimpleString("sys.path.insert(0, '..')");
    PyRun_SimpleString("sys.path.insert(0, '../..')");
    
    /* Import the FFI wrapper module */
    PyObject *pName = PyUnicode_DecodeFSDefault("ffi.python_ffi_wrapper");
    if (pName == NULL) {
        /* Try alternative import path */
        PyErr_Clear();
        pName = PyUnicode_DecodeFSDefault("python_ffi_wrapper");
    }
    
    if (pName != NULL) {
        ffi_module = PyImport_Import(pName);
        Py_DECREF(pName);
        
        if (ffi_module == NULL) {
            PyErr_Print();
            fprintf(stderr, "Failed to load FFI module\n");
        }
    }
    
    python_initialized = 1;
}

/**
 * Cleanup Python interpreter.
 * Call this at program exit.
 */
void ffi_cleanup() {
    if (ffi_module != NULL) {
        Py_DECREF(ffi_module);
        ffi_module = NULL;
    }
    
    if (python_initialized) {
        Py_Finalize();
        python_initialized = 0;
    }
}

/**
 * Get a QCAL constant by name.
 * 
 * @param name Constant name (e.g., "F0", "C_PRIMARY")
 * @return Constant value, or 0.0 on error
 */
double ffi_get_constant(const char *name) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return 0.0;
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_get_constant");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return 0.0;
    }
    
    PyObject *pArgs = Py_BuildValue("(s)", name);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return 0.0;
    }
    
    double result = PyFloat_AsDouble(pValue);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Validate QCAL constants coherence.
 * 
 * @return true if coherence checks pass, false otherwise
 */
bool ffi_validate_coherence() {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return false;
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_validate_coherence");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return false;
    }
    
    PyObject *pValue = PyObject_CallObject(pFunc, NULL);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return false;
    }
    
    bool result = PyObject_IsTrue(pValue);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Compute Ψ = I × A_eff² × C^∞
 * 
 * @param intensity Information intensity I
 * @param area_eff Effective area A_eff
 * @param coherence Coherence factor C
 * @return Ψ value
 */
double ffi_compute_psi(double intensity, double area_eff, double coherence) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return 0.0;
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_compute_psi");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return 0.0;
    }
    
    PyObject *pArgs = Py_BuildValue("(ddd)", intensity, area_eff, coherence);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return 0.0;
    }
    
    double result = PyFloat_AsDouble(pValue);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Run comprehensive QCAL validation.
 * 
 * @param config_json JSON configuration string
 * @return JSON result string (caller must free)
 */
char* ffi_run_validation(const char *config_json) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return strdup("{\"error\": \"FFI module not loaded\", \"all_checks_passed\": false}");
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_run_validation");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return strdup("{\"error\": \"Function not found\", \"all_checks_passed\": false}");
    }
    
    PyObject *pArgs = Py_BuildValue("(s)", config_json);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return strdup("{\"error\": \"Call failed\", \"all_checks_passed\": false}");
    }
    
    const char *result_str = PyUnicode_AsUTF8(pValue);
    char *result = strdup(result_str);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Compute the n-th Riemann zeta zero.
 * 
 * @param n Zero index (1-based)
 * @return JSON result string (caller must free)
 */
char* ffi_compute_riemann_zero(int n) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return strdup("{\"error\": \"FFI module not loaded\"}");
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_compute_riemann_zero");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return strdup("{\"error\": \"Function not found\"}");
    }
    
    PyObject *pArgs = Py_BuildValue("(i)", n);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return strdup("{\"error\": \"Call failed\"}");
    }
    
    const char *result_str = PyUnicode_AsUTF8(pValue);
    char *result = strdup(result_str);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Evaluate the Riemann zeta function.
 * 
 * @param s_real Real part of s
 * @param s_imag Imaginary part of s
 * @return JSON result string (caller must free)
 */
char* ffi_evaluate_zeta(double s_real, double s_imag) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return strdup("{\"error\": \"FFI module not loaded\"}");
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_evaluate_zeta");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return strdup("{\"error\": \"Function not found\"}");
    }
    
    PyObject *pArgs = Py_BuildValue("(dd)", s_real, s_imag);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return strdup("{\"error\": \"Call failed\"}");
    }
    
    const char *result_str = PyUnicode_AsUTF8(pValue);
    char *result = strdup(result_str);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Check if a point is a zero of the zeta function.
 * 
 * @param s_real Real part of s
 * @param s_imag Imaginary part of s
 * @param tolerance Tolerance for zero check
 * @return true if |ζ(s)| < tolerance
 */
bool ffi_check_critical_line(double s_real, double s_imag, double tolerance) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return false;
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_check_critical_line");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return false;
    }
    
    PyObject *pArgs = Py_BuildValue("(ddd)", s_real, s_imag, tolerance);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return false;
    }
    
    bool result = PyObject_IsTrue(pValue);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Generate a mathematical certificate.
 * 
 * @param output_path Path where to save the certificate
 * @return true if successful
 */
bool ffi_generate_certificate(const char *output_path) {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return false;
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_generate_certificate");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return false;
    }
    
    PyObject *pArgs = Py_BuildValue("(s)", output_path);
    PyObject *pValue = PyObject_CallObject(pFunc, pArgs);
    Py_DECREF(pArgs);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return false;
    }
    
    bool result = PyObject_IsTrue(pValue);
    Py_DECREF(pValue);
    
    return result;
}

/**
 * Get API information.
 * 
 * @return JSON string with API docs (caller must free)
 */
char* ffi_get_api_info() {
    ensure_python_initialized();
    
    if (ffi_module == NULL) {
        return strdup("{\"error\": \"FFI module not loaded\"}");
    }
    
    PyObject *pFunc = PyObject_GetAttrString(ffi_module, "ffi_get_api_info");
    if (pFunc == NULL || !PyCallable_Check(pFunc)) {
        PyErr_Print();
        Py_XDECREF(pFunc);
        return strdup("{\"error\": \"Function not found\"}");
    }
    
    PyObject *pValue = PyObject_CallObject(pFunc, NULL);
    Py_DECREF(pFunc);
    
    if (pValue == NULL) {
        PyErr_Print();
        return strdup("{\"error\": \"Call failed\"}");
    }
    
    const char *result_str = PyUnicode_AsUTF8(pValue);
    char *result = strdup(result_str);
    Py_DECREF(pValue);
    
    return result;
}
