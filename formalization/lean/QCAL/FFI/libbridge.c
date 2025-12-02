#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <Python.h>

/*
 * FFI bridge: ejecuta el verificador universal en Python y devuelve true/false.
 * Compílalo con:  clang -shared -fPIC -I/usr/include/python3.x -o libbridge.so libbridge.c
 */

bool qcal_verify(const char* jsonld, const char* proof) {
    bool ok = false;
    Py_Initialize();
    PyObject *pName = PyUnicode_DecodeFSDefault("tools.universal_kernel");
    PyObject *pModule = PyImport_Import(pName);
    Py_DECREF(pName);
    if (pModule) {
        PyObject *pFunc = PyObject_GetAttrString(pModule, "verify_universal_api");
        if (pFunc && PyCallable_Check(pFunc)) {
            PyObject *args = Py_BuildValue("(ss)", jsonld, proof);
            PyObject *result = PyObject_CallObject(pFunc, args);
            if (result) {
                ok = PyObject_IsTrue(result);
                Py_DECREF(result);
            }
            Py_XDECREF(args);
        }
        Py_XDECREF(pFunc);
        Py_DECREF(pModule);
    }
    Py_Finalize();
    return ok;
}
