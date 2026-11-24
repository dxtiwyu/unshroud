"""Runs the exception tests of a test DLL natively (bench/exc): prints {test: [results]} as JSON.
usage: python -I exc_native.py <dll>     (started by exc_check.py in a process of its own)"""
import ctypes, json, sys
M = (1 << 64) - 1
TESTS = [("t01_av_write", [(0, 5), (1, 5), (2, 9)]), ("t02_av_read_filter", [(0, 1), (8, 2), (0x1238, 3)]), ("t03_search_outer", [(0, 1), (1, 2), (3, 4)]),
         ("t04_continue", [(7, 1), (8, 1)]), ("t05_raise_args", [(1, 2), (0x1111, 0x2222)]),
         ("t06_divide", [(100, 7), (5, 0), (1 << 63, M), (7, M)]), ("t07_finally", [(0, 1), (1, 2), (2, 3), (3, 4)]),
         ("t08_nested", [(0, 0), (1, 0), (2, 0), (3, 0)]), ("t09_int3_skipped", [(0, 0), (1, 0)]), ("t10_ud2_skipped", [(0, 0), (1, 0), (2, 0), (3, 0)]),
         ("t11_veh_continue_raise", [(0, 0), (1, 0)]), ("t12_cpp_catch", [(0, 1), (1, 1), (2, 1), (3, 1), (4, 1)]),
         ("t13_cpp_nested_rethrow", [(0, 0), (1, 0), (2, 0), (3, 0)]), ("t14_cpp_deep", [(0, 0), (1, 0), (2, 0), (3, 0)]),
         ("t15_cpp_values", [(0, 5), (1, 5), (0x1234567, 0x89), (M, 3)]), ("t16_longjmp", [(0, 3), (1, 3), (0xfe, 1), (0xff, 1)]),
         ("t17_null_call", [(0, 1), (1, 1)]), ("t18_alloca_frame", [(0, 1), (1, 1), (0x40, 2), (0x41, 2)]), ("t21_privileged", [(0, 1), (1, 1)])]
ONLY_UNSHROUD = [("t19_unhandled_filter", [(1, 1), (0x777, 0)]), ("t20_top_filter", [(0, 0), (1, 0)])]
if __name__ == "__main__":
    dll = ctypes.CDLL(sys.argv[1])
    out = {}
    for name, inputs in TESTS:
        f = getattr(dll, name); f.restype = ctypes.c_uint64; f.argtypes = [ctypes.c_uint64, ctypes.c_uint64]
        out[name] = [f(a, b) for a, b in inputs]
        print("native %s done" % name, file=sys.stderr, flush=True)
    print(json.dumps(out))
