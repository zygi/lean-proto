#include <stdint.h>

uint32_t proto_lean_transmute_double_to_uint32(double a) { float r = (float) a; return *(uint32_t*)(&r); }

uint32_t arith_right_shift_32(uint32_t a, uint32_t b) { 
    int32_t a_int = *(int32_t*)(&a);
    int32_t b_int = *(int32_t*)(&b);
    int32_t res = (a_int >> b_int);
    return *(int32_t*)(&res);
 }

uint64_t arith_right_shift_64(uint64_t a, uint64_t b) { 
    int64_t a_int = *(int64_t*)(&a);
    int64_t b_int = *(int64_t*)(&b);
    int64_t res = (a_int >> b_int);
    return *(int64_t*)(&res);
 }