// Lean compiler output
// Module: DMT1.Library.natArithmetic.domain
// Imports: Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_ge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_pred(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_id___boxed(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_isEven(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_fac___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_inc___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_gt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_mul___boxed(lean_object*, lean_object*);
uint8_t l_instDecidableNot___rarg(uint8_t);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_dec___boxed(lean_object*);
static uint8_t l_DMT1_natArithmetic_domain_gt___closed__2;
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_pred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_isEven___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_inc(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_id(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_exp___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_exp(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_lt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_fac(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_dec(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_le___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_gt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_isOdd(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_isEq0(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_isOdd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_eq___boxed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_ge___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_isEq0___boxed(lean_object*);
static uint8_t l_DMT1_natArithmetic_domain_gt___closed__1;
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_id(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_id___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_domain_id(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_inc(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_inc___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_domain_inc(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_pred(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(0u);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_pred___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_domain_pred(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_dec(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_domain_pred(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_dec___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_domain_dec(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_fac(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
x_6 = lean_nat_add(x_5, x_4);
x_7 = l_DMT1_natArithmetic_domain_fac(x_5);
lean_dec(x_5);
x_8 = lean_nat_mul(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_fac___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_domain_fac(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_add(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_DMT1_natArithmetic_domain_add(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_add(x_7, x_5);
lean_dec(x_7);
return x_8;
}
else
{
lean_inc(x_1);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_add___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_DMT1_natArithmetic_domain_add(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_sub(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_1;
}
}
else
{
lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_unsigned_to_nat(0u);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_mul(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_DMT1_natArithmetic_domain_mul(x_1, x_6);
lean_dec(x_6);
x_8 = l_DMT1_natArithmetic_domain_add(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(0u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_mul___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_DMT1_natArithmetic_domain_mul(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_exp(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_2, x_5);
x_7 = l_DMT1_natArithmetic_domain_exp(x_1, x_6);
lean_dec(x_6);
x_8 = lean_nat_mul(x_1, x_7);
lean_dec(x_7);
return x_8;
}
else
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(1u);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_exp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_DMT1_natArithmetic_domain_exp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_isEq0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_isEq0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_DMT1_natArithmetic_domain_isEq0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_isEven(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_sub(x_1, x_4);
lean_dec(x_1);
x_6 = lean_nat_dec_eq(x_5, x_2);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_nat_sub(x_5, x_4);
lean_dec(x_5);
x_1 = x_7;
goto _start;
}
else
{
uint8_t x_9; 
lean_dec(x_5);
x_9 = 0;
return x_9;
}
}
else
{
uint8_t x_10; 
lean_dec(x_1);
x_10 = 1;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_isEven___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_DMT1_natArithmetic_domain_isEven(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_isOdd(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_DMT1_natArithmetic_domain_isEven(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_isOdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_DMT1_natArithmetic_domain_isOdd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_eq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = lean_nat_dec_eq(x_2, x_3);
lean_dec(x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_eq___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_DMT1_natArithmetic_domain_eq(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_le(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_sub(x_1, x_5);
lean_dec(x_1);
x_7 = lean_nat_dec_eq(x_2, x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_nat_sub(x_2, x_5);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_8;
goto _start;
}
else
{
uint8_t x_10; 
lean_dec(x_6);
lean_dec(x_2);
x_10 = 0;
return x_10;
}
}
else
{
uint8_t x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = 1;
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_le___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_DMT1_natArithmetic_domain_le(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static uint8_t _init_l_DMT1_natArithmetic_domain_gt___closed__1() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 0;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
static uint8_t _init_l_DMT1_natArithmetic_domain_gt___closed__2() {
_start:
{
uint8_t x_1; uint8_t x_2; 
x_1 = 1;
x_2 = l_instDecidableNot___rarg(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_gt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_DMT1_natArithmetic_domain_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_DMT1_natArithmetic_domain_gt___closed__1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_DMT1_natArithmetic_domain_gt___closed__2;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_gt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_DMT1_natArithmetic_domain_gt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_DMT1_natArithmetic_domain_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
lean_dec(x_2);
lean_dec(x_1);
x_4 = 0;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = l_DMT1_natArithmetic_domain_eq(x_1, x_2);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = 1;
return x_6;
}
else
{
uint8_t x_7; 
x_7 = 0;
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_DMT1_natArithmetic_domain_lt(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_domain_ge(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
lean_inc(x_2);
lean_inc(x_1);
x_3 = l_DMT1_natArithmetic_domain_gt(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = l_DMT1_natArithmetic_domain_eq(x_1, x_2);
return x_4;
}
else
{
uint8_t x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = 1;
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_domain_ge___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_DMT1_natArithmetic_domain_ge(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DMT1_Library_natArithmetic_domain(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_DMT1_natArithmetic_domain_gt___closed__1 = _init_l_DMT1_natArithmetic_domain_gt___closed__1();
l_DMT1_natArithmetic_domain_gt___closed__2 = _init_l_DMT1_natArithmetic_domain_gt___closed__2();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
