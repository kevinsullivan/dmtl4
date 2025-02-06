// Lean compiler output
// Module: DMT1.Library.natArithmetic.semantics
// Imports: Init DMT1.Library.natArithmetic.syntax DMT1.Library.natArithmetic.domain
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
uint8_t l_DMT1_natArithmetic_domain_ge(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalUnOp(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalBinOp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalLit(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalRelOp___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_DMT1_natArithmetic_domain_add(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_eval(lean_object*, lean_object*);
uint8_t l_DMT1_natArithmetic_domain_le(lean_object*, lean_object*);
lean_object* l_DMT1_natArithmetic_domain_sub(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_semantics_evalRelOp(uint8_t, lean_object*, lean_object*);
lean_object* l_DMT1_natArithmetic_domain_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalLit___boxed(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_semantics_evalRelExpr(lean_object*, lean_object*);
uint8_t l_DMT1_natArithmetic_domain_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalRelExpr___boxed(lean_object*, lean_object*);
uint8_t l_DMT1_natArithmetic_domain_eq(lean_object*, lean_object*);
lean_object* l_DMT1_natArithmetic_domain_fac(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t l_DMT1_natArithmetic_domain_gt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalUnOp___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pred(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalBinOp(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalUnOp(uint8_t x_1, lean_object* x_2) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_add(x_2, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = lean_nat_pred(x_2);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_mul(x_2, x_6);
return x_7;
}
case 3:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_div(x_2, x_8);
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = l_DMT1_natArithmetic_domain_fac(x_2);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalUnOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_DMT1_natArithmetic_semantics_evalUnOp(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalBinOp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_4; 
x_4 = l_DMT1_natArithmetic_domain_add(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
case 1:
{
lean_object* x_5; 
x_5 = l_DMT1_natArithmetic_domain_sub(x_2, x_3);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = l_DMT1_natArithmetic_domain_mul(x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_DMT1_natArithmetic_semantics_evalBinOp(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_semantics_evalRelOp(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (x_1) {
case 0:
{
uint8_t x_4; 
x_4 = l_DMT1_natArithmetic_domain_eq(x_2, x_3);
return x_4;
}
case 1:
{
uint8_t x_5; 
x_5 = l_DMT1_natArithmetic_domain_le(x_2, x_3);
return x_5;
}
case 2:
{
uint8_t x_6; 
x_6 = l_DMT1_natArithmetic_domain_lt(x_2, x_3);
return x_6;
}
case 3:
{
uint8_t x_7; 
x_7 = l_DMT1_natArithmetic_domain_ge(x_2, x_3);
return x_7;
}
default: 
{
uint8_t x_8; 
x_8 = l_DMT1_natArithmetic_domain_gt(x_2, x_3);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalRelOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_DMT1_natArithmetic_semantics_evalRelOp(x_4, x_2, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalLit(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_natArithmetic_semantics_evalLit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
case 2:
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_DMT1_natArithmetic_semantics_eval(x_7, x_2);
x_9 = l_DMT1_natArithmetic_semantics_evalUnOp(x_6, x_8);
lean_dec(x_8);
return x_9;
}
default: 
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_2);
x_13 = l_DMT1_natArithmetic_semantics_eval(x_11, x_2);
x_14 = l_DMT1_natArithmetic_semantics_eval(x_12, x_2);
x_15 = l_DMT1_natArithmetic_semantics_evalBinOp(x_10, x_13, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT uint8_t l_DMT1_natArithmetic_semantics_evalRelExpr(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
lean_inc(x_2);
x_6 = l_DMT1_natArithmetic_semantics_eval(x_4, x_2);
x_7 = l_DMT1_natArithmetic_semantics_eval(x_5, x_2);
x_8 = l_DMT1_natArithmetic_semantics_evalRelOp(x_3, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_DMT1_natArithmetic_semantics_evalRelExpr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_DMT1_natArithmetic_semantics_evalRelExpr(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_natArithmetic_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_natArithmetic_domain(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DMT1_Library_natArithmetic_semantics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_natArithmetic_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_natArithmetic_domain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
