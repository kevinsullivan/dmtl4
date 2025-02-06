// Lean compiler output
// Module: DMT1.Library.propLogicWithArith.semantics
// Imports: Init DMT1.Library.propLogicWithArith.syntax DMT1.Library.propLogicWithArith.domain DMT1.Library.natArithmetic.semantics
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
LEAN_EXPORT uint8_t l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg(uint8_t);
uint8_t l_DMT1_propLogicwithArith_domain_iff(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalUnOp(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_propLogicwithArith_semantics_evalBinOp(uint8_t, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalBinOp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalUnOp___boxed(lean_object*);
uint8_t l_DMT1_natArithmetic_semantics_evalRelExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalPLAExpr(lean_object*, lean_object*, lean_object*);
uint8_t l_DMT1_propLogicwithArith_domain_imp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg___boxed(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
uint8_t x_2; 
x_2 = 1;
return x_2;
}
else
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalUnOp(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalUnOp___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_DMT1_propLogicwithArith_semantics_evalUnOp(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_DMT1_propLogicwithArith_semantics_evalBinOp(uint8_t x_1, uint8_t x_2, uint8_t x_3) {
_start:
{
switch (x_1) {
case 0:
{
if (x_2 == 0)
{
uint8_t x_4; 
x_4 = 0;
return x_4;
}
else
{
return x_3;
}
}
case 1:
{
if (x_2 == 0)
{
return x_3;
}
else
{
uint8_t x_5; 
x_5 = 1;
return x_5;
}
}
case 2:
{
uint8_t x_6; 
x_6 = l_DMT1_propLogicwithArith_domain_imp(x_2, x_3);
return x_6;
}
default: 
{
uint8_t x_7; 
x_7 = l_DMT1_propLogicwithArith_domain_iff(x_2, x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_DMT1_propLogicwithArith_semantics_evalBinOp(x_4, x_5, x_6);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_DMT1_propLogicwithArith_semantics_evalPLAExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint8_t x_4; lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
case 1:
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
case 2:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_DMT1_propLogicwithArith_semantics_evalPLAExpr(x_8, x_2, x_3);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
x_11 = l_DMT1_propLogicwithArith_semantics_evalUnOp___rarg(x_10);
x_12 = lean_box(x_11);
return x_12;
}
case 3:
{
uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_dec(x_1);
lean_inc(x_3);
lean_inc(x_2);
x_16 = l_DMT1_propLogicwithArith_semantics_evalPLAExpr(x_14, x_2, x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
x_18 = l_DMT1_propLogicwithArith_semantics_evalPLAExpr(x_15, x_2, x_3);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = l_DMT1_propLogicwithArith_semantics_evalBinOp(x_13, x_17, x_19);
x_21 = lean_box(x_20);
return x_21;
}
default: 
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_2);
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_DMT1_natArithmetic_semantics_evalRelExpr(x_22, x_3);
x_24 = lean_box(x_23);
return x_24;
}
}
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogicWithArith_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogicWithArith_domain(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_natArithmetic_semantics(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DMT1_Library_propLogicWithArith_semantics(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogicWithArith_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogicWithArith_domain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_natArithmetic_semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
