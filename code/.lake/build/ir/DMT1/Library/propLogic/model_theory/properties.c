// Lean compiler output
// Module: DMT1.Library.propLogic.model_theory.properties
// Imports: Init DMT1.Library.propLogic.model_theory.truthTable
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
LEAN_EXPORT uint8_t l_DMT1_Library_propLogic_model__theory_is__valid(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_Library_propLogic_model__theory_is__unsat(lean_object*);
uint8_t l_DMT1_Library_propLogic_utilities_reduce__or(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__sat___boxed(lean_object*);
lean_object* l_DMT1_Library_propLogic_model__theory_truth__table_truthTableOutputs(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_Library_propLogic_model__theory_is__sat(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__unsat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__valid___boxed(lean_object*);
lean_object* l_DMT1_Library_propLogic_semantics_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__model(lean_object*, lean_object*);
uint8_t l_DMT1_Library_propLogic_utilities_reduce__and(lean_object*);
LEAN_EXPORT uint8_t l_DMT1_Library_propLogic_model__theory_is__sat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_DMT1_Library_propLogic_model__theory_truth__table_truthTableOutputs(x_1);
x_3 = l_DMT1_Library_propLogic_utilities_reduce__or(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__sat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_DMT1_Library_propLogic_model__theory_is__sat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_DMT1_Library_propLogic_model__theory_is__valid(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_DMT1_Library_propLogic_model__theory_truth__table_truthTableOutputs(x_1);
x_3 = l_DMT1_Library_propLogic_utilities_reduce__and(x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__valid___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_DMT1_Library_propLogic_model__theory_is__valid(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_DMT1_Library_propLogic_model__theory_is__unsat(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_DMT1_Library_propLogic_model__theory_is__sat(x_1);
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
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__unsat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_DMT1_Library_propLogic_model__theory_is__unsat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_DMT1_Library_propLogic_model__theory_is__model(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_DMT1_Library_propLogic_semantics_eval(x_2, x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_model__theory_truth__table(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DMT1_Library_propLogic_model__theory_properties(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_model__theory_truth__table(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
