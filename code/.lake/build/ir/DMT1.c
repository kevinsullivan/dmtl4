// Lean compiler output
// Module: DMT1
// Imports: Init DMT1.Lectures.L02_propLogic.formal.syntax DMT1.Lectures.L02_propLogic.formal.semantics DMT1.Lectures.L02_propLogic.formal.interpretation DMT1.Lectures.L02_propLogic.formal.domain DMT1.Lectures.L02_propLogic.formal.axioms DMT1.Lectures.L02_propLogic.formal.identities DMT1.Lectures.L02_propLogic.formal.utilities DMT1.MyWork.hw3.syntax DMT1.MyWork.hw3.domain DMT1.MyWork.hw3.semantics DMT1.MyWork.hw3.axioms DMT1.MyWork.hw3.interpretation DMT1.MyWork.hw3.utilities DMT1.Lectures.L03_modelTheory.models DMT1.Lectures.L03_modelTheory.counterexamples DMT1.Lectures.L03_modelTheory.truthTable DMT1.Lectures.L03_modelTheory.properties DMT1.Lectures.L03_modelTheory.validity DMT1.Lectures.L04_nat_arithmetic.syntax DMT1.Lectures.L04_nat_arithmetic.semantics DMT1.Lectures.L04_nat_arithmetic.domain
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
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_semantics(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_interpretation(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_domain(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_axioms(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_identities(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_utilities(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_MyWork_hw3_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_MyWork_hw3_domain(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_MyWork_hw3_semantics(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_MyWork_hw3_axioms(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_MyWork_hw3_interpretation(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_MyWork_hw3_utilities(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L03__modelTheory_models(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L03__modelTheory_counterexamples(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L03__modelTheory_truthTable(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L03__modelTheory_properties(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L03__modelTheory_validity(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L04__nat__arithmetic_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L04__nat__arithmetic_semantics(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L04__nat__arithmetic_domain(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DMT1(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_interpretation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_domain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_axioms(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_identities(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L02__propLogic_formal_utilities(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_MyWork_hw3_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_MyWork_hw3_domain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_MyWork_hw3_semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_MyWork_hw3_axioms(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_MyWork_hw3_interpretation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_MyWork_hw3_utilities(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L03__modelTheory_models(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L03__modelTheory_counterexamples(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L03__modelTheory_truthTable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L03__modelTheory_properties(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L03__modelTheory_validity(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L04__nat__arithmetic_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L04__nat__arithmetic_semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Lectures_L04__nat__arithmetic_domain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
