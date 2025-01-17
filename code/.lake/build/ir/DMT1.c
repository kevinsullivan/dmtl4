// Lean compiler output
// Module: DMT1
// Imports: Init DMT1.Library.propLogic.syntax DMT1.Library.propLogic.semantics DMT1.Library.propLogic.interpretation DMT1.Library.propLogic.domain DMT1.Library.propLogic.axioms DMT1.Library.propLogic.identities DMT1.Library.propLogic.utilities DMT1.Lectures.L02_propLogic.formal.syntax DMT1.Lectures.L02_propLogic.formal.semantics DMT1.Lectures.L02_propLogic.formal.interpretation DMT1.Lectures.L02_propLogic.formal.domain DMT1.Lectures.L02_propLogic.formal.axioms DMT1.Lectures.L02_propLogic.formal.identities DMT1.Lectures.L02_propLogic.formal.utilities
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
lean_object* initialize_DMT1_Library_propLogic_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_semantics(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_interpretation(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_domain(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_axioms(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_identities(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Library_propLogic_utilities(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_syntax(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_semantics(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_interpretation(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_domain(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_axioms(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_identities(uint8_t builtin, lean_object*);
lean_object* initialize_DMT1_Lectures_L02__propLogic_formal_utilities(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DMT1(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_syntax(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_semantics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_interpretation(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_domain(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_axioms(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_identities(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DMT1_Library_propLogic_utilities(builtin, lean_io_mk_world());
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
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
