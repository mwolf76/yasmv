/* Controlled assertion adapter. Deliberately checked on every inclusion. */
#ifdef NDEBUG
#error "llvm2smv requires assertions enabled (NDEBUG is unsupported)"
#endif
#include "yasmv.h"
#undef assert
#define assert(condition) __VERIFIER_assert(!!(condition))
