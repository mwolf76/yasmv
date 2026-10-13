#ifndef YASMV_INTERPOLATION_MEMORY_HH
#define YASMV_INTERPOLATION_MEMORY_HH

namespace sat {
// Best-effort process-wide allocator release at completed interpolation
// destruction boundaries. No-op on non-glibc platforms.
// YASMV_IMC_HEAP_RELEASE=auto|off selects the policy independently of logging.
void release_interpolation_heap(const char* boundary);
}
#endif
