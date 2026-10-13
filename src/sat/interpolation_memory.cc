#include <sat/interpolation_memory.hh>
#include <sat/interpolation_diagnostics.hh>
#include <chrono>
#include <cstdlib>
#include <stdexcept>
#include <string_view>
#ifdef __GLIBC__
#include <malloc.h>
#endif

namespace sat {
void release_interpolation_heap(const char* boundary)
{
    const char* setting = std::getenv("YASMV_IMC_HEAP_RELEASE");
    const std::string_view policy = setting ? setting : "auto";
    if (policy != "auto" && policy != "off")
        throw std::invalid_argument("YASMV_IMC_HEAP_RELEASE must be auto or off");
    constexpr size_t threshold = 64u * 1024u * 1024u;
    bool supported = false, attempted = false, released = false;
    size_t free_bytes = 0;
#ifdef __GLIBC__
    supported = true;
    free_bytes = mallinfo2().fordblks;
    attempted = policy == "auto" && free_bytes >= threshold;
#endif
    const auto log = [&](const char* suffix, uint64_t elapsed_us) {
        if (!diagnostics::enabled()) return;
        diagnostics::Fields fields{{"heap_release_enabled",policy == "auto"},
            {"heap_release_supported",supported},{"heap_release_attempted",attempted},
            {"heap_release_released",released},{"heap_release_free_bytes_before",free_bytes},
            {"heap_release_threshold_bytes",threshold},{"heap_release_elapsed_us",elapsed_us}};
        const auto phase = std::string(boundary) + suffix;
        if (auto* run = diagnostics::current()) run->counters(phase,std::move(fields));
        else diagnostics::sample(phase,std::move(fields));
    };
    log("_heap_release_begin",0);
    const auto started = std::chrono::steady_clock::now();
#ifdef __GLIBC__
    if (attempted) released = malloc_trim(0) != 0;
#endif
    const auto elapsed = std::chrono::duration_cast<std::chrono::microseconds>(
        std::chrono::steady_clock::now()-started).count();
    log("_heap_release_end",elapsed);
}
}
