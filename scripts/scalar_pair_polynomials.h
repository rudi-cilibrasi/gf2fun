#pragma once

#include <NTL/GF2X.h>
#include <algorithm>

namespace scalar_pairs {
inline NTL::GF2X trinomial(long a, long b, long c) {
    long low = std::min({a, b, c});
    NTL::GF2X f;
    for (long e : {a, b, c}) NTL::SetCoeff(f, e-low);
    return f;
}

inline NTL::GF2X cyclotomic(long h) {
    NTL::GF2X f;
    NTL::SetCoeff(f, h);
    NTL::SetCoeff(f, 0);
    long remaining = h;
    for (long d = 2; d <= remaining; ++d) {
        if (remaining % d) continue;
        NTL::GF2X smaller;
        NTL::SetCoeff(smaller, h/d);
        NTL::SetCoeff(smaller, 0);
        f /= NTL::GCD(f, smaller);
        do { remaining /= d; } while (remaining % d == 0);
    }
    return f;
}
}
