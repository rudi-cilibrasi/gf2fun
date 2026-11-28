// Measure minimal-polynomial weights along two linear and one quadratic sequence.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <array>
#include <iostream>
#include <limits>
#include <set>
#include <stdexcept>
#include <vector>

using NTL::GF2X;
using NTL::GF2XModulus;
using NTL::ZZ;

namespace {
constexpr long degree = 1229;

GF2X read_polynomial() {
    ZZ mask;
    if (!(std::cin >> mask) || mask <= 0) throw std::runtime_error("invalid binary mask");
    std::vector<unsigned char> bytes(NTL::NumBytes(mask));
    NTL::BytesFromZZ(bytes.data(), mask, bytes.size());
    return NTL::GF2XFromBytes(bytes.data(), bytes.size());
}

// The value at t is first * ratio^t * curvature^binom(t,2).
void census(const char* name, long radius, const GF2X& first, const GF2X& ratio,
            const GF2X& curvature, const GF2XModulus& field) {
    const ZZ start(-radius);
    const ZZ triangular = start * (start - 1) / 2;
    GF2X value = NTL::MulMod(first, NTL::PowerMod(ratio, start, field), field);
    value = NTL::MulMod(value, NTL::PowerMod(curvature, triangular, field), field);
    GF2X step = NTL::MulMod(ratio, NTL::PowerMod(curvature, start, field), field);
    using Mask = std::array<unsigned char, (degree + 8) / 8>;
    std::set<Mask> polynomials;
    long minimum = degree + 2, position = 0;
    for (long t = -radius; t <= radius; ++t) {
        const GF2X f = NTL::MinPolyMod(value, field);
        if (NTL::IsZero(value) || NTL::IsOne(value) || NTL::deg(f) != degree ||
            !NTL::IsZero(NTL::CompMod(f, value, field)))
            throw std::runtime_error("degree or substitution failed");
        Mask mask;
        NTL::BytesFromGF2X(mask.data(), f, mask.size());
        polynomials.insert(mask);
        const long weight = NTL::weight(f);
        if (weight <= 5) {
            std::cout << name << " hit " << t;
            for (long j = 0; j <= degree; ++j)
                if (NTL::IsOne(NTL::coeff(f, j))) std::cout << ' ' << j;
            std::cout << '\n';
        } else if (weight < minimum) {
            minimum = weight;
            position = t;
        }
        value = NTL::MulMod(value, step, field);
        step = NTL::MulMod(step, curvature, field);
    }
    std::cout << name << " minimum-above-five " << minimum << ' ' << position << '\n';
    std::cout << name << " distinct " << polynomials.size() << std::endl;
}
}

int main() {
    long radius;
    ZZ known;
    if (!(std::cin >> radius >> known) || radius < 1 ||
        radius == std::numeric_limits<long>::max() || known < 1)
        throw std::runtime_error("invalid radius or known order component");
    const GF2X f = read_polynomial(), a = read_polynomial(), b = read_polynomial();
    if (NTL::deg(f) != degree || !NTL::IterIrredTest(f) ||
        NTL::deg(a) >= degree || NTL::deg(b) >= degree)
        throw std::runtime_error("invalid common field or root");
    const GF2XModulus field(f);
    const GF2X step = NTL::PowerXMod(known, field);
    census("product", radius, a, step, GF2X(1), field);
    census("seroussi", radius, b, step, GF2X(1), field);
    const GF2X ratio = NTL::MulMod(b, NTL::InvMod(a, f), field);
    census("quadratic", radius, a, ratio, step, field);
}
