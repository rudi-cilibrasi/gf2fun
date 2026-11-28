// Find sparse-root quotients with one unknown factor or a bounded relative factor degree.
#include <NTL/GF2XFactoring.h>

#include <algorithm>
#include <atomic>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

using namespace NTL;

GF2X read_mask() {
    std::string s;
    if (!(std::cin >> s) || s.size() < 3 || s.substr(0, 2) != "0x")
        throw std::invalid_argument("expected a hexadecimal polynomial mask on standard input");
    GF2X out;
    for (size_t i = 2; i < s.size(); ++i) {
        int digit = std::stoi(s.substr(i, 1), nullptr, 16);
        for (int b = 0; b < 4; ++b)
            if ((digit >> b) & 1) SetCoeff(out, 4 * (s.size() - i - 1) + b);
    }
    return out;
}

std::string mask_hex(const GF2X& p) {
    std::string s = "0x";
    for (long i = std::max(0L, deg(p)) / 4; i >= 0; --i) {
        unsigned digit = 0;
        for (int b = 0; b < 4; ++b)
            if (IsOne(coeff(p, 4*i + b))) digit |= 1u << b;
        s += "0123456789abcdef"[digit];
    }
    return s;
}

// All irreducible factors of degree dividing 20 occur once in T^(2^20) + T.
GF2X linear_base_part(const GF2X& p) {
    if (deg(p) <= 1) return p;
    GF2X t(1, 1), power = t;
    GF2XModulus mod(p);
    for (int i = 0; i < 20; ++i) SqrMod(power, power, mod);
    return GCD(p, power + t);
}

GF2X remove_linear_base(GF2X p) {
    GF2X part = linear_base_part(p);
    while (deg(part) > 0) {
        p /= part;
        part = GCD(p, part);
    }
    return p;
}

// Apply the degree bounds to two adjacent Euclidean remainder vectors.
struct Fraction { GF2X u, v; };

std::vector<Fraction> quotient_basis(const GF2X& field, const GF2X& w, long top, long bottom) {
    GF2X a = field, b = w, c, d(0, 1);
    while (!IsZero(b) && deg(b) - deg(d) >= top - bottom) {
        GF2X quotient, remainder;
        DivRem(quotient, remainder, a, b);
        a = b;
        b = remainder;
        remainder = c + quotient * d;
        c = d;
        d = remainder;
    }
    std::vector<Fraction> basis;
    for (long i = 0; i <= top - deg(a); ++i) basis.push_back({a << i, c << i});
    for (long i = 0; i <= bottom - deg(d); ++i) basis.push_back({b << i, d << i});
    return basis;
}

std::vector<GF2X> conjugates(const GF2XModulus& mod, GF2X root, long n) {
    std::vector<GF2X> orbit(n);
    for (auto& w : orbit) {
        w = root;
        SqrMod(root, root, mod);
    }
    if (root != orbit.front()) throw std::logic_error("incorrect Frobenius orbit");
    return orbit;
}

std::vector<GF2X> shift_powers(const GF2XModulus& mod, const GF2X& multiplier,
                               long start, long count, long n) {
    std::vector<GF2X> powers((start+count-1)/n - start/n + 1);
    PowerMod(powers.front(), multiplier, start/n, mod);
    for (size_t i = 1; i < powers.size(); ++i) MulMod(powers[i], powers[i-1], multiplier, mod);
    return powers;
}

bool bounded_factors(const GF2X& p, long bound) {
    for (const auto& piece : SquareFreeDecomp(p)) {
        for (const auto& group : DDF(piece.a)) {
            long d = group.b;
            if (d / std::gcd(d, 20L) > bound) return false;
        }
    }
    return true;
}

int smooth_search(long bound, long start, long count) {
    const long n = 1229, stride = 64817;
    GF2X field = read_mask(), root = read_mask();
    if (deg(field) != n || !IterIrredTest(field) || IsZero(root) || deg(root) >= n ||
        bound < 1 || start < 0 || count < 1 || start > std::numeric_limits<long>::max()-count ||
        (start+count-1)/n > std::numeric_limits<long>::max()/stride)
        throw std::invalid_argument("invalid model, relative degree or search interval");
    GF2XModulus mod(field);
    auto orbit = conjugates(mod, root, n);
    auto powers = shift_powers(mod, PowerMod(GF2X(1,1), stride, mod), start, count, n);
    #pragma omp parallel for schedule(dynamic, 1)
    for (long step = 0; step < count; ++step) {
        const long index = start+step, j = index%n, shift = index/n;
        auto basis = quotient_basis(field, MulMod(orbit[j], powers[shift-start/n], mod), 620, 620);
        // The first 1023 Gray-code combinations use the first ten basis vectors.
        unsigned choices = 1u << std::min<size_t>(10, basis.size());
        GF2X u, v;
        for (unsigned i = 1; i < choices; ++i) {
            const auto& delta = basis[__builtin_ctz(i)];
            u += delta.u;
            v += delta.v;
            if (IsZero(u) || IsZero(v) || !IsOne(GCD(u, v)) ||
                !bounded_factors(u, bound) || !bounded_factors(v, bound)) continue;
            #pragma omp critical
            {
                std::cout << "{\"frobenius\": " << j << ", \"base_shift\": " << shift*stride
                          << ", \"numerator_hex\": \"" << mask_hex(u)
                          << "\", \"denominator_hex\": \"" << mask_hex(v) << "\"}" << std::endl;
            }
        }
    }
    return 0;
}

int main(int argc, char** argv) {
    if (argc == 5 && std::string(argv[1]) == "--smooth")
        return smooth_search(std::stol(argv[2]), std::stol(argv[3]), std::stol(argv[4]));
    if (argc != 6) {
        std::cerr << "Usage: find_1229_known_offset NUM_DEG DEN_DEG RELATIVE_DEG START COUNT\n"
                  << "   or: find_1229_known_offset --smooth MAX_RELATIVE_DEG START COUNT\n"
                  << "Read the model modulus and sparse root as hexadecimal masks from stdin.\n";
        return 2;
    }
    const long top = std::stol(argv[1]), bottom = std::stol(argv[2]), relative = std::stol(argv[3]);
    const long start = std::stol(argv[4]), count = std::stol(argv[5]);
    GF2X field = read_mask(), root = read_mask();
    const long n = deg(field);
    if (n != 1229 || !IterIrredTest(field) || IsZero(root) || deg(root) >= n ||
        bottom < 1 || top < bottom || top >= n || relative < 1 ||
        start < 0 || count < 1 || start > std::numeric_limits<long>::max() - count ||
        top + bottom + 2 - n > 23)
        throw std::invalid_argument("invalid model, search interval or degree bounds");
    const GF2XModulus mod(field);
    auto orbit = conjugates(mod, root, n);
    GF2X multiplier(20, 1);
    SetCoeff(multiplier, 3);
    SetCoeff(multiplier, 0);
    auto powers = shift_powers(mod, multiplier, start, count, n);
    std::atomic<bool> found(false), oversized(false);
    #pragma omp parallel for schedule(dynamic, 4)
    for (long step = 0; step < count; ++step) {
        if (found.load()) continue;
        const long j = (start + step) % n, shift = (start + step) / n;
        auto basis = quotient_basis(field, MulMod(orbit[j], powers[shift - start/n], mod), top, bottom);
        if (basis.size() > 23) {
            oversized.store(true);
            continue;
        }
        GF2X u, v;
        for (unsigned i = 1; i < (1u << basis.size()); ++i) {
            const auto& delta = basis[__builtin_ctz(i)];
            u += delta.u;
            v += delta.v;
            if (IsZero(u) || IsZero(v) || !IsOne(remove_linear_base(v))) continue;
            GF2X unknown = remove_linear_base(u);
            long degree = deg(unknown);
            if (!IsOne(unknown) &&
                (degree / std::gcd(degree, 20L) > relative || !IterIrredTest(unknown))) continue;
            if (!found.exchange(true)) {
                GF2X common = GCD(u, v);
                std::cout << "{\"frobenius\": " << j << ", \"multiplier_hex\": \"0x100009\""
                          << ", \"multiplier_power\": " << shift
                          << ", \"known_numerator_hex\": \"" << mask_hex((u / common) / unknown)
                          << "\", \"known_denominator_hex\": \"" << mask_hex(v / common)
                          << "\", \"unknown_mask_hex\": \"" << mask_hex(unknown) << "\"}\n";
            }
            break;
        }
    }
    if (found.load()) return 0;
    if (oversized.load()) {
        std::cerr << "One or more quotient spaces exceeded 23 dimensions. Reduce the degree bounds.\n";
        return 2;
    }
    return 1;
}
