// NTL backend for check_1229_factor_base_orders.py. Input and output use decimal integers.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <array>
#include <iostream>
#include <vector>

using NTL::GF2X;
using NTL::GF2XModulus;
using NTL::ZZ;

static GF2X binary_polynomial(const ZZ& mask) {
    GF2X f;
    for (long i = 0; i < NTL::NumBits(mask); ++i)
        if (NTL::bit(mask, i)) NTL::SetCoeff(f, i);
    return f;
}

// The same base is raised to a different 943-bit exponent on every row.
constexpr long window = 6;
using Powers = std::vector<std::array<GF2X, 1L << window>>;

static Powers fixed_powers(GF2X base, long bits, const GF2XModulus& field) {
    Powers powers((bits + window - 1) / window);
    for (auto& column : powers) {
        NTL::set(column[0]);
        for (size_t j = 1; j < column.size(); ++j)
            NTL::MulMod(column[j], column[j-1], base, field);
        NTL::MulMod(base, column.back(), base, field);
    }
    return powers;
}

static GF2X remove_cofactor_part(GF2X value, const ZZ& log, const Powers& powers,
                                 const GF2XModulus& field) {
    long offset = 0;
    for (const auto& column : powers) {
        long digit = 0;
        for (long i = 0; i < window; ++i) digit += NTL::bit(log, offset+i) << i;
        if (digit != 0) NTL::MulMod(value, value, column[digit], field);
        offset += window;
    }
    return value;
}

struct Row {
    long mask, terms = 0, missing = 0;
    ZZ log;
};

int main() {
    ZZ modulus_mask;
    std::array<ZZ, 4> primes;
    if (!(std::cin >> modulus_mask >> primes[0] >> primes[1] >> primes[2] >> primes[3])) return 1;
    const GF2X modulus = binary_polynomial(modulus_mask);
    if (NTL::deg(modulus) != 1229 || !NTL::IterIrredTest(modulus)) return 1;
    const GF2XModulus field(modulus);
    const ZZ order = NTL::power2_ZZ(1229) - 1;
    const ZZ small = primes[0]*primes[1], large = primes[2]*primes[3];
    const ZZ known = small*large, cofactor = order/known;
    if (known*cofactor != order || NTL::GCD(known, cofactor) != 1) return 1;
    const ZZ projector = known*NTL::InvMod(known % cofactor, cofactor);
    const Powers powers = fixed_powers(NTL::PowerXMod(order-projector, field),
                                       NTL::NumBits(cofactor), field);
    std::vector<Row> rows;
    long mask;
    ZZ log;
    while (std::cin >> mask >> log) rows.push_back({mask, 0, 0, log});
    if (!std::cin.eof() || rows.empty()) return 1;
    bool valid = true;
    #pragma omp parallel reduction(&&:valid)
    {
        const GF2XModulus local_field(modulus);
        #pragma omp for schedule(static)
        for (size_t i = 0; i < rows.size(); ++i) {
            Row& row = rows[i];
            const GF2X p = binary_polynomial(NTL::to_ZZ(row.mask));
            if (NTL::deg(p) <= 0 || 20 % NTL::deg(p) || !NTL::IterIrredTest(p) ||
                row.log < 0 || row.log >= cofactor || NTL::GCD(row.log, cofactor) != 1) {
                valid = false;
                continue;
            }
            const GF2X v = remove_cofactor_part(p, row.log, powers, local_field);
            const GF2X small_part = NTL::PowerMod(v, large, local_field);
            const GF2X large_part = NTL::PowerMod(v, small, local_field);
            const GF2X first = NTL::PowerMod(small_part, primes[1], local_field);
            // v^known = 1 is exactly the published projected logarithm identity.
            if (!NTL::IsOne(NTL::PowerMod(first, primes[0], local_field))) {
                valid = false;
                continue;
            }
            row.missing = NTL::IsOne(first) + 2*NTL::IsOne(NTL::PowerMod(small_part, primes[0], local_field))
                        + 4*NTL::IsOne(NTL::PowerMod(large_part, primes[3], local_field))
                        + 8*NTL::IsOne(NTL::PowerMod(large_part, primes[2], local_field));
            // Each nonconstant p(x) has degree 1229 because the extension has prime degree.
            const GF2X minimal = NTL::IrredPolyMod(p, local_field);
            if (NTL::deg(minimal) != 1229) valid = false;
            row.terms = NTL::weight(minimal);
        }
    }
    if (!valid) {
        std::cerr << "A field identity, irreducibility, or degree check failed.\n";
        return 1;
    }
    for (const Row& row : rows)
        std::cout << row.mask << ' ' << row.terms << ' ' << row.missing << '\n';
}
