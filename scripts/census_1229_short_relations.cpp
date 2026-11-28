// Classify short multiplicative relations between a degree-1229 element and its translate.
#include <NTL/GF2XFactoring.h>
#include <array>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using namespace NTL;
constexpr int degree = 1229;
constexpr int limit = 2 * degree - 1;

struct Row {
    int tap;
    long parent_weight;
    std::array<long, 3> coordinate_weights;
};

struct Slice {
    int parents = 0;
    std::vector<Row> rows;
};

Slice scan(int m) {
    Slice result;
    const GF2X x(1, 1);
    for (int a = 1; 2 * a <= m; ++a) {
        if (std::gcd(m, a) != 1) continue;
        ++result.parents;
        GF2X parent = GF2X(m, 1) + GF2X(a, 1) + 1;
        GF2XModulus modulus(parent);
        GF2X power = x;
        for (int i = 0; i < degree; ++i) SqrMod(power, power, modulus);
        // The degree is prime, the parent has no linear factor, and m < 2*degree.
        GF2X factor = GCD(parent, power + x);
        if (IsOne(factor)) continue;
        if (deg(factor) != degree) throw std::logic_error("unexpected Frobenius gcd");

        Row row{a, weight(factor), {}};
        GF2XModulus field(factor);
        const std::array<int, 3> exponents{a, m, m - a};
        for (size_t i = 0; i < exponents.size(); ++i) {
            GF2X value = PowerXMod(exponents[i], field);
            GF2X p = MinPolyMod(value, field);
            if (deg(p) != degree || !IsZero(CompMod(p, value, field)))
                throw std::logic_error("coordinate minimal polynomial failed verification");
            row.coordinate_weights[i] = weight(p);
        }
        result.rows.push_back(row);
    }
    return result;
}
}

int main(int argc, char **argv) {
    int first = degree, last = limit;
    if (argc == 3) {
        first = std::stoi(argv[1]);
        last = std::stoi(argv[2]);
    }
    if ((argc != 1 && argc != 3) || first < degree || last > limit || first > last) {
        std::cerr << "usage: census_1229_short_relations [first_degree last_degree]\n";
        return 2;
    }
    std::vector<Slice> slices(last - first + 1);
    #pragma omp parallel for schedule(dynamic, 1)
    for (int m = first; m <= last; ++m) slices[m - first] = scan(m);

    long parents = 0, hits = 0;
    std::cout << "degree,tap,weight_z,weight_z_a,weight_z_m,weight_z_m_minus_a\n";
    for (int m = first; m <= last; ++m) {
        const auto& slice = slices[m - first];
        parents += slice.parents;
        hits += slice.rows.size();
        for (const Row& row : slice.rows) {
            std::cout << m << ',' << row.tap << ',' << row.parent_weight;
            for (long w : row.coordinate_weights) std::cout << ',' << w;
            std::cout << '\n';
        }
    }
    std::cerr << parents << " normalized trinomials, " << hits << " with a degree-1229 factor\n";
}
