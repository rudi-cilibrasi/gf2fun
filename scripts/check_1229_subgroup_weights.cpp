// Enumerate the minimal polynomials in the subgroup of order 36871 * 46703.
#include <NTL/GF2XFactoring.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <utility>
#include <vector>

namespace {
constexpr int n = 1229;
constexpr int p = 36871;
constexpr int q = 46703;

// The powers of two act on exponents by field conjugation.
std::vector<int> orbit_representatives(int prime) {
    std::vector<bool> used(prime);
    std::vector<int> reps;
    for (int e = 1; e < prime; ++e) {
        if (used[e]) continue;
        reps.push_back(e);
        int k = e, length = 0;
        do {
            used[k] = true;
            k = 2 * k % prime;
            ++length;
        } while (k != e);
        if (length != n) throw std::runtime_error("unexpected orbit length");
    }
    return reps;
}

struct Weights {
    std::int64_t count = 0;
    int lowest = n + 2, highest = 0;
    std::pair<int, int> first{};

    void combine(const Weights &other) {
        if (!other.count) return;
        count += other.count;
        highest = std::max(highest, other.highest);
        if (other.lowest < lowest || (other.lowest == lowest && other.first < first)) {
            lowest = other.lowest;
            first = other.first;
        }
    }

    void measure(const NTL::GF2X &root, const NTL::GF2XModulus &field, int a, int b) {
        NTL::GF2X poly = NTL::MinPolyMod(root, field);
        if (NTL::deg(poly) != n) throw std::runtime_error("incorrect minimal-polynomial degree");
        const int weight = NTL::weight(poly);
        combine({1, weight, weight, {a, b}});
    }
};

NTL::GF2X project(const NTL::GF2XModulus &field, const NTL::ZZ &group, int prime) {
    if (group % prime != 0) throw std::runtime_error("incorrect group divisor");
    NTL::GF2X root;
    NTL::PowerXMod(root, group / prime, field);
    if (NTL::IsOne(root) || !NTL::IsOne(NTL::PowerMod(root, prime, field)))
        throw std::runtime_error("incorrect projected order");
    return root;
}
}

int main() {
    NTL::GF2X f;
    for (int i : {0, 2, 6, 15, n}) NTL::SetCoeff(f, i);
    if (!NTL::IterIrredTest(f)) throw std::runtime_error("reducible field modulus");
    const NTL::GF2XModulus field(f);
    const NTL::ZZ group = NTL::power2_ZZ(n) - 1;
    const auto alpha = project(field, group, p);
    const auto beta = project(field, group, q);
    const auto reps = orbit_representatives(p);
    std::vector<std::array<Weights, 2>> rows(reps.size());

    // Each product orbit with nontrivial first coordinate has a unique
    // representative alpha^a beta^b with a in reps and 0 <= b < q.
    #pragma omp parallel for schedule(dynamic, 1)
    for (int i = 0; i < static_cast<int>(reps.size()); ++i) {
        NTL::GF2XModulus local_field(f);
        NTL::GF2X y = NTL::PowerMod(alpha, reps[i], local_field);
        rows[i][0].measure(y, local_field, reps[i], 0);
        for (int b = 1; b < q; ++b) {
            NTL::MulMod(y, y, beta, local_field);
            rows[i][1].measure(y, local_field, reps[i], b);
        }
    }
    std::array<Weights, 3> result{};
    for (const auto &row : rows) {
        result[0].combine(row[0]);
        result[2].combine(row[1]);
    }
    for (int b : orbit_representatives(q))
        result[1].measure(NTL::PowerMod(beta, b, field), field, 0, b);

    const std::array<std::int64_t, 3> orders{p, q, std::int64_t(p)*q};
    const std::array<std::int64_t, 3> elements{p-1, q-1, std::int64_t(p-1)*(q-1)};
    std::cout << "order,polynomials,min_weight,max_weight,alpha_exponent,beta_exponent\n";
    for (int i = 0; i < 3; ++i) {
        const auto &w = result[i];
        if (w.count * n != elements[i]) throw std::runtime_error("incomplete subgroup census");
        std::cout << orders[i] << ',' << w.count << ',' << w.lowest << ',' << w.highest
                  << ',' << w.first.first << ',' << w.first.second << '\n';
    }
}
