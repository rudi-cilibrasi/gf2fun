// Enumerate short quotients independently by searching powers modulo each pentanomial.
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <numeric>
#include <vector>

namespace {
using Mask = unsigned __int128;
using Word = std::uint64_t;
using Row = std::array<int, 7>;

constexpr int weight_limit = 9;
constexpr int edges = weight_limit + 2;
constexpr int factor_limit = 2 * edges * edges * edges / 27;
constexpr int quotient_limit = edges * (edges-1) * (edges-2) * (edges-3) / 24;
constexpr int parent_limit = factor_limit + quotient_limit;
constexpr int table_bits = 9;
static_assert(factor_limit < 128 && parent_limit < 32767);

unsigned bucket(Mask value) {
    Word low = static_cast<Word>(value);
    Word high = static_cast<Word>(value >> 64);
    Word mix = low * 0x9e3779b97f4a7c15ULL + high * 0xcbf29ce484222325ULL;
    mix ^= mix >> 27;
    return static_cast<unsigned>(mix >> (64-table_bits));
}

int quotient_weight(int degree, int tap, const std::array<int, 5>& factor) {
    std::array<Word, parent_limit / 64 + 1> remainder{};
    auto toggle = [&](int bit) { remainder[bit/64] ^= Word{1} << (bit%64); };
    toggle(0);
    toggle(tap);
    toggle(degree);
    int count = 0;
    for (int word = degree / 64; word >= 0; --word) {
        while (remainder[word] != 0) {
            int lead = 64*word + 63 - __builtin_clzll(remainder[word]);
            if (lead < factor.back() || ++count > weight_limit) return weight_limit + 1;
            for (int bit : factor) toggle(lead - factor.back() + bit);
        }
    }
    return count;
}

void scan(const std::array<int, 5>& factor, std::vector<Row>& rows) {
    int n = factor.back();
    Mask modulus = 0;
    for (int bit : factor) modulus |= Mask{1} << bit;
    std::array<std::int16_t, 1 << table_bits> heads;
    heads.fill(-1);
    std::array<std::int16_t, parent_limit + 1> next;
    std::array<Mask, parent_limit + 1> residues;
    Mask residue = 1;
    for (int degree = 0; degree <= n + quotient_limit; ++degree) {
        if (degree > n) {
            // A match of the full residues means F divides X^degree + X^tap + 1.
            Mask target = residue ^ 1;
            for (int tap = heads[bucket(target)]; tap >= 0; tap = next[tap]) {
                if (tap == 0 || residues[tap] != target) continue;
                int weight = quotient_weight(degree, tap, factor);
                if (weight <= weight_limit)
                    rows.push_back({weight, degree, tap, n, factor[1], factor[2], factor[3]});
            }
        }
        unsigned key = bucket(residue);
        next[degree] = heads[key];
        heads[key] = static_cast<std::int16_t>(degree);
        residues[degree] = residue;
        residue <<= 1;
        if ((residue >> n) != 0) residue ^= modulus;
    }
}
}

int main() {
    std::vector<Row> rows;
    #pragma omp parallel
    {
        std::vector<Row> local;
        #pragma omp for schedule(dynamic, 1)
        for (int n = 4; n <= factor_limit; ++n)
            for (int a = 1; a < n-2; ++a)
                for (int b = a+1; b < n-1; ++b)
                    for (int c = b+1; c < n; ++c)
                        if (std::gcd(std::gcd(n, a), std::gcd(b, c)) == 1)
                            scan({0, a, b, c, n}, local);
        #pragma omp critical
        rows.insert(rows.end(), local.begin(), local.end());
    }
    std::sort(rows.begin(), rows.end());
    std::cout << "quotient_weight,parent_degree,parent_tap,factor_degree,a,b,c\n";
    for (const Row& row : rows) {
        std::cout << row[0];
        for (std::size_t i = 1; i < row.size(); ++i) std::cout << ',' << row[i];
        std::cout << '\n';
    }
}
