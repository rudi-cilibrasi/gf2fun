// Check short sums of conjugate exponents modulo a known degree-1229 order divisor.
// Build with g++ -O3 -std=c++17 -fopenmp scripts/check_1229_short_products.cpp -lgmpxx -lgmp -o check1229
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>
#include <gmpxx.h>

namespace {
constexpr int degree = 1229;
constexpr int max_half = 4;
using Key = std::array<std::uint64_t, 2>;

std::uint64_t binomial(int n, int k) {
    std::uint64_t result = 1;
    for (int i = 1; i <= k; ++i) result = result * (n + 1 - i) / i;
    return result;
}

class Checker {
    const mpz_class prime{"10543179280661916121033"};
    const mpz_class middle = prime / 2;
    std::array<mpz_class, degree> powers;
    std::array<int, max_half> gaps{};
    std::array<mpz_class, max_half> sums;
    mpz_class value;
    std::vector<Key> keys;

    Key signature(const mpz_class &sum, mpz_class &result) const {
        mpz_powm_ui(result.get_mpz_t(), sum.get_mpz_t(), degree, prime.get_mpz_t());
        bool negative = result > middle;
        if (negative) result = prime - result;
        // Store (min(t,p-t), sign) exactly as a two-word lexicographic key.
        std::uint64_t words[2]{};
        mpz_export(words, nullptr, -1, sizeof(words[0]), 0, 0, result.get_mpz_t());
        return {(words[1] << 1) | (words[0] >> 63), (words[0] << 1) | negative};
    }

    void record(int size) {
        // The closing gap is first in this cyclic ordering. Use the largest
        // lexicographic rotation to resolve ties between largest gaps.
        for (int offset = 1; offset < size; ++offset) {
            for (int i = 0; i < size; ++i) {
                int other = gaps[(offset + i) % size];
                if (other > gaps[i]) return;
                if (other < gaps[i]) break;
            }
        }
        Key key = signature(sums[size - 1], value);
        if (key == Key{}) throw std::runtime_error("a half-sum is zero");
        keys.push_back(key);
    }

    void enumerate(int size, int used, int last, int largest) {
        int remaining = degree - last;
        if (used == size) {
            gaps[0] = remaining;
            record(size);
            return;
        }
        // Reserve one positive gap per remaining interior position and
        // enough space for the closing gap to dominate every interior gap.
        int after = size - used - 1;
        int limit = std::min((remaining - after) / 2, remaining - largest - after);
        for (int gap = 1; gap <= limit; ++gap) {
            gaps[used] = gap;
            sums[used] = sums[used - 1] + powers[last + gap];
            enumerate(size, used + 1, last + gap, std::max(largest, gap));
        }
    }

public:
    void run(int half) {
        if (mpz_probab_prime_p(prime.get_mpz_t(), 30) == 0 || mpz_sizeinbase(prime.get_mpz_t(), 2) > 127)
            throw std::runtime_error("invalid modulus for the two-word keys");
        powers[0] = 1;
        for (int i = 1; i < degree; ++i) powers[i] = (2 * powers[i - 1]) % prime;
        if ((2 * powers.back()) % prime != 1 || std::count(powers.begin(), powers.end(), 1) != 1)
            throw std::runtime_error("unexpected order of 2");
        std::uint64_t total = 0;
        for (int k = 1; k <= half; ++k) total += binomial(degree, k) / degree;
        keys.reserve(total);
        sums[0] = 1;
        for (int k = 1; k <= half; ++k) {
            auto previous = keys.size();
            enumerate(k, 1, 0, 0);
            if ((keys.size() - previous) * degree != binomial(degree, k))
                throw std::runtime_error("cyclic orbit count disagrees with the binomial coefficient");
            std::cout << "Rank " << k << " has " << keys.size() - previous << " orbits.\n";
        }
        std::sort(keys.begin(), keys.end());
        for (std::size_t i = 1; i < keys.size(); ++i) {
            if (keys[i] == keys[i - 1])
                throw std::runtime_error("distinct cyclic subset orbits have equal signatures");
            if (keys[i][0] == keys[i - 1][0] && (keys[i][1] ^ keys[i - 1][1]) == 1)
                throw std::runtime_error("opposite half-sum signatures intersect");
        }
        std::cout << "All " << total << " nonzero subset-orbit signatures are distinct.\n";
        std::cout << "All " << total << " signatures exclude product-one ranks 1 through "
                  << 2 * half << ".\n";
    }

    void check_nine() const {
        // The nine cyclic windows of five points each use four gaps. Their
        // total width is 4n, so a shortest window fits in [0, floor(4n/9)].
        constexpr int width = 4 * degree / 9;
        constexpr std::uint64_t mask = (std::uint64_t{1} << 31) - 1;
        std::vector<std::uint64_t> low((mask + 1) / 64), high(low.size());
        for (const Key &key : keys) {
            auto a = key[1] & mask;
            auto b = ((key[1] >> 32) ^ key[0]) & mask;
            low[a / 64] |= std::uint64_t{1} << (a % 64);
            high[b / 64] |= std::uint64_t{1} << (b % 64);
        }
        std::uint64_t tested = 0, collisions = 0;
#ifdef _OPENMP
#pragma omp parallel for schedule(dynamic, 1) reduction(+:tested, collisions)
#endif
        for (int i = 1; i <= width - 3; ++i) {
            mpz_class pair = 1 + powers[i], triple, four, five, result;
            for (int j = i + 1; j <= width - 2; ++j) {
                triple = pair + powers[j];
                for (int k = j + 1; k <= width - 1; ++k) {
                    four = triple + powers[k];
                    for (int l = k + 1; l <= width; ++l) {
                        five = four + powers[l];
                        Key wanted = signature(five, result);
                        ++tested;
                        if (wanted == Key{}) {
                            ++collisions;
                            continue;
                        }
                        wanted[1] ^= 1;
                        auto a = wanted[1] & mask;
                        if (!((low[a / 64] >> (a % 64)) & 1)) continue;
                        auto b = ((wanted[1] >> 32) ^ wanted[0]) & mask;
                        if (!((high[b / 64] >> (b % 64)) & 1)) continue;
                        if (std::binary_search(keys.begin(), keys.end(), wanted)) ++collisions;
                    }
                }
            }
        }
        if (tested != binomial(width, 4)) throw std::runtime_error("incorrect five-term window count");
        if (collisions) throw std::runtime_error("five-term windows give a zero or an opposite signature");
        std::cout << "All " << tested << " five-term windows exclude rank 9.\n";
    }
};
}

int main(int argc, char **argv) {
    try {
        bool nine = argc == 2 && std::string(argv[1]) == "--nine";
        int half = argc == 1 || nine ? max_half : std::stoi(argv[1]);
        if (argc > 2 || half < 1 || half > max_half)
            throw std::invalid_argument("supply --nine or a half-rank from 1 through 4");
        Checker checker;
        checker.run(half);
        if (nine) checker.check_nine();
    } catch (const std::exception &error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
