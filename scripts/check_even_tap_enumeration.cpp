// Exhaustively list the odd-factor product supports with an even tap in degrees 3,5 mod 8.
#include <algorithm>
#include <cstdio>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
bool inverse_coefficient(int a, int b, int degree) {
    bool bit = false;
    for (int j = 0; b*j <= degree; ++j) {
        const int remaining = degree-b*j;
        if (remaining % a == 0 && ((remaining/a) & j) == 0) bit = !bit;
    }
    return bit;
}

bool odd_factor_count(int n, int u, int v) {
    if (u % 2 == 0 && v % 2 == 0) {
        const int a = u/2, b = v/2;
        return (n % a == 0) ^ ((n-v) % a == 0) ^ (n % b == 0) ^ ((n-u) % b == 0);
    }
    if (u % 2 == 0) std::swap(u, v);
    const int r = v/2, b = (n-u)/2, a = b-r;
    if (r % 2 == 0) return b % 2 != 0 && inverse_coefficient(a, b, u);

    bool bit = false;
    for (int j = 0; j <= 3; ++j) bit ^= (n-j*u) % r == 0;
    const int k = u - (b % 2 == 0 ? a : b+2*r);
    bit ^= k >= 0 && k % (2*r) == 0;
    bit ^= k >= a && (k-a) % r == 0;
    return bit ^ inverse_coefficient(a, b, k-2*a);
}
}

int main(int argc, char** argv) {
    try {
        if (argc != 2) throw std::invalid_argument("usage: check_even_tap_enumeration DEGREE");
        const std::string argument(argv[1]);
        std::size_t consumed;
        const long value = std::stol(argument, &consumed);
        if (consumed != argument.size() || value < 3 || value > std::numeric_limits<int>::max()/4
                || (value % 8 != 3 && value % 8 != 5))
            throw std::invalid_argument("expected a degree congruent to three or five modulo eight");
        const int n = static_cast<int>(value);
        std::vector<std::vector<int>> rows(n/2+1);
        #pragma omp parallel for schedule(dynamic, 16)
        for (int u = 1; u <= n/2; ++u) {
            for (int v = u+1; v < n-u; ++v) {
                if ((u % 2 == 0 || v % 2 == 0) && odd_factor_count(n, u, v))
                    rows[u].push_back(v);
            }
        }
        std::puts("degree,u,v");
        for (int u = 1; u <= n/2; ++u)
            for (int v : rows[u]) std::printf("%d,%d,%d\n", n, u, v);
    } catch (const std::exception& error) {
        std::fprintf(stderr, "%s\n", error.what());
        return 1;
    }
}
