// Search increasing normalized tap widths. Read the prime factors of 2^n-1
// from stdin, including multiplicities. Certify returned rows with check_product_range.py.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <charconv>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string_view>
#include <utility>
#include <vector>

namespace {
using NTL::GF2X;
using NTL::GF2XModulus;
using NTL::ZZ;

long positive_integer(std::string_view value) {
    long result = 0;
    auto end = value.data() + value.size();
    auto parsed = std::from_chars(value.data(), end, result);
    if (parsed.ec != std::errc{} || parsed.ptr != end || result < 1 ||
        result > std::numeric_limits<int>::max())
        throw std::invalid_argument("expected a positive 32-bit integer");
    return result;
}

bool full_order(const GF2XModulus& modulus, const ZZ& order, const std::vector<ZZ>& tree) {
    const size_t leaves = tree.size()/2;
    struct Node { size_t index; GF2X value; };
    std::vector<Node> pending{{1, NTL::PowerXMod(order/tree[1], modulus)}};
    while (!pending.empty()) {
        Node node = std::move(pending.back());
        pending.pop_back();
        // This value is X^(order/product of the primes below this node).
        if (NTL::IsOne(node.value)) return false;
        if (node.index < leaves) {
            const size_t left = 2*node.index, right = left+1;
            pending.push_back({left, NTL::PowerMod(node.value, tree[right], modulus)});
            pending.push_back({right, NTL::PowerMod(node.value, tree[left], modulus)});
        }
    }
    return true;
}

int run(int argc, char** argv) {
    if (argc < 2 || argc > 3) throw std::invalid_argument("usage: search_width DEGREE [MAX_WIDTH]");
    const long n = positive_integer(argv[1]);
    if (n < 4) throw std::invalid_argument("five terms require degree at least four");
    const long limit = argc == 3 ? std::min(n, positive_integer(argv[2])) : n;
    const ZZ order = NTL::power2_ZZ(n)-1;
    ZZ factor, product(1);
    std::vector<ZZ> primes;
    while (std::cin >> factor) {
        if (factor < 2) throw std::invalid_argument("invalid order factor");
        product *= factor;
        primes.push_back(factor);
    }
    if (!std::cin.eof() || product != order) throw std::invalid_argument("incomplete order factorization");
    std::sort(primes.begin(), primes.end());
    primes.erase(std::unique(primes.begin(), primes.end()), primes.end());
    for (const ZZ& p : primes)
        if (!NTL::ProbPrime(p)) throw std::invalid_argument("composite order factor");
    std::vector<ZZ> tree(2*primes.size());
    std::copy(primes.begin(), primes.end(), tree.begin()+primes.size());
    for (size_t i = primes.size()-1; i > 0; --i) tree[i] = tree[2*i]*tree[2*i+1];

    for (long width = 3; width <= limit; ++width) {
        for (long c = 1; c <= width/2; ++c) {
            // At width > 2c there is one possible k. At width = 2c any k < c fits.
            const long first = width == 2*c ? 1 : width-c;
            const long last = width == 2*c ? c-1 : first;
            for (long k = first; k <= last; ++k) {
                if (std::gcd(c, k) != 1) continue;
                for (long w = 1; w <= (n-1)/std::max(k,c); ++w) {
                    if (std::gcd(w, n) != 1) continue;
                    const long b = c*w, a = k*w;
                    if (b == n-b || a == n-b) continue;
                    GF2X f;
                    for (long exponent : {0L,b,a,n-b,n}) NTL::SetCoeff(f,exponent);
                    if (!NTL::IterIrredTest(f) || !full_order(GF2XModulus(f), order, tree)) continue;
                    std::cout << n << ',' << std::min(b,n-b) << ',' << std::min(a,n-a) << '\n';
                    return 0;
                }
            }
        }
    }
    std::cerr << "No primitive complementary pentanomial through width " << limit << '\n';
    return 1;
}
}

int main(int argc, char** argv) {
    try { return run(argc, argv); }
    catch (const std::exception& e) { std::cerr << e.what() << '\n'; return 2; }
}
