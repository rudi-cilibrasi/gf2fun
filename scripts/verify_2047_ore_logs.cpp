// Read a decompressed degree-2047 projected-log archive on stdin.
// Every row is verified by finite-field exponentiation, independently of the solve.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <array>
#include <atomic>
#include <cstdint>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using namespace NTL;
constexpr int degree = 2047, width = 228;

unsigned read32() {
    std::array<unsigned char, 4> buf{};
    if (!std::cin.read(reinterpret_cast<char*>(buf.data()), buf.size()))
        throw std::runtime_error("truncated integer");
    unsigned value = 0;
    for (unsigned i = 0; i < buf.size(); ++i) value |= unsigned(buf[i]) << (8*i);
    return value;
}

struct Row {
    unsigned mask;
    std::array<unsigned char, width> bytes;
};

GF2X polynomial(unsigned mask) {
    GF2X result;
    for (unsigned j = 0; mask; mask >>= 1, ++j) if (mask & 1) SetCoeff(result, j);
    return result;
}

void verify(int jobs) {
    char magic[4];
    if (!std::cin.read(magic, 4) || std::memcmp(magic, "G2O1", 4))
        throw std::runtime_error("invalid archive");
    unsigned q = read32(), n = read32();
    if (!((q == 512 && n == 14602) || (q == 1024 && n == 52488)))
        throw std::runtime_error("unexpected factor-base size");
    const int m = q == 512 ? 18 : 20;
    GF2X modulus;
    for (unsigned j : {0u, 511u, 2047u}) SetCoeff(modulus, j);
    if (!IterIrredTest(modulus)) throw std::runtime_error("reducible modulus");
    const GF2XModulus field(modulus);
    const ZZ order = (ZZ(1) << degree)-1;
    ZZ known(1);
    for (const char* decimal : {"47", "131009", "178481", "724639", "2529391927",
                                "70676429054711", "618970019642690137449562111"}) {
        const ZZ p = to_ZZ(decimal);
        if (order % p != 0 || IsOne(PowerXMod(order/p, field)))
            throw std::runtime_error("known prime-index check failed");
        known *= p;
    }
    const ZZ cofactor = order/known;
    if (known*cofactor != order || !IsOne(GCD(known, cofactor)) || NumBytes(cofactor) != width)
        throw std::runtime_error("invalid projection exponent");
    std::vector<Row> rows(n);
    unsigned previous = 0;
    for (auto& row : rows) {
        row.mask = read32();
        if (!std::cin.read(reinterpret_cast<char*>(row.bytes.data()), width))
            throw std::runtime_error("truncated projected logarithm");
        if (row.mask <= previous || row.mask < 2 || row.mask >= (2u << m)
                || ZZFromBytes(row.bytes.data(), width) >= cofactor)
            throw std::runtime_error("invalid mask order or exponent range");
        previous = row.mask;
    }
    if (std::cin.peek() != std::char_traits<char>::eof() || std::cin.bad())
        throw std::runtime_error("trailing data or stream error");

    // Fixed-base powering in radix 256. The other side uses NTL's PowerMod.
    std::vector<std::array<GF2X, 256>> powers(width);
    GF2X base = PowerXMod(known, field);
    for (auto& digit : powers) {
        set(digit[0]);
        for (unsigned j = 1; j < digit.size(); ++j) MulMod(digit[j], digit[j-1], base, field);
        for (unsigned k = 0; k < 8; ++k) SqrMod(base, base, field);
    }
    std::atomic<unsigned> bad_mask(0);
    #pragma omp parallel num_threads(jobs)
    {
        const GF2XModulus local_field(modulus);
        #pragma omp for schedule(static)
        for (unsigned i = 0; i < n; ++i) {
            const auto& row = rows[i];
            auto p = polynomial(row.mask);
            if (m % deg(p) || !IterIrredTest(p)) {
                bad_mask.store(row.mask);
                continue;
            }
            GF2X left;
            set(left);
            for (unsigned j = 0; j < width; ++j)
                if (row.bytes[j]) MulMod(left, left, powers[j][row.bytes[j]], local_field);
            if (left != PowerMod(p, known, local_field)) bad_mask.store(row.mask);
        }
    }
    if (bad_mask.load())
        throw std::runtime_error("field identity or irreducibility failed at mask "+std::to_string(bad_mask.load()));
    // All accepted masks are distinct irreducibles whose degree divides m.
    // There are exactly sum_{d|m} I_2(d) of these, computed independently here.
    std::vector<unsigned> counts(m+1);
    unsigned total = 0;
    for (int d = 1; d <= m; ++d) {
        unsigned elements = 1u << d;
        for (int e = 1; e < d; ++e) if (d % e == 0) elements -= e*counts[e];
        counts[d] = elements/d;
        if (m % d == 0) total += counts[d];
    }
    if (total != n) throw std::runtime_error("incomplete factor base");
    std::cout << "Verified all " << n << " projected logarithms for degrees dividing " << m
              << " at the root of T^2047 + T^511 + 1.\n";
}
}

int main(int argc, char** argv) {
    try {
        int jobs = argc == 2 ? std::stoi(argv[1]) : 1;
        if (jobs < 1 || argc > 2) throw std::invalid_argument("usage: verify_2047_ore_logs [THREADS]");
        verify(jobs);
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
