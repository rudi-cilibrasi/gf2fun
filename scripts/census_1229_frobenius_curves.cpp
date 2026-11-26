// Test whether the monomials X^i Y^j in a square are independent at (r,r^q).
// Input is the repository's decompressed degree-1229 support CSV.
#include <NTL/GF2X.h>
#include <array>
#include <iostream>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using namespace NTL;
constexpr unsigned degree = 1229;
constexpr std::array<unsigned, 4> fields{256, 512, 1024, 2048};
struct Support { unsigned a, b, c; };

bool dependent(const GF2XModulus& f, const std::vector<GF2X>& powers,
               unsigned stride, unsigned side) {
    std::array<int, degree> pivot;
    pivot.fill(-1);
    std::vector<GF2X> basis;
    basis.reserve((side+1)*(side+1));
    for (unsigned j = 0; j <= side; ++j) {
        GF2X x = powers[stride*j];
        for (unsigned i = 0; i <= side; ++i) {
            GF2X column = x;
            while (!IsZero(column)) {
                int k = pivot[deg(column)];
                if (k < 0) break;
                add(column, column, basis[k]);
            }
            if (IsZero(column)) return true;
            pivot[deg(column)] = static_cast<int>(basis.size());
            basis.push_back(std::move(column));
            if (i < side) MulByXMod(x, x, f);
        }
    }
    return false;
}

std::array<bool, 4> scan(Support taps, unsigned side) {
    GF2X polynomial;
    for (unsigned e : {0u, taps.a, taps.b, taps.c, degree}) SetCoeff(polynomial, e);
    const GF2XModulus f(polynomial);
    std::vector<GF2X> powers(8*side+1);
    set(powers.front());
    for (unsigned j = 1; j < powers.size(); ++j)
        rem(powers[j], powers[j-1] << 256, f);
    std::array<bool, 4> result{};
    for (unsigned k = 0; k < fields.size(); ++k)
        result[k] = dependent(f, powers, fields[k]/256, side);
    return result;
}

void census(unsigned side, int jobs) {
    std::string line;
    if (!std::getline(std::cin, line) || line != "a,b,c,missing_mask")
        throw std::runtime_error("unexpected support header");
    std::vector<Support> rows;
    while (std::getline(std::cin, line)) {
        Support s;
        unsigned missing;
        char u, v, w;
        std::istringstream row(line);
        if (!(row >> s.a >> u >> s.b >> v >> s.c >> w >> missing) ||
                u != ',' || v != ',' || w != ',' || !(0 < s.a && s.a < s.b && s.b < s.c && s.c < degree))
            throw std::runtime_error("invalid support row");
        row >> std::ws;
        if (!row.eof()) throw std::runtime_error("trailing data in support row");
        rows.push_back(s);
    }
    if (!std::cin.eof()) throw std::runtime_error("failed to read support table");
    std::vector<std::array<bool, 4>> hits(rows.size());
    #pragma omp parallel for num_threads(jobs) schedule(dynamic, 32)
    for (std::size_t i = 0; i < rows.size(); ++i) hits[i] = scan(rows[i], side);
    std::cout << "q,a,b,c\n";
    for (unsigned k = 0; k < fields.size(); ++k)
        for (std::size_t i = 0; i < rows.size(); ++i)
            if (hits[i][k]) std::cout << fields[k] << ',' << rows[i].a << ','
                                     << rows[i].b << ',' << rows[i].c << '\n';
    std::cerr << "Checked " << rows.size() << " supports at side " << side << " for all four q.\n";
}
}

int main(int argc, char** argv) {
    try {
        if (argc != 3) throw std::invalid_argument("usage: census_1229_frobenius_curves SIDE THREADS");
        int side = std::stoi(argv[1]), jobs = std::stoi(argv[2]);
        if (side < 1 || side > 34 || jobs < 1) throw std::invalid_argument("invalid side or thread count");
        census(side, jobs);
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
