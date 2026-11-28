// Count norm circles with a completely split residual polynomial in the degree-3073 model.
#include "binary_circle_field.hpp"

#include <iostream>
#include <string>
#include <utility>

using Counts = std::vector<std::uint8_t>;

// For q=512 the parameter is the square root of the parameter used at q=1024.
std::pair<Word, Word> coordinates(const Field& f, Word z) {
    Word denominator = f.frobenius(z ^ 1, 1);
    Word x = f.mul(z, denominator);
    Word y = f.mul(z, f.exp[f.period - f.log[denominator]]);
    if (f.q == 512) x = f.frobenius(x, 1);
    if (f.q == 2048) y = f.frobenius(y, 1);
    return {x, y};
}

Word circle_value(const Field& f, Word b, Word x, Word y) {
    return f.mul(x, y) ^ f.mul(b, y) ^ f.mul(f.conjugate[b], x);
}

// For two centres, check all radii by evaluating the rational functions
// directly at every constant. This also checks proper-subfield orbits.
void check_centre(const Field& f, Word b, const Counts& counts) {
    Counts direct(f.q);
    for (Word z = 0; z < f.size; ++z) {
        if (z == 1) continue;
        auto [x, y] = coordinates(f, z);
        Word d = circle_value(f, b, x, y);
        if (f.conjugate[d] == d && d != f.mul(b, f.conjugate[b]))
            ++direct[f.real_index[d]];
    }
    for (Word j = 0; j < f.q; ++j)
        if (direct[j] != counts[f.orbit_id[b]*f.q + j])
            throw std::runtime_error("direct root count disagrees");
}

std::uint64_t count(const Field& f) {
    const unsigned degree = f.q == 512 ? 8 : (f.q == 1024 ? 5 : 7);
    Counts counts(f.representatives.size()*f.q);
    for (Word b : f.representatives)
        if (b) ++counts[f.orbit_id[b]*f.q];  // z=0 gives precisely d=0.

    for (Word z : f.representatives) {
        if (z <= 1) continue;
        auto [x, y] = coordinates(f, z);
        Word h = y ^ f.conjugate[x];
        if (!h) throw std::runtime_error("unexpected constant Frobenius solution");
        Word inverse = f.exp[f.period - f.log[h]];
        Word product = f.mul(x, y);
        for (Word u : f.real) {
            // The circle value is real exactly when xy+b(y+bar(x)) is real.
            Word b = f.mul(product ^ u, inverse);
            if (!b) continue;
            unsigned j = f.to_rep[b];
            if (j >= f.degree[z]) continue;
            Word d = circle_value(f, b, x, y);
            if (d == f.mul(b, f.conjugate[b])) continue;
            // Restore exactly the conjugate roots whose centre is the representative.
            for (; j < f.degree[z]; j += f.degree[b]) {
                Word index = f.real_index[f.frobenius(d, j)];
                if (index >= f.q || ++counts[f.orbit_id[b]*f.q + index] > degree)
                    throw std::runtime_error("invalid residual root count");
            }
        }
    }
    check_centre(f, 1, counts);
    check_centre(f, f.representatives.at(2), counts);
    std::uint64_t total = 0;
    for (Word b : f.representatives) {
        if (!b) continue;
        for (Word j = 0; j < f.q; ++j)
            if (counts[f.orbit_id[b]*f.q + j] == degree) total += f.degree[b];
    }
    return total;
}

int main(int argc, char** argv) {
    if (argc != 2 || (std::string(argv[1]) != "512" && std::string(argv[1]) != "1024"
                      && std::string(argv[1]) != "2048")) {
        std::cerr << "Usage: count_3073_circles {512|1024|2048}\n";
        return 2;
    }
    try {
        Field f(std::stoul(argv[1]));
        std::cout << "q=" << f.q << ", splitting circles=" << count(f) << '\n';
    } catch (const std::exception& error) {
        std::cerr << error.what() << '\n';
        return 1;
    }
}
