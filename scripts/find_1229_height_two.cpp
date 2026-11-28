// Search X^(2q+1)+X^(q+1)+vX+u over binary constant fields for a degree-1229 factor.
#include <NTL/GF2EXFactoring.h>
#include <array>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace NTL;
constexpr int q = 1024, parent_degree = 2 * q + 1, target_degree = 1229;

GF2X binary(int mask) {
    GF2X f;
    for (int i = 0; mask; mask >>= 1, ++i)
        if (mask & 1)
            SetCoeff(f, i);
    return f;
}

int encoding(const GF2E &z) {
    int mask = 0;
    for (int i = 0; i <= deg(rep(z)); ++i)
        if (IsOne(coeff(rep(z), i)))
            mask |= 1 << i;
    return mask;
}

int constant_modulus(int s) {
    switch (s) {
    case 1:
        return 3;
    case 2:
        return 7;
    case 4:
        return 19;
    case 5:
        return 37;
    case 10:
        return 1033;
    default:
        throw std::invalid_argument("choose constant degree 1, 2, 4, 5 or 10");
    }
}

class Search {
    using Slices = std::vector<GF2X>;
    using Columns = std::array<std::vector<int>, 10>;
    int s, size;
    std::vector<int> squares;
    std::vector<std::vector<int>> products;

  public:
    explicit Search(int degree)
        : s(degree), size(1 << degree), squares(size), products(size, std::vector<int>(size)) {
        int modulus = constant_modulus(s);
        GF2E::init(binary(modulus));
        for (int i = 0; i < size; ++i)
            for (int j = 0; j < size; ++j) {
                int a = i, b = j, r = 0;
                while (b) {
                    if (b & 1)
                        r ^= a;
                    b >>= 1;
                    a <<= 1;
                    if (a & size)
                        a ^= modulus;
                }
                products[i][j] = r;
            }
        for (int i = 0; i < size; ++i)
            squares[i] = products[i][i];
    }
    bool representative(int u, int v) const {
        int a = u, b = v;
        for (int i = 0; i < s; ++i) {
            a = squares[a];
            b = squares[b];
            if (a * size + b < u * size + v)
                return false;
        }
        return true;
    }
    GF2EX factor(int u, int v) const {
        // Each binary slice is one coefficient of the polynomial basis of F_(2^s).
        Columns square_to, u_to, v_to;
        for (int i = 0; i < s; ++i)
            for (int j = 0; j < s; ++j) {
                if (squares[1 << i] & (1 << j))
                    square_to[i].push_back(j);
                if (products[u][1 << i] & (1 << j))
                    u_to[i].push_back(j);
                if (products[v][1 << i] & (1 << j))
                    v_to[i].push_back(j);
            }
        Slices f(s), tmp(s), high(s), shifted(s);
        SetX(f[0]);
        for (int it = 0; it < s * target_degree; ++it) {
            for (int i = 0; i < s; ++i) {
                sqr(tmp[i], f[i]);
                clear(f[i]);
            }
            for (int i = 0; i < s; ++i)
                for (int j : square_to[i])
                    f[j] += tmp[i];
            // Reduce X^(2q+1) to X^(q+1)+vX+u. Two passes reduce every square below 2q+1.
            for (int pass = 0; pass < 2; ++pass) {
                for (int i = 0; i < s; ++i) {
                    RightShift(high[i], f[i], parent_degree);
                    trunc(f[i], f[i], parent_degree);
                    LeftShift(shifted[i], high[i], 1);
                }
                for (int i = 0; i < s; ++i) {
                    LeftShift(tmp[i], high[i], q + 1);
                    f[i] += tmp[i];
                    for (int j : u_to[i])
                        f[j] += high[i];
                    for (int j : v_to[i])
                        f[j] += shifted[i];
                }
            }
        }
        f[0] += GF2X(1, 1);
        GF2EX residue, parent, x;
        SetX(x);
        SetCoeff(parent, parent_degree, 1);
        SetCoeff(parent, q + 1, 1);
        SetCoeff(parent, 1, to_GF2E(binary(v)));
        SetCoeff(parent, 0, to_GF2E(binary(u)));
        for (int j = 0; j < parent_degree; ++j) {
            int c = 0;
            for (int i = 0; i < s; ++i)
                if (IsOne(coeff(f[i], j)))
                    c |= 1 << i;
            if (c)
                SetCoeff(residue, j, to_GF2E(binary(c)));
        }
        // 1229 is prime. This gcd has only linear factors and factors of degree 1229.
        GF2EX candidate = GCD(parent, residue);
        if (deg(candidate) < target_degree)
            return GF2EX();
        candidate /= GCD(candidate, power(x, size) + x);
        if (deg(candidate) != target_degree || !IsOne(LeadCoeff(candidate)) ||
            !IsZero(parent % candidate) || !IterIrredTest(candidate))
            throw std::logic_error("degree-1229 factor check failed");
        return candidate;
    }
};
int scan(int s, int start, int count) {
    constant_modulus(s);
    int size = 1 << s;
    if (start < 0 || count < 1 || start >= size * size || count > size * size - start)
        throw std::invalid_argument("search interval outside the parameter square");
    Search search(s);
    int canonical = 0, hits = 0;
    for (int i = start; i < start + count; ++i) {
        int u = i / size, v = i % size;
        if (!u || !search.representative(u, v))
            continue;
        ++canonical;
        GF2EX found = search.factor(u, v);
        if (IsZero(found))
            continue;
        ++hits;
        std::cout << s << ' ' << u << ' ' << v;
        for (int j = 0; j <= target_degree; ++j)
            std::cout << ' ' << encoding(coeff(found, j));
        std::cout << '\n';
    }
    std::cerr << "F_(2^" << s << "): checked " << canonical << " Frobenius orbits, found " << hits
              << " factors.\n";
    return hits;
}
int main(int argc, char **argv) {
    try {
        if (argc == 2 && std::string(argv[1]) == "--small-fields") {
            for (int s : {1, 2, 4, 5})
                if (scan(s, 0, 1 << (2 * s)))
                    throw std::logic_error("unexpected small-field model");
        } else if (argc == 4) {
            scan(std::stoi(argv[1]), std::stoi(argv[2]), std::stoi(argv[3]));
        } else
            throw std::invalid_argument("use --small-fields or CONSTANT_DEGREE START COUNT");
        return 0;
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
