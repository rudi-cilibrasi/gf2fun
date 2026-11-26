// Find and verify degree-halving pencils in the certified q = 1024 model.
#include <NTL/GF2EXFactoring.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>

#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <sstream>
#include <stdexcept>
#include <string>
#include <vector>

using namespace NTL;
using Matrix = std::array<GF2E, 4>;
using Edges = std::map<ZZ, std::array<long, 2>>;

GF2X from_integer(const ZZ& z) {
    std::vector<unsigned char> bytes(NumBytes(z));
    BytesFromZZ(bytes.data(), z, bytes.size());
    return GF2XFromBytes(bytes.data(), bytes.size());
}

ZZ as_integer(const GF2X& p) {
    std::vector<unsigned char> bytes(NumBytes(p));
    BytesFromGF2X(bytes.data(), p, bytes.size());
    return ZZFromBytes(bytes.data(), bytes.size());
}

GF2E frobenius(GF2E x, long bits) {
    for (long i = 0; i < bits; ++i) sqr(x, x);
    return x;
}

// Gaussian elimination over F_2 with preimages retained in the original binary basis.
class LinearImage {
    std::vector<GF2X> images, preimages;
public:
    explicit LinearImage(long degree) : images(degree), preimages(degree) {}

    bool insert(GF2X y, GF2X x) {
        while (!IsZero(y)) {
            long pivot = deg(y);
            if (IsZero(images[pivot])) {
                images[pivot] = y;
                preimages[pivot] = x;
                return true;
            }
            y += images[pivot];
            x += preimages[pivot];
        }
        return false;
    }

    bool solve(GF2X y, GF2E& solution) const {
        GF2X x;
        while (!IsZero(y)) {
            long pivot = deg(y);
            if (IsZero(images[pivot])) return false;
            y += images[pivot];
            x += preimages[pivot];
        }
        solution = to_GF2E(x);
        return true;
    }

    // Both the reduced remainder and the chosen preimage are binary-linear in y.
    GF2X remainder(GF2X y, GF2E& preimage) const {
        GF2X x, missing;
        while (!IsZero(y)) {
            long pivot = deg(y);
            if (IsZero(images[pivot])) {
                SetCoeff(missing, pivot);
                SetCoeff(y, pivot, 0);
            } else {
                y += images[pivot];
                x += preimages[pivot];
            }
        }
        preimage = to_GF2E(x);
        return missing;
    }
};

GF2EX linear(const GF2E& a, const GF2E& b) {
    GF2EX p;
    SetCoeff(p, 1, a);
    SetCoeff(p, 0, b);
    return p;
}

struct QuadraticTarget {
    long m;
    GF2E alpha, conjugate;
    GF2EX h0, h1, quadratic;

    explicit QuadraticTarget(long degree) : m(degree / 2), alpha(to_GF2E(GF2X(1, 1))),
                                            conjugate(frobenius(alpha, m)) {
        GF2EX x;
        SetX(x);
        h0 = power(x, 5) + sqr(x) + 1;
        h1 = power(x, 3) + x;
        quadratic = (x + alpha) * (x + conjugate);
    }

    // The determinant pencil at x becomes this numerator at y = x^1024.
    bool split_residual(const Matrix& matrix, GF2EX& residual) const {
        const auto& [a, b, c, d] = matrix;
        if (IsZero(a*d + b*c)) return false;
        GF2EX numerator = (a*h0 + b*h1) * linear(frobenius(c, 10), frobenius(d, 10))
                        + (c*h0 + d*h1) * linear(frobenius(a, 10), frobenius(b, 10));
        GF2EX rem;
        DivRem(residual, rem, numerator, quadratic);
        if (!IsZero(rem) || IsZero(residual)) return false;
        MakeMonic(residual);
        if (deg(residual) < 2) return true;
        GF2EXModulus mod(residual);
        GF2EX x;
        SetX(x);
        GF2EX fixed = x;
        for (long i = 0; i < m; ++i) SqrMod(fixed, fixed, mod);
        return fixed == x;
    }
};

// The projectivity taking the ordered triple (x, xb, y) to (0, infinity, 1).
Matrix triple_coordinates(const GF2E& x, const GF2E& xb, const GF2E& y) {
    return {y+xb, x*(y+xb), y+x, xb*(y+x)};
}

Matrix match_triples(const Matrix& input, const Matrix& output) {
    const auto& [a,b,c,d] = input;
    const auto& [e,f,g,h] = output;
    Matrix result{h*a+f*c, h*b+f*d, g*a+e*c, g*b+e*d};
    for (const auto& entry : result) {
        if (!IsZero(entry)) {
            const GF2E scale = inv(entry);
            for (auto& value : result) value *= scale;
            return result;
        }
    }
    throw std::logic_error("singular triple");
}

GF2E scalar_generator(long degree);

long find_pencil(const QuadraticTarget& target, long start, long count, bool lines, Matrix& result) {
    const long m = target.m;
    const GF2E gamma = frobenius(target.alpha, 2*m-10);
    const GF2E beta = eval(target.h0, target.alpha) / eval(target.h1, target.alpha);
    const GF2E gamma_bar = frobenius(gamma, m), beta_bar = frobenius(beta, m);
    const GF2E step = gamma + gamma_bar;
    if (IsZero(step*(beta+beta_bar)*(beta+gamma)*(beta+gamma_bar))) return 0;
    const GF2E invariant = (gamma+beta)*(gamma_bar+beta_bar)/(step*(beta+beta_bar));
    const GF2E theta = gamma/step, eta = sqr(theta)+theta, xi = frobenius(theta, 10)+theta;
    const Matrix input = triple_coordinates(gamma, gamma_bar, beta);

    LinearImage basis(2*m), artin_schreier(2*m), q_difference(2*m);
    GF2E a(1), ab(1);
    long rank = 0;
    for (long i = 0; i < 2*m; ++i, a *= target.alpha, ab *= target.conjugate) {
        GF2E v = a+ab;
        if (!basis.insert(rep(v), rep(v))) continue;
        ++rank;
        artin_schreier.insert(rep(sqr(v)+v), rep(v));
        q_difference.insert(rep(frobenius(v, 10)+v), rep(v));
    }
    if (rank != m) throw std::logic_error("wrong fixed-field dimension");

    GF2E v = power(step, start), vq = frobenius(v, 10);
    const GF2E stepq = frobenius(step, 10);
    std::vector<GF2E> scalars;
    if (lines) {
        GF2E z = scalar_generator(2*m), s(1);
        for (int i = 0; i < 10; ++i, s *= z) scalars.push_back(s);
    }
    for (long i = 0; i < count; ++i) {
        v *= step;
        vq *= stepq;
        GF2E delta = v+vq, w, u, shift;
        if (IsZero(delta)) continue;
        GF2E weight = invariant/sqr(delta);
        if (lines) {
            // On v + F_q the difference delta is fixed, so both equations are binary-linear in s.
            auto obstruction = [&](const GF2E& b, const GF2E& f) {
                GF2E lift, unused;
                GF2X r = artin_schreier.remainder(rep(b), lift);
                return r + (q_difference.remainder(rep(delta*lift + f), unused) << (2*m));
            };
            LinearImage choices(4*m);
            for (const auto& s : scalars)
                choices.insert(obstruction(weight*(sqr(s)+delta*s), s*xi), rep(s));
            if (!choices.solve(obstruction(eta+weight*v*vq, vq*xi), shift)) continue;
        }
        GF2E value = v+shift, conjugate_q = vq+shift;
        if (!artin_schreier.solve(rep(eta + weight*value*conjugate_q), w)) continue;
        if (!q_difference.solve(rep(delta*w + conjugate_q*xi), u)) continue;
        GF2E t = value*theta+u, tq = frobenius(t, 10), tb = t+value;
        if (tq == t || tq == tb) continue;
        result = match_triples(input, triple_coordinates(t, tb, tq));
        for (const auto& z : result)
            if (frobenius(z, m) != z) throw std::logic_error("matrix outside the fixed field");
        GF2EX residual;
        if (target.split_residual(result, residual)) return start+i+1;
    }
    return 0;
}

GF2E scalar_generator(long degree) {
    const ZZ exponent = (power2_ZZ(degree)-1)/1023;
    for (long i = 2; ; ++i) {
        GF2E a = power(to_GF2E(from_integer(to_ZZ(i))), exponent);
        if (!IsOne(power(a, 1023/3)) && !IsOne(power(a, 1023/11)) && !IsOne(power(a, 1023/31)))
            return a;
    }
}

Edges expand(const QuadraticTarget& target, const Matrix& matrix) {
    for (const auto& entry : matrix)
        if (frobenius(entry, target.m) != entry) throw std::invalid_argument("coefficient outside fixed field");
    GF2EX residual;
    if (!target.split_residual(matrix, residual)) throw std::invalid_argument("invalid quadratic pencil");
    const auto& [a,b,c,d] = matrix;
    const GF2XModulus field(GF2E::modulus());
    Edges edges;
    auto record = [&](const GF2E& z, int side) {
        GF2X p = MinPolyMod(rep(z), field, target.m);
        if (target.m % deg(p)) throw std::logic_error("incorrect minimal-polynomial degree");
        edges[as_integer(p)][side] += target.m/deg(p);
    };
    const auto roots = FindRoots(residual);
    if (roots.length() != std::max(0L, deg(residual))) throw std::logic_error("incomplete residual");
    for (const auto& root : roots) {
        if (frobenius(root, target.m) != root || !IsZero(eval(residual, root)))
            throw std::logic_error("invalid residual root");
        record(root, 1);
    }
    auto finite_preimage = [&](const GF2E& slope) {
        GF2E denominator = a + slope*c;
        if (!IsZero(denominator)) record((b+slope*d)/denominator, 0);
    };
    finite_preimage(GF2E(0));
    const GF2E generator = scalar_generator(2*target.m);
    GF2E slope(1);
    for (long i = 0; i < 1023; ++i, slope *= generator) finite_preimage(slope);
    if (!IsOne(slope)) throw std::logic_error("incorrect scalar group");
    if (!IsZero(c)) record(d/c, 0);
    return edges;
}

void verify_field_identity(const GF2X& parent, const Edges& edges, const GF2XModulus& model) {
    GF2X source(0,1), residual(0,1);
    for (const auto& [mask, multiplicity] : edges) {
        const GF2X child = from_integer(mask) % model.f;
        auto multiply = [&](GF2X& product, long e) {
            if (e == 1) MulMod(product, product, child, model);
            else if (e > 1) MulMod(product, product, PowerMod(child, e, model), model);
        };
        multiply(source, multiplicity[0]);
        multiply(residual, multiplicity[1]);
    }
    GF2X lhs = MulMod(parent % model.f, residual, model);
    for (int i = 0; i < 10; ++i) SqrMod(lhs, lhs, model);
    GF2X h1 = GF2X(3,1) + GF2X(1,1);
    GF2X rhs = MulMod(PowerMod(h1, 1024*(deg(parent)/2), model), source, model);
    if (lhs != rhs) throw std::logic_error("degree-1229 field identity failed");
}

int run(int argc, char** argv) {
    std::string mode = argc > 1 ? argv[1] : "";
    bool finding = mode == "find" || mode == "find-lines";
    if ((finding && argc != 4) || (!finding && (argc != 2 || (mode != "expand" && mode != "verify"))))
        throw std::invalid_argument("use find or find-lines with START COUNT, expand, or verify");
    long start = 0, count = 0;
    GF2XModulus model;
    if (finding) {
        start = std::stol(argv[2]);
        count = std::stol(argv[3]);
        if (start < 0 || count < 1 || start > std::numeric_limits<long>::max()-count)
            throw std::invalid_argument("invalid search interval");
    } else {
        ZZ modulus;
        if (!(std::cin >> modulus) || modulus <= 0) throw std::invalid_argument("missing model modulus");
        GF2X f = from_integer(modulus);
        if (deg(f) != 1229 || !IterIrredTest(f)) throw std::invalid_argument("invalid degree-1229 field");
        build(model, f);
    }
    ZZ mask;
    while (std::cin >> mask) {
        if (mask <= 0) throw std::invalid_argument("invalid binary mask");
        GF2X parent = from_integer(mask);
        if (deg(parent) < 40 || deg(parent) % 40 || !IterIrredTest(parent))
            throw std::invalid_argument("expected a binary irreducible of degree divisible by 40");
        GF2E::init(parent);
        QuadraticTarget target(deg(parent));
        Matrix matrix;
        if (finding) {
            long index = find_pencil(target, start, count, mode == "find-lines", matrix);
            if (!index) return 1;
            std::cout << mask << " " << index;
            for (const auto& entry : matrix) std::cout << " " << as_integer(rep(entry));
            std::cout << '\n';
        } else {
            for (auto& entry : matrix) {
                ZZ value;
                if (!(std::cin >> value) || value < 0 || NumBits(value) > deg(parent))
                    throw std::invalid_argument("invalid matrix entry");
                entry = to_GF2E(from_integer(value));
            }
            Edges edges = expand(target, matrix);
            verify_field_identity(parent, edges, model);
            long maximum = 0;
            for (const auto& [child, multiplicity] : edges) {
                long d = NumBits(child)-1;
                maximum = std::max(maximum, d/GCD(d, 20L));
                if (mode == "expand") std::cout << mask << " " << child << " "
                                                << multiplicity[0] << " " << multiplicity[1] << '\n';
            }
            if (mode == "verify") std::cout << mask << " " << edges.size() << " " << maximum << '\n';
        }
    }
    if (!std::cin.eof()) throw std::invalid_argument("invalid input");
    return 0;
}

int main(int argc, char** argv) {
    try {
        return run(argc, argv);
    } catch (const std::exception& e) {
        std::cerr << e.what() << '\n';
        return 2;
    }
}
