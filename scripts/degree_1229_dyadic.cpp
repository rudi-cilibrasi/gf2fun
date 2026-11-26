// Find and verify degree-halving pencils in the certified q = 1024 model.
#include <NTL/GF2EXFactoring.h>
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>

#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
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

// A four-bit lookup table for repeated reduction against the same binary pivots.
// Rows contain the remainder followed, when requested, by the chosen preimage.
class ReductionTable {
    long words, columns, blocks;
    std::vector<unsigned long> data;

    unsigned long* row(long block, long value) {
        return data.data() + (16*block+value)*columns;
    }
public:
    ReductionTable(const LinearImage& image, long n, bool preimages)
        : words((n+NTL_BITS_PER_LONG-1)/NTL_BITS_PER_LONG), columns(preimages ? 2*words : words),
          blocks((n+3)/4), data(16*blocks*columns) {
        for (long block = 0; block < blocks; ++block) {
            for (long bit = 0; bit < 4 && 4*block+bit < n; ++bit) {
                GF2E pre;
                GF2X rem = image.remainder(GF2X(4*block+bit, 1), pre);
                auto* base = row(block, 1L<<bit);
                for (long j = 0; j < rem.xrep.length(); ++j) base[j] = rem.xrep[j];
                if (preimages)
                    for (long j = 0; j < rep(pre).xrep.length(); ++j) base[words+j] = rep(pre).xrep[j];
            }
            for (long value = 1; value < 16; ++value) {
                long lower = value & (value-1);
                if (!lower) continue;
                auto* dst = row(block, value);
                auto* a = row(block, lower);
                auto* b = row(block, value-lower);
                for (long j = 0; j < columns; ++j) dst[j] = a[j]^b[j];
            }
        }
    }

    GF2X apply(const GF2X& value, GF2E* preimage) const {
        std::vector<unsigned long> result(columns);
        for (long word = 0; word < value.xrep.length(); ++word) {
            unsigned long bits = value.xrep[word];
            long block = word*(NTL_BITS_PER_LONG/4);
            while (bits) {
                const auto* entry = data.data() + (16*block+(bits&15))*columns;
                for (long j = 0; j < columns; ++j) result[j] ^= entry[j];
                bits >>= 4;
                ++block;
            }
        }
        GF2X out;
        out.xrep.SetLength(words);
        if (preimage) {
            std::copy_n(result.data()+words, words, out.xrep.elts());
            out.normalize();
            *preimage = to_GF2E(out);
            out.xrep.SetLength(words);
        }
        std::copy_n(result.data(), words, out.xrep.elts());
        out.normalize();
        return out;
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
    ZZ cube_root_exponent;

    explicit QuadraticTarget(long degree) : m(degree / 2), alpha(to_GF2E(GF2X(1, 1))),
                                            conjugate(frobenius(alpha, m)) {
        GF2EX x;
        SetX(x);
        h0 = power(x, 5) + sqr(x) + 1;
        h1 = power(x, 3) + x;
        quadratic = (x + alpha) * (x + conjugate);
        const ZZ cubes = (power2_ZZ(m)-1)/3;
        if (cubes % 3 != 0) cube_root_exponent = InvMod(to_ZZ(3), cubes);
    }

    // The cubic resolvent gives a partition into two quadratics. The remaining
    // tests are Artin--Schreier equations over the fixed field of size 2^m.
    bool split_quartic(const GF2EX& f, const LinearImage& image) const {
        const GF2E a = coeff(f,3), b = coeff(f,2), c = coeff(f,1), d = coeff(f,0);
        const GF2E g = sqr(b)+a*c, h = sqr(a)*d+sqr(c)+a*b*c;
        if (IsZero(h)) return false;
        GF2E z;
        if (!image.solve(rep(sqr(g)*g/sqr(h)), z)) return false;
        GF2E w = IsZero(z) ? h : h*z;
        GF2E u = power(w, cube_root_exponent);
        if (sqr(u)*u != w) return false;
        const GF2E y = b+u+g/u;
        if (!image.solve(rep((b+y)/sqr(a)), z)) return false;
        const GF2E p = a*z, s = a+p, r = (c+p*y)/a, t = y+r;
        if (IsZero(p*s) || r*t != d) return false;
        return image.solve(rep(r/sqr(p)), z) && image.solve(rep(t/sqr(s)), z);
    }

    // The determinant pencil at x becomes this numerator at y = x^1024.
    bool split_residual(const Matrix& matrix, GF2EX& residual, const LinearImage* image = nullptr) const {
        const auto& [a, b, c, d] = matrix;
        if (IsZero(a*d + b*c)) return false;
        GF2EX numerator = (a*h0 + b*h1) * linear(frobenius(c, 10), frobenius(d, 10))
                        + (c*h0 + d*h1) * linear(frobenius(a, 10), frobenius(b, 10));
        GF2EX rem;
        DivRem(residual, rem, numerator, quadratic);
        if (!IsZero(rem) || IsZero(residual)) return false;
        MakeMonic(residual);
        if (deg(residual) < 2) return true;
        if (image && deg(residual) == 4 && !IsZero(coeff(residual,3)) && !IsZero(cube_root_exponent))
            return split_quartic(residual, *image);
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
    std::unique_ptr<ReductionTable> lift_table, trace_table;
    if (lines) {
        GF2E z = scalar_generator(2*m), s(1);
        for (int i = 0; i < 10; ++i, s *= z) scalars.push_back(s);
        if (count > 10 && 2*m <= 320) {
            lift_table = std::make_unique<ReductionTable>(artin_schreier, 2*m, true);
            trace_table = std::make_unique<ReductionTable>(q_difference, 2*m, false);
        }
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
                GF2X r = lift_table ? lift_table->apply(rep(b), &lift) : artin_schreier.remainder(rep(b), lift);
                GF2E rhs = delta*lift + f;
                GF2X s = trace_table ? trace_table->apply(rep(rhs), nullptr) : q_difference.remainder(rep(rhs), unused);
                return r + (s << (2*m));
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
        GF2EX residual;
        if (target.split_residual(result, residual, &artin_schreier)) {
            for (const auto& z : result)
                if (frobenius(z, m) != z) throw std::logic_error("matrix outside the fixed field");
            return start+i+1;
        }
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

// Enumerate the projective linear Hermitian forms containing an absolute-degree-40 target.
// Here the half field is exactly F_(q^2), so the remaining source logarithms are known.
void terminal_circles(const ZZ& mask) {
    GF2E x = to_GF2E(GF2X(1,1)), xb = frobenius(x, 20);
    GF2E y = (power(x,5)+sqr(x)+1)/(power(x,3)+x), yb = frobenius(y,20);
    GF2E s = y+yb, t = x+xb, h = x*y+xb*yb;
    GF2E sq = frobenius(s,10), tq = frobenius(t,10), det = s*sq+t*tq;
    auto test = [&](const GF2E& a, const GF2E& b) {
        GF2E bq = frobenius(b,10), d = a*x*y+b*y+bq*x;
        if (frobenius(d,10) != d) return;
        QuadraticTarget target(40);
        GF2EX f = target.h0*linear(a,b) + target.h1*linear(bq,d), cofactor, rem;
        DivRem(cofactor, rem, f, target.quadratic);
        if (!IsZero(rem) || IsZero(cofactor)) throw std::logic_error("invalid terminal form");
        while (divide(cofactor, target.quadratic)) cofactor /= target.quadratic;
        MakeMonic(cofactor);
        if (deg(cofactor) > 0) {
            for (const auto& item : CanZass(cofactor))
                if (deg(item.a) != 1 || frobenius(ConstTerm(item.a),20) != ConstTerm(item.a)) return;
        }
        std::cout << mask << " " << as_integer(rep(a)) << " " << as_integer(rep(b))
                  << " " << as_integer(rep(d)) << '\n';
    };
    if (!IsZero(det)) {
        test(GF2E(1), (sq*h+t*frobenius(h,10))/det);
        return;
    }
    // When the norm difference vanishes the kernel for b is the F_q-line through b1.
    GF2E mu = s/t, b1 = IsOne(mu) ? GF2E(1) : GF2E(1)+inv(mu);
    test(GF2E(0), b1);
    GF2E value = h/(b1*s);
    if (frobenius(value,10) != value) return;
    GF2E u = x, ub = xb;
    while (u+ub == frobenius(u+ub,10)) { u *= x; ub *= xb; }
    GF2E epsilon = (u+ub)/((u+ub)+frobenius(u+ub,10));
    GF2E b0 = b1*value*epsilon;
    GF2E d0 = x*y+b0*y+frobenius(b0,10)*x, d1 = b1*y+frobenius(b1,10)*x;
    GF2E e0 = d0+frobenius(d0,10), e1 = d1+frobenius(d1,10);
    if (!IsZero(e1)) {
        test(GF2E(1), b0+b1*(e0/e1));
    } else if (IsZero(e0)) {
        test(GF2E(1), b0);
        GF2E scalar(1), generator = scalar_generator(40);
        for (long i = 0; i < 1023; ++i, scalar *= generator) test(GF2E(1), b0+b1*scalar);
    }
}

int run(int argc, char** argv) {
    std::string mode = argc > 1 ? argv[1] : "";
    bool finding = mode == "find" || mode == "find-lines";
    bool terminal = mode == "terminal", replay = mode == "replay-lines" || mode == "expand-lines";
    if ((finding && argc != 4) ||
        (!finding && (argc != 2 || (!terminal && !replay && mode != "expand" && mode != "verify"))))
        throw std::invalid_argument("use find or find-lines with START COUNT, expand, verify, "
                                    "replay-lines, expand-lines, or terminal");
    long start = 0, count = 0;
    GF2XModulus model;
    if (finding) {
        start = std::stol(argv[2]);
        count = std::stol(argv[3]);
        if (start < 0 || count < 1 || start > std::numeric_limits<long>::max()-count)
            throw std::invalid_argument("invalid search interval");
    } else if (!terminal) {
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
        if (terminal) {
            if (deg(parent) != 40) throw std::invalid_argument("terminal requires binary degree 40");
            terminal_circles(mask);
            continue;
        }
        QuadraticTarget target(deg(parent));
        Matrix matrix;
        if (finding) {
            long index = find_pencil(target, start, count, mode == "find-lines", matrix);
            if (!index) return 1;
            std::cout << mask << " " << index;
            for (const auto& entry : matrix) std::cout << " " << as_integer(rep(entry));
            std::cout << '\n';
        } else {
            if (replay) {
                long step;
                if (!(std::cin >> step) || step < 1 ||
                    find_pencil(target, step-1, 1, true, matrix) != step)
                    throw std::invalid_argument("invalid pencil index");
                GF2EX residual;
                if (!target.split_residual(matrix, residual)) throw std::logic_error("quartic failed to split");
                if (mode == "replay-lines") {
                    const auto& [a,b,c,d] = matrix;
                    bool infinity = IsZero(c) || frobenius(a,10)*c == a*frobenius(c,10);
                    std::cout << mask << " " << 1025-infinity+deg(residual) << " " << target.m/20 << '\n';
                    continue;
                }
            } else {
                for (auto& entry : matrix) {
                    ZZ value;
                    if (!(std::cin >> value) || value < 0 || NumBits(value) > deg(parent))
                        throw std::invalid_argument("invalid matrix entry");
                    entry = to_GF2E(from_integer(value));
                }
            }
            Edges edges = expand(target, matrix);
            verify_field_identity(parent, edges, model);
            long maximum = 0;
            for (const auto& [child, multiplicity] : edges) {
                long d = NumBits(child)-1;
                maximum = std::max(maximum, d/GCD(d, 20L));
                if (mode == "expand" || mode == "expand-lines")
                    std::cout << mask << " " << child << " " << multiplicity[0] << " " << multiplicity[1] << '\n';
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
