// Count rational roots of every linear Hermitian pencil over F_(2^20).
// Binary Frobenius orbits of roots and coefficients keep the incidence table small.
#include <algorithm>
#include <array>
#include <NTL/GF2EXFactoring.h>
#include <map>
#include <fstream>
#include <iostream>
#include <numeric>
#include <stdexcept>
#include <string>
#include <vector>

constexpr int q = 1024, size = q * q, period = size - 1;
using Bin = std::array<int, 7>;
struct Field {
    std::vector<int> exp, log, square, bar, trace, norm, orbit, rotation, reps, length;
    std::array<int, q> real{};
    std::array<int, q + 1> torus{};
    std::array<std::array<int, q>, 20> rotate_real{}, canonical{};
    Field()
        : exp(2 * period + 1), log(size, -1), square(size), bar(size), trace(size), norm(size),
          orbit(size, -1), rotation(size) {
        int v = 1;
        for (int i = 0; i < period; i++) {
            if (log[v] != -1)
                throw std::logic_error("nonprimitive field generator");
            exp[i] = exp[period + i] = v;
            log[v] = i;
            v <<= 1;
            if (v & size)
                v ^= size + 9;
        }
        if (v != 1)
            throw std::logic_error("invalid field modulus");
        for (int i = 0; i < q - 1; i++)
            real[i] = exp[(q + 1) * i];
        for (int i = 0; i <= q; i++)
            torus[i] = exp[(q - 1) * i];
        for (int i = 1; i < size; i++) {
            square[i] = exp[2 * log[i]];
            bar[i] = exp[(static_cast<long>(log[i]) * q) % period];
            norm[i] = exp[(q + 1) * (log[i] % (q - 1))];
        }
        for (int i = 0; i < size; i++)
            if (orbit[i] < 0) {
                int n = 0, x = i;
                do {
                    orbit[x] = reps.size();
                    x = square[x];
                    n++;
                } while (x != i);
                x = i;
                for (int j = 0; j < n; j++, x = square[x])
                    rotation[x] = (n - j) % n;
                length.push_back(n);
                reps.push_back(i);
            }
        for (int i = 0; i < size; i++)
            trace[i] = i ^ bar[i];
        for (int k = 0; k < 20; k++)
            for (int i = 0; i < q; i++)
                rotate_real[k][i] = i == q - 1 ? i : (i * (1 << (k % 10))) % (q - 1);
        for (int k : {1, 2, 4, 5, 10, 20})
            for (int i = 0; i < q; i++) {
                int best = i;
                for (int j = k; j < 20; j += k)
                    best = std::min(best, rotate_real[j][i]);
                canonical[k % 20][i] = best;
            }
    }
    int mul(int a, int b) const {
        return a && b ? exp[log[a] + log[b]] : 0;
    }
    int inv(int a) const {
        if (!a)
            throw std::logic_error("division by zero");
        return exp[period - log[a]];
    }
    int di(int d) const {
        return d ? log[d] / (q + 1) : q - 1;
    }
    // Canonicalize (b,d) by squaring b to its representative, then following its stabilizer on d.
    int parameters(int b, int d) const {
        int i = orbit[b];
        return q * i + canonical[length[i] % 20][rotate_real[rotation[b]][di(d)]];
    }
    Bin polynomial(int a, int b, int d) const {
        return {b, a ^ d, b ^ bar[b], a ^ d, bar[b], b, a};
    }
    // At a known root evaluate the derivative first. Synthetic division handles a multiple root.
    int multiplicity(int a, int b, int d, int t, int t4, int square_plus_one) const {
        if (mul(b, t4) != mul(a ^ d, square_plus_one))
            return 1;
        Bin f = polynomial(a, b, d);
        int n = a ? 6 : 5, j = 0;
        while (n > 0) {
            Bin quot{};
            int lead = f[n];
            for (int k = n - 1; k >= 0; k--) {
                quot[k] = lead;
                lead = f[k] ^ mul(lead, t);
            }
            if (lead)
                break;
            f = quot;
            n--;
            j++;
        }
        if (!j)
            throw std::logic_error("point failed pencil incidence");
        return j;
    }
    bool repeated_quadratic(int a, int b, int d) const {
        if (!b || a == d)
            return false;
        // The square root of the derivative can contain at most one irreducible quadratic.
        int v = mul(a ^ d, inv(b));
        int z = exp[((static_cast<long>(log[v]) * (size / 2)) % period)];
        // The normalized square root of the derivative is T^2+z*T+z.
        int w = inv(z), tr = 0;
        for (int i = 0; i < 20; i++, w = square[w])
            tr ^= w;
        if (tr != 1)
            return false;
        auto f = polynomial(a, b, d);
        int hi = 0, lo = 0;
        for (int k = 6; k >= 0; k--) {
            int u = mul(hi, z);
            hi = lo ^ u;
            lo = f[k] ^ u;
        }
        return !hi && !lo;
    }
};

using namespace NTL;
// Coefficient norm of T+root down to the binary field of the root's orbit.
int binary_minimal(const Field &k, int root, int degree) {
    std::array<int, 21> coeff{};
    coeff[0] = 1;
    int t = root;
    for (int j = 0; j < degree; j++, t = k.square[t]) {
        for (int h = j + 1; h >= 0; h--)
            coeff[h] = (h ? coeff[h - 1] : 0) ^ k.mul(t, coeff[h]);
    }
    int result = 0;
    for (int j = 0; j <= degree; j++) {
        if (coeff[j] > 1)
            throw std::logic_error("nonbinary minimal polynomial");
        result |= coeff[j] << j;
    }
    return result;
}

// W(t) is the known logarithm of the 20-fold binary coefficient norm of T+t.
// For a norm circle the finite points are bar(b) + sqrt(d+N(b)) times the norm-one torus.
// For a trace line they satisfy Tr(b*t)=d.
class SourceLogs {
    const Field &k;
    NTL::ZZ modulus, iq, offset;
    std::vector<NTL::ZZ> weight;
    std::vector<int> circle_points;
    int epsilon = 0;

  public:
    SourceLogs(const Field &field, const char *path)
        : k(field), weight(k.reps.size()), circle_points(q * (q + 1)) {
        std::ifstream in(path);
        if (!(in >> modulus) || modulus <= 1)
            throw std::invalid_argument("invalid projected order");
        iq = NTL::InvMod(NTL::to_ZZ(q), modulus);
        std::map<int, NTL::ZZ> logs;
        int p;
        NTL::ZZ e;
        while (in >> p >> e) {
            if (e < 0 || e >= modulus || !logs.emplace(p, e).second)
                throw std::invalid_argument("invalid base logarithm");
        }
        if (!in.eof() || logs.size() != k.reps.size())
            throw std::invalid_argument("incomplete linear logarithm table");
        for (size_t i = 0; i < weight.size(); i++) {
            int deg = k.length[i];
            weight[i] = (logs.at(binary_minimal(k, k.reps[i], deg)) * (20 / deg)) % modulus;
        }
        offset = 20 * (logs.at(2) + 2 * logs.at(3));
        for (int i = 0; i < q - 1; i++) {
            int r = k.real[(i * (q / 2)) % (q - 1)];
            for (int j = 0; j <= q; j++)
                circle_points[i * (q + 1) + j] = k.mul(r, k.torus[j]);
        }
        for (int a = 2; !epsilon; a++)
            if (k.trace[a])
                epsilon = k.mul(a, k.inv(k.trace[a]));
    }
    NTL::ZZ exponent(int a, int b, int d, int mult, const std::vector<long> &roots) const {
        NTL::ZZ sum, rhs;
        if (a) {
            int rho = d ^ k.norm[b];
            int center = k.bar[b];
            if (rho) {
                int off = (q + 1) * k.di(rho);
                for (int j = 0; j <= q; j++)
                    sum += weight[k.orbit[center ^ circle_points[off + j]]];
            } else {
                sum = (q + 1) * weight[k.orbit[center]];
            }
        } else {
            int inv = k.inv(b), base = k.mul(epsilon, d);
            for (int s : k.real)
                sum += weight[k.orbit[k.mul(inv, base ^ s)]];
        }
        for (int r : roots)
            rhs += weight[k.orbit[r]];
        // h1(x)^(20q) times the source norm equals the q-power of the substituted norm.
        NTL::ZZ e = ((sum % modulus) * iq + offset - rhs) % modulus;
        if (mult != 1)
            e = NTL::MulMod(e, NTL::InvMod(NTL::to_ZZ(mult), modulus), modulus);
        return e;
    }
};
// Enumerate incidences from a rational root t to its pencils. A full Frobenius orbit of t
// contributes length(t) times its multiplicity to the orbit of each incident pencil.
void census(const Field &k, const char *path) {
    const auto &squares = k.square;
    int epsilon = 0;
    for (int a = 2; !epsilon; a++)
        if (k.trace[a])
            epsilon = k.mul(a, k.inv(k.trace[a]));
    std::vector<unsigned short> norms(k.reps.size() * q);
    std::vector<int> torus_index(k.reps.size(), -1), torus_reps;
    for (auto b : k.torus) {
        int j = k.orbit[b];
        if (torus_index[j] < 0) {
            torus_index[j] = torus_reps.size();
            torus_reps.push_back(j);
        }
    }
    std::vector<unsigned short> lines(torus_reps.size() * q);
    for (size_t j = 0; j < k.reps.size(); j++) {
        int t = k.reps[j], len = k.length[j], s = squares[t], t4 = squares[s];
        auto record = [&](int a, int b, int d) {
            if (!k.trace[d] && (!a || d != k.norm[b])) {
                int id = k.parameters(b, d), n = len * k.multiplicity(a, b, d, t, t4, s ^ 1);
                if (a)
                    norms[id] += n;
                else
                    lines[torus_index[id / q] * q + id % q] += n;
            } else if (k.trace[d])
                throw std::logic_error("parameter outside F_q");
        };
        if (t <= 1) {
            for (int d : k.real)
                record(1, t, d);
            continue;
        }
        int y = k.mul(k.mul(t4, t) ^ s ^ 1, k.inv(k.mul(s, t) ^ t));
        int prod = k.mul(t, y), u = y ^ k.bar[t];
        auto incidence = [&](int a, int b) {
            int d = (a ? prod : 0) ^ k.mul(b, y) ^ k.mul(k.bar[b], t);
            record(a, b, d);
        };
        // For a=1 the condition is Tr(b*u)=Tr(t*y), where y=R(t) and u=y+bar(t).
        // For a=0 it is Tr(b*u)=0, and b is normalized to the norm-one torus.
        if (!u) {
            for (int b = 0; b < size; b++)
                incidence(1, b);
            for (int b : k.torus)
                incidence(0, b);
        } else {
            int ui = k.inv(u), b0 = k.mul(ui, k.mul(epsilon, k.trace[prod]));
            for (int s0 : k.real)
                incidence(1, b0 ^ k.mul(s0, ui));
            // log(b*u) must be divisible by q+1. Since q-1=-2 mod q+1, divide log(u) by two.
            incidence(0, k.torus[(static_cast<long>(513) * k.log[u]) % (q + 1)]);
        }
    }
    std::ofstream out(path);
    if (!out)
        throw std::runtime_error("cannot open pencil list");
    long long count = 0, classes = 0, smooth = 0, rep = 0;
    std::array<long long, 7> distribution{};
    // If two degrees remain after the rational roots, they form an irreducible quadratic.
    // A repeated quadratic is the only other possible single nonlinear factor.
    auto finish = [&](int a, int j, const unsigned short *hist) {
        int b = k.reps[j], n = a ? 6 : 5, ell = k.length[j];
        for (int v = 0; v < q; v++) {
            int d = k.real[v];
            if (k.canonical[ell % 20][v] != v || (a && d == k.norm[b]))
                continue;
            int period_bd = std::lcm(ell, k.length[k.orbit[d]]);
            if (hist[v] % period_bd)
                throw std::logic_error("inconsistent incidence orbit");
            int l = hist[v] / period_bd;
            if (l > n)
                throw std::logic_error("excess rational roots");
            classes++;
            count += period_bd;
            distribution[l] += period_bd;
            bool repeated = l <= n - 4 && k.repeated_quadratic(a, b, d);
            if (l == n - 2 || repeated) {
                out << a << ' ' << b << ' ' << d << ' ' << period_bd << ' ' << l << '\n';
                if (l == n - 2)
                    smooth += period_bd;
                if (repeated)
                    rep += period_bd;
            }
        }
    };
    for (size_t j = 0; j < k.reps.size(); j++)
        finish(1, j, &norms[q * j]);
    for (size_t i = 0; i < torus_reps.size(); i++)
        finish(0, torus_reps[i], &lines[q * i]);
    if (count != static_cast<long long>(q) * q * q + q)
        throw std::logic_error("incomplete subline census");
    std::cout << count << " sublines in " << classes << " orbits. Rational multiplicity distribution:";
    for (auto c : distribution)
        std::cout << " " << c;
    std::cout << "\n"
              << smooth << " simple quadratic eliminations and " << rep
              << " additional pencils with repeated irreducible quadratic.\n";
}
// A nonrational quadratic point belongs to at most one nonsingular pencil. Distinct
// conjugate quadratic factors in one pencil therefore force a proper coefficient orbit.
// Rank-one forms are indexed separately by their single point in the projective line.
void supplement(const Field &k, const char *path) {
    std::ofstream out(path);
    if (!out)
        throw std::runtime_error("cannot open supplementary pencil list");
    for (size_t j = 0; j < k.reps.size(); j++) {
        int b = k.reps[j], ell = k.length[j];
        out << 1 << ' ' << b << ' ' << k.norm[b] << ' ' << ell << " -1\n";
        if (ell == 20)
            continue;
        for (int i = 0; i < q; i++) {
            int d = k.real[i], len = std::lcm(ell, k.length[k.orbit[d]]);
            if (k.canonical[ell % 20][i] != i || len == 20)
                continue;
            if (d != k.norm[b])
                out << 1 << ' ' << b << ' ' << d << ' ' << len << " -1\n";
            if (k.norm[b] == 1)
                out << 0 << ' ' << b << ' ' << d << ' ' << len << " -1\n";
        }
    }
    // The remaining rank-one form has constant source and substituted polynomial h1.
}
// Integer encodings place the constant binary coefficient in the least significant bit.
GF2X binary(long value) {
    GF2X r;
    for (int i = 0; value; value >>= 1, i++)
        if (value & 1)
            SetCoeff(r, i);
    return r;
}
long mask(const GF2X &f) {
    long r = 0;
    for (int j = 0; j <= deg(f); j++)
        if (IsOne(coeff(f, j)))
            r |= 1L << j;
    return r;
}
// In the charts T, 1/T and 1/(T+1), a pair with sum u and product v has sums
// u, u/v and u/(v+u+1). Their binary minimal polynomials identify each trace orbit.
void fiber_traces() {
    long p;
    while (std::cin >> p) {
        if (p <= 0)
            throw std::invalid_argument("invalid quadratic mask");
        GF2X f = binary(p), x(1, 1), conjugate = x;
        long n = deg(f);
        if ((n != 8 && n != 40) || !IterIrredTest(f))
            throw std::invalid_argument("expected a relative quadratic irreducible");
        GF2XModulus field(f);
        for (int i = 0; i < 20; ++i)
            SqrMod(conjugate, conjugate, field);
        GF2X u = x+conjugate, v = MulMod(x, conjugate, field);
        auto trace_mask = [&](const GF2X& denominator) {
            GF2X t = MulMod(u, InvMod(denominator, f), field);
            GF2X minimal = MinPolyMod(t, field);
            if (deg(minimal) <= 0 || (n/2) % deg(minimal) || 20 % deg(minimal))
                throw std::logic_error("unexpected relative trace degree");
            return mask(minimal);
        };
        std::cout << p << ' ' << trace_mask(GF2X(0, 1)) << ' ' << trace_mask(v)
                  << ' ' << trace_mask(v+u+1) << '\n';
    }
    if (!std::cin.eof())
        throw std::invalid_argument("invalid mask input");
}

std::pair<long, int> quadratic_norm(const GF2EX &target) {
    GF2EX prod(1), qb = target;
    int s = 0;
    do {
        prod *= qb;
        s++;
        SetCoeff(qb, 0, sqr(ConstTerm(qb)));
        SetCoeff(qb, 1, sqr(coeff(qb, 1)));
    } while (qb != target && s <= 20);
    if (s != 4 && s != 20)
        throw std::logic_error("unexpected quadratic orbit length");
    long p = 0;
    for (int j = 0; j <= deg(prod); j++) {
        if (IsOne(coeff(prod, j)))
            p |= 1L << j;
        else if (!IsZero(coeff(prod, j)))
            throw std::logic_error("nonbinary target");
    }
    return {p, 20 / s};
}

// Independently factor every candidate numerator over the constant field, then take the
// binary coefficient norm of its one quadratic, retaining the orbit multiplicity.
void factor(const SourceLogs *logs) {
    GF2E::init(binary((1 << 20) + 9));
    long a, b, d, orbit_size, l;
    while (std::cin >> a) {
        if (!(std::cin >> b >> d >> orbit_size >> l) || (a != 0 && a != 1) || b < 0 || b >= size || d < 0 ||
            d >= size || orbit_size < 0 || (orbit_size && 20 % orbit_size) || l < -1 || l > 6)
            throw std::invalid_argument("invalid projective pencil row");
        GF2E A = to_GF2E(binary(a)), B = to_GF2E(binary(b)), D = to_GF2E(binary(d)), bc = power(B, 1024);
        if (power(D, q) != D || (!a && IsZero(B)))
            throw std::invalid_argument("invalid Hermitian pencil");
        GF2EX f;
        std::array<GF2E, 7> coefficients{B, A + D, B + bc, A + D, bc, B, A};
        for (int j = 0; j < 7; j++)
            SetCoeff(f, j, coefficients[j]);
        MakeMonic(f);
        long p = 0;
        int mult = 0, rational = 0;
        bool single = true;
        std::vector<long> roots;
        for (const auto &fac : CanZass(f)) {
            if (deg(fac.a) == 1) {
                rational += fac.b;
                for (int j = 0; j < fac.b; j++)
                    roots.push_back(mask(rep(ConstTerm(fac.a))));
            } else if (deg(fac.a) == 2) {
                const auto [binary_mask, norm_mult] = quadratic_norm(fac.a);
                if (p && p != binary_mask)
                    single = false;
                p = binary_mask;
                mult += fac.b * norm_mult;
            } else
                single = false;
        }
        if (l >= 0 && rational != l)
            throw std::logic_error("rational-root census mismatch");
        if (!single || !p) {
            if (l == deg(f) - 2)
                throw std::logic_error("smoothness census mismatch");
            continue;
        }
        std::cout << p << ' ' << a << ' ' << b << ' ' << d;
        if (logs)
            std::cout << ' ' << logs->exponent(a, b, d, mult, roots);
        else {
            std::cout << ' ' << mult << ' ' << rational;
            for (long t : roots)
                std::cout << ' ' << t;
        }
        std::cout << '\n';
    }
    if (!std::cin.eof())
        throw std::invalid_argument("invalid input row");
}

int main(int argc, char **argv) {
    try {
        const std::string mode = argc > 1 ? argv[1] : "";
        if (mode == "scan" && argc == 3)
            census(Field(), argv[2]);
        else if (mode == "supplement" && argc == 3)
            supplement(Field(), argv[2]);
        else if (mode == "factor" && argc == 2)
            factor(nullptr);
        else if (mode == "traces" && argc == 2)
            fiber_traces();
        else if (mode == "logs" && argc == 3) {
            Field field;
            SourceLogs logs(field, argv[2]);
            factor(&logs);
        } else
            throw std::invalid_argument(
                "use scan or supplement with PENCIL_FILE, factor, traces, or logs FACTOR_BASE");
        return 0;
    } catch (const std::exception &e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
