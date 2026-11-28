// Solve homogeneous matching equations for two binary power images.
// check_power_orbit_collisions.py supplies residue profiles and parity-reduced monomials.
#include <algorithm>
#include <array>
#include <iostream>
#include <numeric>
#include <set>
#include <stdexcept>
#include <utility>
#include <vector>

using Vector = std::array<long long, 4>;
using Support = std::vector<long long>;
using Solutions = std::set<std::pair<int, Support>>;

struct Term {
    Vector point;
    Vector original;
};

struct Profile {
    int weight;
    int modulus;
    int sign;
    Vector residues;
};

static long long coordinate_gcd(const Vector& v) {
    long long divisor = 0;
    for (long long entry : v) divisor = std::gcd(divisor, entry);
    return divisor;
}

static Vector normal(const Vector& a, const Vector& b) {
    Vector h{};
    for (size_t i = 0; i < h.size(); ++i) h[i] = a[i] - b[i];
    long long divisor = coordinate_gcd(h);
    if (!divisor) throw std::logic_error("identical surviving terms");
    auto pivot = std::find_if(h.begin(), h.end(), [](long long x) { return x != 0; });
    if (*pivot < 0) divisor = -divisor;
    for (auto& entry : h) entry /= divisor;
    return h;
}

static long long dot(const Vector& a, const Vector& b) {
    return std::inner_product(a.begin(), a.end(), b.begin(), 0LL);
}

static std::vector<Term> cancel_pairs(std::vector<Term> terms) {
    std::sort(terms.begin(), terms.end(), [](const Term& a, const Term& b) { return a.point < b.point; });
    std::vector<Term> remaining;
    for (size_t i = 0, end; i < terms.size(); i = end) {
        end = i + 1;
        while (end < terms.size() && terms[i].point == terms[end].point) ++end;
        if ((end - i) % 2) remaining.push_back(terms[i]);
    }
    return remaining;
}

static bool compatible(const Support& support, const Profile& profile) {
    for (int unit = 1; unit < profile.modulus; ++unit) {
        if (std::gcd(unit, profile.modulus) != 1) continue;
        bool matches = true;
        for (int i = 1; i < profile.weight; ++i) {
            if ((unit * support[i] - profile.residues[i-1]) % profile.modulus != 0) matches = false;
        }
        if (matches) return true;
    }
    return false;
}

static void check_line(const Profile& profile, const std::vector<Vector>& points,
                       const std::vector<Term>& terms, const Vector& h, Solutions& solutions) {
    const Vector line{h[1], -h[0], 0, 0};
    std::vector<long long> exponents;
    for (const auto& term : terms) exponents.push_back(dot(term.point, line));
    std::sort(exponents.begin(), exponents.end());
    for (size_t i = 0; i < exponents.size(); i += 2) {
        if (i + 1 == exponents.size() || exponents[i] != exponents[i+1]) return;
    }

    Support support;
    long long divisor = 0;
    for (const auto& point : points) {
        support.push_back(dot(point, line));
        divisor = std::gcd(divisor, support.back());
    }
    if (!support.back()) return;
    if (support.back() < 0) divisor = -divisor;
    for (auto& entry : support) entry /= divisor;
    const long long degree = support.back();
    for (int i = 1; i < profile.weight - 1; ++i) {
        if (support[i] <= 0 || support[i] >= degree) return;
    }
    if (!compatible(support, profile)) return;
    std::sort(support.begin(), support.end());
    if (std::adjacent_find(support.begin(), support.end()) != support.end()) return;
    solutions.emplace(profile.sign, support);
    std::reverse(support.begin(), support.end());
    for (auto& entry : support) entry = degree - entry;
    solutions.emplace(profile.sign, support);
}

static void search(const Profile& profile, int dimension, const std::vector<Vector>& points,
                   const std::vector<Term>& terms, Solutions& solutions) {
    if (terms.empty()) throw std::runtime_error("positive-dimensional identity requires classification");
    // The first surviving term must cancel with some other surviving term.
    std::set<Vector> visited;
    for (size_t i = 1; i < terms.size(); ++i) {
        const auto original = normal(terms.front().original, terms[i].original);
        if (dot(original, profile.residues) % profile.modulus != 0) continue;
        const auto h = normal(terms.front().point, terms[i].point);
        if (!visited.insert(h).second) continue;
        if (dimension == 2) {
            check_line(profile, points, terms, h, solutions);
            continue;
        }

        int pivot = 0;
        while (!h[pivot]) ++pivot;
        // Eliminate the pivot coordinate and use the same denominator for every label.
        auto project = [&](const Vector& v) {
            Vector projected{};
            int j = 0;
            for (int k = 0; k < dimension; ++k) {
                if (k != pivot) projected[j++] = h[pivot] * v[k] - v[pivot] * h[k];
            }
            return projected;
        };
        std::vector<Vector> next_points;
        long long divisor = 0;
        for (const auto& p : points) {
            next_points.push_back(project(p));
            divisor = std::gcd(divisor, coordinate_gcd(next_points.back()));
        }
        if (std::set<Vector>(next_points.begin(), next_points.end()).size() < points.size()) continue;
        for (auto& p : next_points) for (auto& entry : p) entry /= divisor;
        std::vector<Term> next_terms;
        for (const auto& term : terms) {
            auto p = project(term.point);
            for (auto& entry : p) entry /= divisor;
            next_terms.push_back({p, term.original});
        }
        search(profile, dimension - 1, next_points, cancel_pairs(std::move(next_terms)), solutions);
    }
}

int main() {
    try {
        Solutions solutions;
        Profile profile{};
        while (std::cin >> profile.weight) {
            if (!(std::cin >> profile.modulus >> profile.sign) || (profile.weight != 3 && profile.weight != 5)
                    || profile.modulus < 2 || profile.modulus > 35 || (profile.sign != 1 && profile.sign != -1))
                throw std::invalid_argument("invalid matching profile");
            const int dimension = profile.weight - 1;
            std::vector<Vector> points(profile.weight);
            profile.residues.fill(0);
            for (int i = 0; i < dimension; ++i) {
                if (!(std::cin >> profile.residues[i]) || profile.residues[i] < 0
                        || profile.residues[i] >= profile.modulus) throw std::invalid_argument("invalid residue");
                points[i+1][i] = 1;
            }
            int count;
            if (!(std::cin >> count) || count < 0) throw std::invalid_argument("invalid term count");
            std::vector<Term> terms;
            for (int j = 0; j < count; ++j) {
                Vector p{};
                for (int i = 0; i < dimension; ++i) {
                    if (!(std::cin >> p[i]) || p[i] < -profile.modulus || p[i] > profile.modulus)
                        throw std::invalid_argument("invalid monomial label");
                }
                terms.push_back({p, p});
            }
            // At modulus <= 35 the two projections bound coordinates by 4,900 then
            // 96,040,000. The final two-dimensional dot products fit in a signed 64-bit integer.
            search(profile, dimension, points, cancel_pairs(std::move(terms)), solutions);
        }
        if (!std::cin.eof()) throw std::invalid_argument("invalid trailing input");
        for (const auto& [sign, support] : solutions) {
            std::cout << sign;
            for (auto e : support) std::cout << ' ' << e;
            std::cout << '\n';
        }
    } catch (const std::exception& e) {
        std::cerr << e.what() << '\n';
        return 1;
    }
}
