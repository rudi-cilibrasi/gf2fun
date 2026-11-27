// Find exact power relations between sparse roots and published elements with known order.
// The Python driver validates the two input catalogues. All trace filters are necessary conditions.
#include <NTL/GF2XFactoring.h>
#include <NTL/ZZ.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <limits>
#include <numeric>
#include <stdexcept>
#include <string>
#include <tuple>
#include <unordered_set>
#include <vector>
#ifdef __PCLMUL__
#include <wmmintrin.h>
#endif

namespace {
using Word = std::uint64_t;
using Taps = std::array<int, 3>;
using NTL::GF2X;
using NTL::GF2XModulus;
constexpr int degree = 1229, prefix_bits = 24;
constexpr int signature_bits = 64;
constexpr int last_moment = 2 * signature_bits - 1;

Taps reciprocal(Taps t) { return {degree - t[2], degree - t[1], degree - t[0]}; }

GF2X pentanomial(Taps taps) {
    GF2X f;
    NTL::SetCoeff(f, 0);
    NTL::SetCoeff(f, degree);
    for (int d : taps) NTL::SetCoeff(f, d);
    return f;
}

GF2X polynomial(const NTL::ZZ& mask) {
    GF2X f;
    for (int i = 0; i < NTL::NumBits(mask); ++i)
        if (NTL::bit(mask, i)) NTL::SetCoeff(f, i);
    return f;
}

Word low_product(Word a, Word b) {
#ifdef __PCLMUL__
    return _mm_cvtsi128_si64(_mm_clmulepi64_si128(_mm_cvtsi64_si128(a), _mm_cvtsi64_si128(b), 0));
#else
    Word result = 0;
    for (; b; b &= b - 1) result ^= a << __builtin_ctzll(b);
    return result;
#endif
}

// If Q is the reciprocal of f, TQ'/Q has coefficients Tr(alpha^j), j > 0.
// Past word n its denominator Q(T^64) gives a recurrence at whole-word offsets.
class Traces {
    static constexpr int padding = degree / 64 + 2;
    const std::array<int, 4> delays;
    std::array<Word, padding> numerator{};
    Word inverse = 1;
    std::vector<Word> words = std::vector<Word>(padding);

public:
    explicit Traces(Taps q) : delays{q[0], q[1], q[2], degree} {
        Word low = 1;
        for (int d : delays) {
            if (d < 64) low |= Word(1) << d;
            if (d % 2) numerator[d / 64] |= Word(1) << (d % 64);
        }
        Word residue = low;
        for (int i = 1; i < 64; ++i)
            if ((residue >> i) & 1) {
                inverse ^= Word(1) << i;
                residue ^= low << i;
            }
    }

    void extend(int last) {
        const int begin = int(words.size()) - padding;
        const int end = last / 64 + 1;
        if (end <= begin) return;
        words.resize(padding + end);
        Word* w = words.data() + padding;
        for (int k = begin; k < std::min(end, degree + 1); ++k) {
            Word value = k < padding ? numerator[k] : 0;
            for (int d : delays) {
                const int blocks = d / 64, bits = d % 64;
                if (bits) value ^= w[k - blocks - 1] >> (64 - bits);
                if (blocks) value ^= w[k - blocks] << bits;
            }
            w[k] = inverse == 1 ? value : low_product(value, inverse);
        }
        for (int k = std::max(begin, degree + 1); k < end; ++k)
            w[k] = w[k - delays[0]] ^ w[k - delays[1]] ^ w[k - delays[2]] ^ w[k - degree];
    }

    Word bit(int j) const { return (words[padding + j / 64] >> (j % 64)) & 1; }

    template<int count>
    Word sample(int start, int stride) const {
        Word result = 0;
        for (int i = 0; i < count; ++i, start += stride) result |= bit(start) << i;
        return result;
    }
};

constexpr int high_start = 1201, high_step = 182, high_last = high_start + 31 * high_step;
Word distant(const Traces& pos, const Traces& neg, int m) {
    return pos.sample<32>(high_start * m, high_step * m)
        | (neg.sample<32>(high_start * m, high_step * m) << 32);
}
Word joint_prefix(Word a, Word b) { return a | (b << prefix_bits); }
unsigned short_prefix(Word a, Word b) { return (a & 255) | ((b & 255) << 8); }

struct SparseFilters {
    std::array<bool, 1 << 16> early{};
    std::unordered_set<Word> middle, later, high;

    // The last 32 odd moments through 127 are already in the reference-element trace buffer.
    static Word later_key(const Traces& pos, const Traces& neg, int m) {
        return pos.sample<32>(65*m, 2*m) | (neg.sample<32>(65*m, 2*m) << 32);
    }

    void add(Word a, Word b, Word l, Word h) {
        early[short_prefix(a, b)] = true;
        middle.insert(joint_prefix(a, b));
        later.insert(l);
        high.insert(h);
    }

    explicit SparseFilters(const std::vector<Taps>& supports) {
        // Generate both target orientations even though only one source orientation is needed.
        std::vector<std::array<Word, 4>> rows(supports.size());
        #pragma omp parallel for schedule(static)
        for (size_t i = 0; i < supports.size(); ++i) {
            Traces pos(reciprocal(supports[i])), neg(supports[i]);
            pos.extend(high_last);
            neg.extend(high_last);
            rows[i] = {pos.sample<prefix_bits>(1, 2), neg.sample<prefix_bits>(1, 2),
                       later_key(pos, neg, 1), distant(pos, neg, 1)};
        }
        for (auto [a, b, l, h] : rows) {
            add(a, b, l, h);
            add(b, a, (l << 32) | (l >> 32), (h << 32) | (h >> 32));
        }
    }
};

using DenseRow = std::pair<Word, int>;

struct DenseFilters {
    std::vector<DenseRow> rows;
    std::vector<bool> prefix = std::vector<bool>(1 << prefix_bits);

    DenseFilters(const GF2X& modulus, const std::vector<NTL::ZZ>& masks) : rows(masks.size()) {
        const auto trace = NTL::TraceVec(modulus);
        #pragma omp parallel
        {
            const GF2XModulus field(modulus);
            #pragma omp for schedule(static)
            for (size_t i = 0; i < masks.size(); ++i) {
                const auto powers = NTL::ProjectPowers(trace, last_moment + 1, polynomial(masks[i]), field);
                Word signature = 0;
                for (int j = 0; j < signature_bits; ++j)
                    if (NTL::IsOne(powers[2*j + 1])) signature |= Word(1) << j;
                rows[i] = {signature, int(i)};
            }
        }
        std::sort(rows.begin(), rows.end());
        for (auto [signature, index] : rows) prefix[signature % prefix.size()] = true;
    }
};

struct Match {
    int source, power;
    Taps target;
    int dense; // -1 for a pentanomial, otherwise an index into the certified table
};

struct Search {
    const std::vector<Taps>& supports;
    const std::vector<NTL::ZZ>& masks;
    const GF2X& modulus;
    const SparseFilters& sparse;
    const DenseFilters& dense;

    void known(int i, int m, Word prefix, const Traces& stream, std::vector<Match>& matches) const {
        if (!dense.prefix[prefix]) return;
        Word signature = prefix | (stream.sample<signature_bits - prefix_bits>(
            (2 * prefix_bits + 1) * std::abs(m), 2 * std::abs(m)) << prefix_bits);
        auto row = std::lower_bound(dense.rows.begin(), dense.rows.end(), DenseRow{signature, 0});
        if (row == dense.rows.end() || row->first != signature) return;
        const GF2XModulus field(modulus);
        const GF2XModulus source(pentanomial(m > 0 ? supports[i] : reciprocal(supports[i])));
        const auto y = NTL::PowerXMod(std::abs(m), source);
        for (; row != dense.rows.end() && row->first == signature; ++row) {
            const auto g = NTL::IrredPolyMod(polynomial(masks[row->second]), field);
            if (NTL::IsZero(NTL::CompMod(g, y, source))) matches.push_back({i, m, {}, row->second});
        }
    }

    std::vector<Match> run(int maximum, int start, int end, long long& shortlisted) const {
        std::vector<Match> matches;
        #pragma omp parallel reduction(+:shortlisted)
        {
            std::vector<Match> local;
            #pragma omp for schedule(dynamic, 32)
            for (int i = start; i < end; ++i) {
                Traces pos(reciprocal(supports[i])), neg(supports[i]);
                pos.extend(last_moment * maximum);
                neg.extend(last_moment * maximum);
                std::vector<int> possible;
                for (int m = 1; m <= maximum; m += 2) {
                    const Word a = pos.sample<prefix_bits>(m, 2*m), b = neg.sample<prefix_bits>(m, 2*m);
                    known(i, m, a, pos, local);
                    known(i, -m, b, neg, local);
                    if (m > 1 && sparse.early[short_prefix(a, b)] && sparse.middle.count(joint_prefix(a, b))
                        && sparse.later.count(SparseFilters::later_key(pos, neg, m)))
                        possible.push_back(m);
                }
                shortlisted += possible.size();
                if (possible.empty()) continue;
                pos.extend(high_last * possible.back());
                neg.extend(high_last * possible.back());
                for (int m : possible) {
                    if (!sparse.high.count(distant(pos, neg, m))) continue;
                    const GF2XModulus source(pentanomial(supports[i]));
                    auto g = NTL::IrredPolyMod(NTL::PowerXMod(m, source), source);
                    if (NTL::deg(g) != degree || NTL::weight(g) != 5) continue;
                    Taps taps;
                    int count = 0;
                    for (int j = 1; j < degree; ++j)
                        if (NTL::IsOne(NTL::coeff(g, j))) taps.at(count++) = j;
                    if (count != 3 || !std::binary_search(supports.begin(), supports.end(),
                                                         std::min(taps, reciprocal(taps))))
                        throw std::logic_error("missing pentanomial in the input census");
                    local.push_back({i, m, taps, -1});
                }
            }
            #pragma omp critical
            matches.insert(matches.end(), local.begin(), local.end());
        }
        std::sort(matches.begin(), matches.end(), [](const Match& a, const Match& b) {
            return std::tie(a.source, a.power, a.dense) < std::tie(b.source, b.power, b.dense);
        });
        return matches;
    }
};

void check_traces(Taps taps) {
    Traces s(reciprocal(taps));
    // Independently test both recurrences across their boundary and at separated large powers.
    s.extend(63);
    s.extend(64 * degree);
    s.extend(130003);
    const GF2XModulus f(pentanomial(taps));
    for (int j : {1, 2, 19, 63, 64, 127, 1229, 78881, 130003}) {
        if (bool(s.bit(j)) != bool(NTL::IsOne(NTL::TraceMod(NTL::PowerXMod(j, f), f))))
            throw std::logic_error("trace sieve disagrees with field arithmetic");
    }
}

void check_reference_lookup(const SparseFilters& sparse) {
    const std::vector<Taps> support{{166, 249, 332}};
    const auto f = pentanomial(support.front());
    const GF2XModulus field(f);
    constexpr int exponent = 1451;
    const auto power = NTL::PowerXMod(exponent, field);
    std::vector<NTL::ZZ> masks;
    for (const auto& y : {power, NTL::InvMod(power, f)}) {
        NTL::ZZ mask;
        for (int j = 0; j < degree; ++j)
            if (NTL::IsOne(NTL::coeff(y, j))) NTL::SetBit(mask, j);
        masks.push_back(mask);
    }
    const DenseFilters dense(f, masks);
    const Search search{support, masks, f, sparse, dense};
    std::vector<Match> hits;
    for (int m : {exponent, -exponent}) {
        Traces s(m > 0 ? reciprocal(support.front()) : support.front());
        s.extend(exponent * last_moment);
        search.known(0, m, s.sample<prefix_bits>(exponent, 2*exponent), s, hits);
    }
    if (hits.size() != 2 || hits[0].dense != 0 || hits[1].dense != 1)
        throw std::logic_error("signed reference lookup missed an exact control");
}

struct PowerClass {
    Word distant_bits;
    std::uint32_t extra_bits, id;

    bool operator<(const PowerClass& other) const {
        return std::tie(distant_bits, extra_bits, id)
             < std::tie(other.distant_bits, other.extra_bits, other.id);
    }
};

void sparse_ratios(const std::vector<Taps>& supports, int maximum) {
    const int width = (maximum + 1) / 2;
    if (supports.size()*width > std::numeric_limits<std::uint32_t>::max())
        throw std::length_error("power class identifiers exceed 32 bits");
    std::vector<PowerClass> classes(supports.size() * width);
    #pragma omp parallel for schedule(dynamic, 128)
    for (size_t i = 0; i < supports.size(); ++i) {
        Traces pos(reciprocal(supports[i])), neg(supports[i]);
        pos.extend(maximum * high_last);
        neg.extend(maximum * high_last);
        for (int m = 1; m <= maximum; m += 2) {
            const Word forward = distant(pos, neg, m), reverse = (forward << 32) | (forward >> 32);
            const std::uint32_t a = pos.sample<16>(5431*m, 42*m), b = neg.sample<16>(5431*m, 42*m);
            const std::uint32_t extra = a | (b << 16), flipped = b | (a << 16);
            // Take the lesser of the two whole signatures, including ties in their first 64 bits.
            const auto key = std::min(std::make_pair(forward, extra), std::make_pair(reverse, flipped));
            const auto id = static_cast<std::uint32_t>(i*width + m/2);
            classes[id] = {key.first, key.second, id};
        }
    }
    std::sort(classes.begin(), classes.end());
    size_t exact = 0, matches = 0;
    for (size_t begin = 0, end; begin < classes.size(); begin = end) {
        end = begin + 1;
        while (end < classes.size() && classes[end].distant_bits == classes[begin].distant_bits
               && classes[end].extra_bits == classes[begin].extra_bits) ++end;
        for (size_t i = begin; i < end; ++i) {
            for (size_t j = i + 1; j < end; ++j) {
                const auto left = classes[i].id, right = classes[j].id;
                const int u = 2*(left % width) + 1, v = 2*(right % width) + 1;
                if (std::gcd(u, v) != 1) continue;
                ++exact;
                const auto a = supports[left/width], b = supports[right/width];
                const GF2XModulus f(pentanomial(a)), g(pentanomial(b));
                const auto p = NTL::IrredPolyMod(NTL::PowerXMod(u, f), f);
                const auto q = NTL::IrredPolyMod(NTL::PowerXMod(v, g), g);
                if (p != q && p != NTL::reverse(q)) continue;
                ++matches;
                for (int tap : a) std::cout << tap << ' ';
                std::cout << u;
                for (int tap : b) std::cout << ' ' << tap;
                std::cout << ' ' << (p == q ? v : -v) << '\n';
            }
        }
    }
    std::cerr << classes.size() << " signed-power classes, " << exact << " exact comparisons, "
              << matches << " reduced matches\n";
}
} // namespace

int main(int argc, char** argv) {
    const bool ratios = argc == 3 && std::string(argv[2]) == "--sparse-ratios";
    if (argc != 2 && argc != 4 && !ratios)
        throw std::invalid_argument("usage: census MAX_ODD [FIRST_ROW END_ROW | --sparse-ratios]");
    const int maximum = std::stoi(argv[1]);
    if (maximum < 1 || maximum % 2 == 0 || maximum >= 36871) throw std::invalid_argument("invalid odd bound");
    GF2X modulus;
    std::vector<NTL::ZZ> masks;
    if (!ratios) {
        NTL::ZZ field_mask;
        int num_masks;
        if (!(std::cin >> field_mask >> num_masks) || num_masks < 1) return 1;
        modulus = polynomial(field_mask);
        if (NTL::deg(modulus) != degree || !NTL::IterIrredTest(modulus)) return 1;
        masks.resize(num_masks);
        for (auto& p : masks) if (!(std::cin >> p) || p <= 1 || NTL::NumBits(p) > degree) return 1;
    }
    int num_sources;
    if (!(std::cin >> num_sources) || num_sources != 319583) return 1;
    std::vector<Taps> supports(num_sources);
    for (auto& t : supports)
        if (!(std::cin >> t[0] >> t[1] >> t[2]) || !(0 < t[0] && t[0] < t[1] && t[1] < t[2]
             && t[2] < degree && t < reciprocal(t))) return 1;
    std::string extra;
    if (std::cin >> extra || !std::is_sorted(supports.begin(), supports.end())
        || std::adjacent_find(supports.begin(), supports.end()) != supports.end()) return 1;
    int start = argc == 4 ? std::stoi(argv[2]) : 0, end = argc == 4 ? std::stoi(argv[3]) : num_sources;
    if (start < 0 || start >= end || end > num_sources) return 1;
    for (Taps t : {Taps{1, 2, 627}, Taps{64, 128, 193}, Taps{166, 249, 332}}) {
        check_traces(t);
        check_traces(reciprocal(t));
    }
    if (ratios) {
        sparse_ratios(supports, maximum);
        return 0;
    }
    const SparseFilters sparse(supports);
    check_reference_lookup(sparse);
    std::cerr << "sparse targets indexed, " << sparse.middle.size() << " short signatures\n";
    const DenseFilters dense(modulus, masks);
    std::cerr << masks.size() << " reference elements indexed\n";
    long long shortlisted = 0;
    const auto matches = Search{supports, masks, modulus, sparse, dense}.run(maximum, start, end, shortlisted);
    for (const auto& match : matches) {
        const auto t = supports[match.source];
        std::cout << t[0] << ' ' << t[1] << ' ' << t[2] << ' ' << match.power;
        if (match.dense < 0)
            for (int j : match.target) std::cout << ' ' << j;
        else std::cout << " mask " << masks[match.dense];
        std::cout << '\n';
    }
    std::cerr << "rows " << start << ".." << end << ", odd powers through " << maximum
              << ", sparse prefix survivors " << shortlisted << ", exact matches " << matches.size() << '\n';
}
