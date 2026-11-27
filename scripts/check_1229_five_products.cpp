// Check signed cyclic orbits of sums of up to five distinct powers of two.
// Compile with g++ -O3 -std=c++17 -fopenmp scripts/check_1229_five_products.cpp -lgmpxx -lgmp.
#include <gmpxx.h>
#include <omp.h>
#include <algorithm>
#include <array>
#include <cstdint>
#include <iostream>
#include <stdexcept>
#include <string>
#include <vector>

namespace {
using Word = std::uint64_t;
using Wide = unsigned __int128;
constexpr int n = 1229, bins = 2048;
constexpr Wide middle_prime = (Wide(0x23b) << 64) + 0x8c013f9aa7f777c9ULL;
using Support = std::array<int, 5>; // unused entries are -1
using Bits = std::array<Word, (n + 63)/64>;
using Counts = std::array<Word, 6>;
using Buckets = std::vector<std::vector<Word>>;

Word binomial(int a, int k) {
    Word r = 1;
    for (int j = 1; j <= k; ++j) r = r * (a - j + 1) / j;
    return r;
}

mpz_class integer(Wide a) {
    const std::array<Word, 2> limbs{Word(a), Word(a >> 64)};
    mpz_class z;
    mpz_import(z.get_mpz_t(), limbs.size(), -1, sizeof(Word), 0, 0, limbs.data());
    return z;
}

Wide wide(const mpz_class& a) {
    std::array<Word, 2> limbs{};
    if (a < 0 || mpz_sizeinbase(a.get_mpz_t(), 2) > 128) throw std::logic_error("residue overflow");
    mpz_export(limbs.data(), nullptr, -1, sizeof(Word), 0, 0, a.get_mpz_t());
    return Wide(limbs[0]) | (Wide(limbs[1]) << 64);
}

// A largest closing gap picks a rotation. Lexicographic comparison resolves ties.
bool canonical(const Support& s, int size) {
    const int closing = n - s[size-1];
    std::array<int, 5> gap{closing};
    bool tie = false;
    for (int j = 1; j < size; ++j) {
        gap[j] = s[j] - s[j-1];
        if (gap[j] > closing) return false;
        tie |= gap[j] == closing;
    }
    if (!tie) return true;
    for (int j = 1; j < size; ++j) if (gap[j] == closing) {
        for (int d = 1; d < size; ++d) {
            int other = gap[(j+d) % size];
            if (other > gap[d]) return false;
            if (other < gap[d]) break;
        }
    }
    return true;
}

Word mix(Word x) {
    x ^= x >> 30;
    x *= 0xbf58476d1ce4e5b9ULL;
    x ^= x >> 27;
    x *= 0x94d049bb133111ebULL;
    return x ^ (x >> 31);
}

struct Phase { int group = -1, shift = 0; bool negative = false; };
struct Family {
    int p, groups = 1;
    std::vector<Phase> phase;
    std::array<int, n> small{};
    std::array<Wide, 2*n> large{};
    const mpz_class modulus = integer(middle_prime);

    explicit Family(int small_prime) : p(small_prime), phase(p) {
        small[0] = 1;
        large[0] = 1;
        for (int j = 1; j < n; ++j) {
            small[j] = 2*small[j-1] % p;
            large[j] = 2*large[j-1] % middle_prime;
        }
        if (2*small.back() % p != 1 || 2*large[n-1] % middle_prime != 1)
            throw std::logic_error("incorrect dyadic period");
        std::copy_n(large.begin(), n, large.begin() + n);
        phase[0] = {0, 0, false};
        for (int u = 1; u < p; ++u) if (phase[u].group < 0) {
            int v = u;
            for (int j = 0; j < n; ++j) {
                if (phase[v].group >= 0 || phase[p-v].group >= 0)
                    throw std::logic_error("overlapping signed residue orbits");
                int inverse_shift = j ? n-j : 0;
                phase[v] = {groups, inverse_shift, false};
                phase[p-v] = {groups, inverse_shift, true};
                v = 2*v % p;
            }
            if (v != u) throw std::logic_error("incomplete signed orbit");
            ++groups;
        }
        if (2*n*(groups-1) != p-1) throw std::logic_error("incomplete orbit partition");
    }

    int add(int a, int b) const { int s = a+b; return s < p ? s : s-p; }

    Word signature(const Support& s, int size, Phase q) const {
        // Rotating the exponents multiplies both prime residues by the same power of two.
        Wide z = large[q.shift];
        for (int i = 1; i < size; ++i) z += large[q.shift+s[i]];
        if (z >= 4*middle_prime) z -= 4*middle_prime;
        if (z >= 2*middle_prime) z -= 2*middle_prime;
        if (z >= middle_prime) z -= middle_prime;
        if (q.group == 0) {
            if (z == 0) throw std::runtime_error("a nonempty sum vanishes modulo both primes");
            auto value = integer(z);
            mpz_powm_ui(value.get_mpz_t(), value.get_mpz_t(), n, modulus.get_mpz_t());
            z = wide(value);
            z = std::min(z, middle_prime-z);
        } else if (q.negative && z) {
            z = middle_prime - z;
        }
        return mix(Word(z) ^ mix(Word(z >> 64) + (Word(q.group) << 16)));
    }

    template<class Visit>
    Counts enumerate(int first, int end, const Visit& visit) const {
        std::vector<Bits> allowed(p);
        #pragma omp parallel for schedule(static)
        for (int r = 0; r < p; ++r)
            for (int j = 0; j < n; ++j) {
                int g = phase[add(r, small[j])].group;
                if (first <= g && g < end) allowed[r][j/64] |= Word(1) << (j%64);
            }
        Counts count{};
        auto record = [&](const Support& s, int size, Phase q, Counts& local) {
            ++local[size];
            visit(s, size, signature(s, size, q));
        };
        auto short_row = [&](const Support& s, int size, int r, Counts& local) {
            Phase q = phase[r];
            if (first <= q.group && q.group < end && canonical(s, size)) record(s, size, q, local);
        };
        short_row({0,-1,-1,-1,-1}, 1, 1, count);
        std::vector<std::array<int, 2>> prefixes;
        for (int a = 1; 2*a <= n; ++a) {
            short_row({0,a,-1,-1,-1}, 2, add(1, small[a]), count);
            // An interior gap must fit before a closing gap at least as large.
            for (int b = a+1; b <= std::min(n-a, (n+a)/2); ++b) prefixes.push_back({a,b});
        }
        #pragma omp parallel
        {
            Counts local{};
            #pragma omp for schedule(dynamic, 32)
            for (size_t id = 0; id < prefixes.size(); ++id) {
                auto [a,b] = prefixes[id];
                int previous = std::max(a, b-a), r3 = add(add(1, small[a]), small[b]);
                Support s{0,a,b,-1,-1};
                short_row(s, 3, r3, local);
                for (int c = b+1; c <= std::min(n-previous, (n+b)/2); ++c) {
                    s[3] = c;
                    int largest = std::max(previous, c-b), r4 = add(r3, small[c]);
                    short_row(s, 4, r4, local);
                    const int last = std::min(n-largest, (n+c)/2), begin = c+1;
                    if (begin > last) continue;
                    const auto& words = allowed[r4];
                    for (int w = begin/64; w <= last/64; ++w) {
                        Word bits = words[w];
                        if (w == begin/64) bits &= ~Word(0) << (begin%64);
                        if (w == last/64) bits &= ~Word(0) >> (63-last%64);
                        while (bits) {
                            int d = 64*w + __builtin_ctzll(bits);
                            bits &= bits-1;
                            s[4] = d;
                            if ((n-d == largest || n-d == d-c) && !canonical(s, 5)) continue;
                            record(s, 5, phase[add(r4, small[d])], local);
                        }
                    }
                }
            }
            #pragma omp critical
            for (int k = 1; k <= 5; ++k) count[k] += local[k];
        }
        return count;
    }
};

int bucket(Word key) { return key >> 53; }

// Repeated full keys must be repeated in both 20-bit projections in their bin.
struct ProjectedRepeats {
    static constexpr Word mask = (1 << 20) - 1;
    std::vector<Word> seen = std::vector<Word>((mask+1)/64), twice = seen;
    void insert(Word x) {
        x &= mask;
        Word bit = Word(1) << (x%64);
        twice[x/64] |= seen[x/64] & bit;
        seen[x/64] |= bit;
    }
    bool repeat(Word x) const {
        x &= mask;
        return (twice[x/64] >> (x%64)) & 1;
    }
};

std::vector<Word> duplicates(std::vector<Buckets>& data) {
    std::vector<Word> result;
    #pragma omp parallel for schedule(dynamic, 1)
    for (int b = 0; b < bins; ++b) {
        ProjectedRepeats lo, hi;
        for (const auto& worker : data)
            for (Word k : worker[b]) { lo.insert(k); hi.insert(k >> 20); }
        std::vector<Word> selected;
        for (auto& worker : data) {
            for (Word k : worker[b])
                if (lo.repeat(k) && hi.repeat(k >> 20)) selected.push_back(k);
            std::vector<Word>().swap(worker[b]);
        }
        std::sort(selected.begin(), selected.end());
        std::vector<Word> hits;
        for (size_t j = 1; j < selected.size(); ++j)
            if (selected[j] == selected[j-1] && (hits.empty() || hits.back() != selected[j]))
                hits.push_back(selected[j]);
        #pragma omp critical
        result.insert(result.end(), hits.begin(), hits.end());
    }
    std::sort(result.begin(), result.end());
    return result;
}

struct Hit { Word key; Support support; int size; };
void resolve(const Family& f, int first, int end, const std::vector<Word>& keys) {
    if (keys.empty()) return;
    std::vector<Hit> hits;
    f.enumerate(first, end, [&](const Support& s, int size, Word key) {
        if (std::binary_search(keys.begin(), keys.end(), key)) {
            #pragma omp critical
            hits.push_back({key, s, size});
        }
    });
    const mpz_class large("9536289355314392579996071515160583098298616686033085857");
    const mpz_class mod = f.modulus * large * f.p;
    auto sum = [](const Hit& h) {
        mpz_class x = 0;
        for (int i = 0; i < h.size; ++i) mpz_setbit(x.get_mpz_t(), h.support[i]);
        return x;
    };
    for (size_t i = 0; i < hits.size(); ++i) for (size_t j = 0; j < i; ++j) {
        if (hits[i].key != hits[j].key) continue;
        mpz_class x = sum(hits[i]) % mod, y = sum(hits[j]) % mod;
        for (int k = 0; k < n; ++k) {
            if (x == y || x+y == mod) throw std::runtime_error("true signed cyclic-orbit collision");
            x = 2*x % mod;
        }
    }
}

Counts run_batch(const Family& f, int first, int end) {
    std::vector<Buckets> data(omp_get_max_threads(), Buckets(bins));
    const Counts count = f.enumerate(first, end, [&](const Support&, int, Word key) {
        data[omp_get_thread_num()][bucket(key)].push_back(key);
    });
    const auto keys = duplicates(data);
    resolve(f, first, end, keys);
    std::cout << f.p << " classes [" << first << ',' << end << ") counts";
    for (int k = 1; k <= 5; ++k) std::cout << ' ' << count[k];
    std::cout << " repeated fingerprints " << keys.size() << std::endl;
    return count;
}
} // namespace

int main(int argc, char** argv) {
    if (argc != 2 && argc != 4) throw std::invalid_argument("usage: check SMALL_PRIME [FIRST_CLASS END_CLASS]");
    const int p = std::stoi(argv[1]);
    if (p != 36871 && p != 46703) throw std::invalid_argument("choose 36871 or 46703");
    const Family f(p);
    const int first = argc == 4 ? std::stoi(argv[2]) : 0, end = argc == 4 ? std::stoi(argv[3]) : f.groups;
    if (first < 0 || first >= end || end > f.groups) throw std::invalid_argument("invalid class range");
    Counts total{};
    for (int a = first; a < end; a += 2) {
        const auto count = run_batch(f, a, std::min(a+2, end));
        for (int k = 1; k <= 5; ++k) total[k] += count[k];
    }
    if (first == 0 && end == f.groups) {
        for (int k = 1; k <= 5; ++k)
            if (n * total[k] != binomial(n,k)) throw std::runtime_error("incomplete subset orbit count");
        std::cout << "All sizes through five verified modulo the three order factors.\n";
    }
}
