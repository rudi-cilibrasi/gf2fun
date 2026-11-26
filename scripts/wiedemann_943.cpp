// Exact 943-bit modular Wiedemann solver (Phase 1 Krylov & Phase 3 Evaluation) for degree-1229 DLP!
// Pure C++20 + AVX2 + OpenMP, ZERO external library dependencies.
// Uses:
//   - 15-limb 64-bit Montgomery arithmetic (960 bits > 943-bit C) for exact reductions & muls
//   - 20-limb 48-bit redundant-radix AVX2 accumulation (5 YMM regs) for blazing-fast +1 SpMV!
// Modes:
//   ./wiedemann_943 --selftest          (tests the 943-bit arithmetic)
//   ./wiedemann_943 --phase1 <rels.bin> <seq.bin> [threads]
//   ./wiedemann_943 --phase3 <rels.bin> <poly.bin> <sol.bin> [threads]
// Compile: g++ -O3 -march=native -fopenmp wiedemann_943.cpp -o wiedemann_943
#include <bits/stdc++.h>
#include <immintrin.h>
#include <omp.h>
using namespace std;

// Exact 943-bit cofactor C = (2^1229 - 1) / (36871 * 46703 * 10543179280661916121033 * 9536289355314392579996071515160583098298616686033085857)
// Stored in 15 uint64_t limbs (little-endian), passed from Python or parsed from decimal string!
static const string COFACTOR_DEC =
    "53392955842462906502525256206896237530607657681405452248628829538140335056019091833139309039691476989536595672486245741799613486059460767317912672601233477410458189253022780891585730123223883909898404934891596729489833819787859139386557550548823481244976333432522178629028656984007087";

static constexpr int L64 = 15;       // 15 * 64 = 960 > 943
static constexpr int L48 = 20;       // 20 * 48 = 960 > 943
static constexpr uint64_t MASK48 = (1ULL << 48) - 1;

struct U960 {
    uint64_t w[L64];
};

struct alignas(32) R48 {
    uint64_t l[L48];
};

// Global modulus C and Montgomery constants (R = 2^960)
U960 MOD_C;
uint64_t MONT_N0INV; // -C[0]^{-1} mod 2^64
U960 MONT_R2;        // R^2 mod C
U960 MONT_ONE;       // R mod C

static inline bool u960_ge(const U960 &a, const U960 &b) {
    for (int i = L64 - 1; i >= 0; --i) {
        if (a.w[i] != b.w[i]) return a.w[i] > b.w[i];
    }
    return true;
}

static inline uint64_t u960_add(U960 &r, const U960 &a, const U960 &b) {
    unsigned char carry = 0;
    for (int i = 0; i < L64; ++i) {
        carry = _addcarry_u64(carry, a.w[i], b.w[i], (unsigned long long *)&r.w[i]);
    }
    return carry;
}

static inline uint64_t u960_sub(U960 &r, const U960 &a, const U960 &b) {
    unsigned char borrow = 0;
    for (int i = 0; i < L64; ++i) {
        borrow = _subborrow_u64(borrow, a.w[i], b.w[i], (unsigned long long *)&r.w[i]);
    }
    return borrow;
}

static inline void mod_add(U960 &r, const U960 &a, const U960 &b) {
    if (u960_add(r, a, b) || u960_ge(r, MOD_C)) {
        u960_sub(r, r, MOD_C);
    }
}

static inline void mod_sub(U960 &r, const U960 &a, const U960 &b) {
    if (u960_sub(r, a, b)) {
        u960_add(r, r, MOD_C);
    }
}

// Montgomery multiplication: returns a * b * R^{-1} mod C (CIOS method)
static inline U960 mont_mul(const U960 &a, const U960 &b) {
    uint64_t t[L64 + 2] = {0};
    for (int i = 0; i < L64; ++i) {
        uint64_t ai = a.w[i];
        unsigned __int128 carry = 0;
        for (int j = 0; j < L64; ++j) {
            unsigned __int128 prod = (unsigned __int128)ai * b.w[j] + t[j] + carry;
            t[j] = (uint64_t)prod;
            carry = prod >> 64;
        }
        unsigned __int128 s = (unsigned __int128)t[L64] + carry;
        t[L64] = (uint64_t)s;
        t[L64 + 1] = (uint64_t)(s >> 64);

        uint64_t m = t[0] * MONT_N0INV;
        carry = ((unsigned __int128)m * MOD_C.w[0] + t[0]) >> 64;
        for (int j = 1; j < L64; ++j) {
            unsigned __int128 prod = (unsigned __int128)m * MOD_C.w[j] + t[j] + carry;
            t[j - 1] = (uint64_t)prod;
            carry = prod >> 64;
        }
        s = (unsigned __int128)t[L64] + carry;
        t[L64 - 1] = (uint64_t)s;
        t[L64] = t[L64 + 1] + (uint64_t)(s >> 64);
        t[L64 + 1] = 0;
    }
    U960 res;
    for (int i = 0; i < L64; ++i) res.w[i] = t[i];
    if (t[L64] || u960_ge(res, MOD_C)) u960_sub(res, res, MOD_C);
    return res;
}

// Fast exact reduction of a (L64 + 1)-limb value (top limb hi < 2^60) modulo C!
// Wait: we can reduce ANY (L64 + 1)-limb value (lo[0..14], hi) by:
//   res = lo_mod_C + hi * (2^960 mod C) mod C!
// Notice 2^960 mod C is JUST MONT_ONE!!
// And multiplying hi (a single uint64_t!) by MONT_ONE takes ONLY 15 muls!
// Wait: hi * MONT_ONE gives a 16-limb number with top limb < hi < 2^60, wait — even better:
//   Since C has 943 bits (top limb C[14] has 47 bits: 2^46 <= C[14] < 2^47),
//   2^960 mod C < C has < 943 bits, so hi * (2^960 mod C) has at most 64 + 943 = 1007 bits!
//   Then its top 64 bits (bits 960..1023) is < 2^47, multiply by MONT_ONE again -> < 990 bits,
//   or simply do 2 steps of fold-by-2^960 (since 2^960 mod C < 2^943, each fold drops bits by 17 bits!!).
//   WAIT A SECOND! Check: 1007 - 960 = 47 bits; fold once -> 47 + 943 = 990 bits -> top 30 bits;
//   fold again -> 30 + 943 = 973 -> top 13 bits; fold again -> 13 + 943 = 956 < 960!!
//   EVEN BETTER: Fold by 2^944 (16 bits below 960!!), where 2^944 mod C = 2^944 - 2*C (or -C) < C!
//   Wait: C is 943 bits (bit 942 is 1: 2^942 < C < 2^943).
//   If we have X = (lo[0..14], hi) up to 1024 bits, let q_approx = floor(X / 2^943) -> at most 81 bits!
//   Even simpler & ZERO edge cases: JUST USE mont_mul(X_lo, MONT_R2) + ... NO, 15-limb fold by MONT_ONE is 3 lines!
//   Wait: for our SpMV, what is the MAXIMUM value of (row_sum * diag[i])?!
//   Row sum of +1 terms: <= 1030 * C < 2^11 * C < 2^954 (fits in 15 limbs with hi = 0!!).
//   Wait: PLUS `other` terms (e.g. +40960 * v[j]): total < 2^17 * C = 2^960 (16 limbs, top limb hi < 2^17)!
//   So let's write a rock-solid `reduce_16(uint64_t x[L64+1])` that works for ANY x[15] < 2^63!
static inline U960 reduce_16(uint64_t x[L64 + 1]) {
    // Fold x[L64] using MONT_ONE = 2^960 mod C (which is < C < 2^943)
    while (x[L64] != 0) {
        uint64_t hi = x[L64];
        x[L64] = 0;
        unsigned __int128 carry = 0;
        for (int i = 0; i < L64; ++i) {
            unsigned __int128 s = (unsigned __int128)hi * MONT_ONE.w[i] + x[i] + carry;
            x[i] = (uint64_t)s;
            carry = s >> 64;
        }
        x[L64] = (uint64_t)carry; // strictly decreases by >= 17 bits every iteration (at most 4 iters, usually 1-2!)
    }
    // Now x[0..14] < 2^960, while C > 2^942, so x / C < 2^18!
    // One approximate quotient step: q = (x[14] >> 46) ? Wait: C[14] is 47 bits (bits 0..46), bit 46 is 1!
    // Let top = (x[14] >> 46) — actually divide x[14] by (C[14] + 1)!!
    // Since x[14] < 2^64 and C[14] >= 2^46, q = x[14] / (C[14] + 1) <= floor(x / C) with error at most 2!!
    uint64_t q = x[L64 - 1] / (MOD_C.w[L64 - 1] + 1);
    if (q) {
        unsigned __int128 borrow = 0;
        for (int i = 0; i < L64; ++i) {
            unsigned __int128 sub = (unsigned __int128)q * MOD_C.w[i] + borrow;
            uint64_t sub_lo = (uint64_t)sub;
            borrow = sub >> 64;
            if (x[i] < sub_lo) ++borrow;
            x[i] -= sub_lo;
        }
    }
    U960 res;
    for (int i = 0; i < L64; ++i) res.w[i] = x[i];
    while (u960_ge(res, MOD_C)) u960_sub(res, res, MOD_C);
    return res;
}

// Multiply U960 a (< C) by uint64_t s (< 2^63) and reduce mod C!
static inline U960 mod_mul_u64(const U960 &a, uint64_t s) {
    uint64_t t[L64 + 1];
    unsigned __int128 carry = 0;
    for (int i = 0; i < L64; ++i) {
        unsigned __int128 prod = (unsigned __int128)a.w[i] * s + carry;
        t[i] = (uint64_t)prod;
        carry = prod >> 64;
    }
    t[L64] = (uint64_t)carry;
    return reduce_16(t);
}

// Convert U960 (< C < 2^943) -> R48 (20 limbs of 48 bits, exact)
static inline void u960_to_r48(const U960 &a, R48 &r) {
    // 3 uint64_t (192 bits) = 4 48-bit limbs! 15 uint64_t = 5 groups of 3 -> 20 48-bit limbs!
    for (int g = 0; g < 5; ++g) {
        uint64_t w0 = a.w[3 * g + 0];
        uint64_t w1 = a.w[3 * g + 1];
        uint64_t w2 = a.w[3 * g + 2];
        r.l[4 * g + 0] = w0 & MASK48;
        r.l[4 * g + 1] = ((w0 >> 48) | (w1 << 16)) & MASK48;
        r.l[4 * g + 2] = ((w1 >> 32) | (w2 << 32)) & MASK48;
        r.l[4 * g + 3] = w2 >> 16;
    }
}

// Carry-propagate R48 (after up to 65535 adds!) and convert to 16-limb 64-bit array for reduce_16
static inline U960 r48_to_u960_mod(const uint64_t l[L48]) {
    uint64_t norm[L48];
    uint64_t carry = 0;
    for (int i = 0; i < L48; ++i) {
        uint64_t v = l[i] + carry;
        norm[i] = v & MASK48;
        carry = v >> 48;
    }
    uint64_t t[L64 + 1];
    for (int g = 0; g < 5; ++g) {
        uint64_t b0 = norm[4 * g + 0];
        uint64_t b1 = norm[4 * g + 1];
        uint64_t b2 = norm[4 * g + 2];
        uint64_t b3 = norm[4 * g + 3];
        t[3 * g + 0] = b0 | (b1 << 48);
        t[3 * g + 1] = (b1 >> 16) | (b2 << 32);
        t[3 * g + 2] = (b2 >> 32) | (b3 << 16);
    }
    t[L64] = carry;
    return reduce_16(t);
}

void init_modulus(const string &dec) {
    memset(&MOD_C, 0, sizeof(MOD_C));
    for (char ch : dec) {
        if (ch < '0' || ch > '9') continue;
        unsigned __int128 carry = (uint64_t)(ch - '0');
        for (int i = 0; i < L64; ++i) {
            unsigned __int128 v = (unsigned __int128)MOD_C.w[i] * 10 + carry;
            MOD_C.w[i] = (uint64_t)v;
            carry = v >> 64;
        }
        assert(carry == 0);
    }
    // Check MOD_C is odd and 943 bits (bit 942 set, bit 943 clear => MOD_C.w[14] in [2^46, 2^47))
    assert((MOD_C.w[0] & 1) == 1);
    assert(MOD_C.w[L64 - 1] >= (1ULL << 46) && MOD_C.w[L64 - 1] < (1ULL << 47));

    // Compute MONT_N0INV = -C[0]^{-1} mod 2^64 by Newton's method
    uint64_t inv = 1;
    for (int i = 0; i < 6; ++i) inv *= 2 - MOD_C.w[0] * inv;
    MONT_N0INV = -inv;
    assert(MOD_C.w[0] * MONT_N0INV == (uint64_t)-1);

    // Compute MONT_ONE = 2^960 mod C by doubling 1 960 times!
    memset(&MONT_ONE, 0, sizeof(MONT_ONE));
    MONT_ONE.w[0] = 1;
    for (int i = 0; i < 960; ++i) mod_add(MONT_ONE, MONT_ONE, MONT_ONE);

    // Compute MONT_R2 = 2^1920 mod C by doubling MONT_ONE 960 times!
    MONT_R2 = MONT_ONE;
    for (int i = 0; i < 960; ++i) mod_add(MONT_R2, MONT_R2, MONT_R2);
}

string u960_to_hex(const U960 &a) {
    ostringstream oss;
    bool started = false;
    for (int i = L64 - 1; i >= 0; --i) {
        if (!started && a.w[i] == 0) continue;
        if (!started) { oss << hex << a.w[i]; started = true; }
        else oss << hex << setw(16) << setfill('0') << a.w[i];
    }
    return started ? oss.str() : "0";
}

// Matrix structure (exact same row selection & seed as check_rank_modp.cpp!)
template<class Column>
struct Matrix {
    uint32_t N;
    vector<uint32_t> masks;
    vector<uint32_t> p1_off, n1024_off, oth_off;
    vector<Column> p1_col;       // expanded positive small coeffs 1..20 (zero mod_mul_u64!)
    vector<Column> n1024_col;    // batched -1024 entries (one mod_mul_u64 per row!)
    vector<pair<Column, int32_t>> oth_col; // rare remaining entries (e.g. +20480, +40960)
    vector<uint64_t> diag; // random 60-bit preconditioner (nonzero)
    vector<uint64_t> u_vec; // random 60-bit projection vector

    void load(const string &path) {
        ifstream in(path, ios::binary);
        if (!in) { cerr << "Cannot open " << path << "\n"; exit(1); }
        uint32_t num_vars, num_rels;
        in.read((char *)&num_vars, 4);
        in.read((char *)&num_rels, 4);
        N = num_vars;
        masks.resize(N);
        in.read((char *)masks.data(), 4 * N);

        struct RawRow {
            vector<Column> p1;
            vector<Column> n1024;
            vector<pair<Column, int32_t>> oth;
        };
        vector<RawRow> all_rows(num_rels);
        for (uint32_t r = 0; r < num_rels; ++r) {
            uint16_t nt;
            if (!in.read((char *)&nt, sizeof(nt))) throw runtime_error("Missing matrix row");
            for (uint16_t k = 0; k < nt; ++k) {
                Column vid; int32_t coef;
                in.read((char *)&vid, sizeof(vid));
                if (!in.read((char *)&coef, sizeof(coef)) || vid >= N)
                    throw runtime_error("Invalid matrix entry");
                if (coef >= 1 && coef <= 20) {
                    for (int rep = 0; rep < coef; ++rep) all_rows[r].p1.push_back(vid);
                } else if (coef == -1024) {
                    all_rows[r].n1024.push_back(vid);
                } else {
                    all_rows[r].oth.push_back({vid, coef});
                }
            }
        }
        in.close();

        // Preserve the row order and projections used by the published certificates.
        vector<uint32_t> perm(num_rels);
        iota(perm.begin(), perm.end(), 0);
        mt19937_64 rng(20261125ULL);
        shuffle(perm.begin(), perm.end(), rng);

        p1_off.assign(N, 0);
        n1024_off.assign(N, 0);
        oth_off.assign(N, 0);
        for (uint32_t i = 0; i < N - 1; ++i) {
            p1_off[i] = (uint32_t)p1_col.size();
            n1024_off[i] = (uint32_t)n1024_col.size();
            oth_off[i] = (uint32_t)oth_col.size();
            for (Column c : all_rows[perm[i]].p1) p1_col.push_back(c);
            for (Column c : all_rows[perm[i]].n1024) n1024_col.push_back(c);
            for (auto &pr : all_rows[perm[i]].oth) oth_col.push_back(pr);
        }
        p1_off[N - 1] = (uint32_t)p1_col.size();
        n1024_off[N - 1] = (uint32_t)n1024_col.size();
        oth_off[N - 1] = (uint32_t)oth_col.size();

        // Generate 60-bit diag and u_vec deterministically from same rng!
        diag.resize(N);
        u_vec.resize(N);
        uint64_t mask60 = (1ULL << 60) - 1;
        for (uint32_t i = 0; i < N; ++i) {
            diag[i] = (rng() & mask60) | 1ULL;
        }
        for (uint32_t i = 0; i < N; ++i) {
            u_vec[i] = (rng() & mask60) | 1ULL;
        }
        cerr << "Loaded matrix N=" << N << " (anchor var 0 mask=" << masks[0]
             << "), p1_nnz=" << p1_col.size() << ", n1024_nnz=" << n1024_col.size()
             << ", oth_nnz=" << oth_col.size() << "\n";
    }

    // Compute nxt = D * A_sq * v (mod C), where v48 is the R48 copy of v!
    void spmv(const vector<U960> &v, const vector<R48> &v48, vector<U960> &nxt, vector<R48> &nxt48) const {
        #pragma omp parallel for schedule(guided, 64)
        for (uint32_t i = 0; i < N - 1; ++i) {
            uint32_t s1 = p1_off[i], e1 = p1_off[i + 1];
            __m256i a0 = _mm256_setzero_si256();
            __m256i a1 = _mm256_setzero_si256();
            __m256i a2 = _mm256_setzero_si256();
            __m256i a3 = _mm256_setzero_si256();
            __m256i a4 = _mm256_setzero_si256();
            for (uint32_t j = s1; j < e1; ++j) {
                if (j + 4 < e1) _mm_prefetch((const char *)&v48[p1_col[j + 4]], _MM_HINT_T0);
                const uint64_t *p = v48[p1_col[j]].l;
                a0 = _mm256_add_epi64(a0, _mm256_load_si256((const __m256i *)(p + 0)));
                a1 = _mm256_add_epi64(a1, _mm256_load_si256((const __m256i *)(p + 4)));
                a2 = _mm256_add_epi64(a2, _mm256_load_si256((const __m256i *)(p + 8)));
                a3 = _mm256_add_epi64(a3, _mm256_load_si256((const __m256i *)(p + 12)));
                a4 = _mm256_add_epi64(a4, _mm256_load_si256((const __m256i *)(p + 16)));
            }
            alignas(32) uint64_t tmp[L48];
            _mm256_store_si256((__m256i *)(tmp + 0), a0);
            _mm256_store_si256((__m256i *)(tmp + 4), a1);
            _mm256_store_si256((__m256i *)(tmp + 8), a2);
            _mm256_store_si256((__m256i *)(tmp + 12), a3);
            _mm256_store_si256((__m256i *)(tmp + 16), a4);
            U960 sum = r48_to_u960_mod(tmp);

            uint32_t sn = n1024_off[i], en = n1024_off[i + 1];
            if (sn < en) {
                __m256i n0 = _mm256_setzero_si256();
                __m256i n1 = _mm256_setzero_si256();
                __m256i n2 = _mm256_setzero_si256();
                __m256i n3 = _mm256_setzero_si256();
                __m256i n4 = _mm256_setzero_si256();
                for (uint32_t j = sn; j < en; ++j) {
                    const uint64_t *p = v48[n1024_col[j]].l;
                    n0 = _mm256_add_epi64(n0, _mm256_load_si256((const __m256i *)(p + 0)));
                    n1 = _mm256_add_epi64(n1, _mm256_load_si256((const __m256i *)(p + 4)));
                    n2 = _mm256_add_epi64(n2, _mm256_load_si256((const __m256i *)(p + 8)));
                    n3 = _mm256_add_epi64(n3, _mm256_load_si256((const __m256i *)(p + 12)));
                    n4 = _mm256_add_epi64(n4, _mm256_load_si256((const __m256i *)(p + 16)));
                }
                alignas(32) uint64_t ntmp[L48];
                _mm256_store_si256((__m256i *)(ntmp + 0), n0);
                _mm256_store_si256((__m256i *)(ntmp + 4), n1);
                _mm256_store_si256((__m256i *)(ntmp + 8), n2);
                _mm256_store_si256((__m256i *)(ntmp + 12), n3);
                _mm256_store_si256((__m256i *)(ntmp + 16), n4);
                U960 nsum = r48_to_u960_mod(ntmp);
                U960 term = mod_mul_u64(nsum, 1024ULL);
                mod_sub(sum, sum, term);
            }

            uint32_t s2 = oth_off[i], e2 = oth_off[i + 1];
            for (uint32_t j = s2; j < e2; ++j) {
                Column col = oth_col[j].first;
                int32_t cf = oth_col[j].second;
                if (cf > 0) {
                    U960 term = mod_mul_u64(v[col], (uint64_t)cf);
                    mod_add(sum, sum, term);
                } else {
                    U960 term = mod_mul_u64(v[col], (uint64_t)(-cf));
                    mod_sub(sum, sum, term);
                }
            }
            U960 res = mod_mul_u64(sum, diag[i]);
            nxt[i] = res;
            u960_to_r48(res, nxt48[i]);
        }
        // Row N-1: anchor row selects v[0]
        U960 last = mod_mul_u64(v[0], diag[N - 1]);
        nxt[N - 1] = last;
        u960_to_r48(last, nxt48[N - 1]);
    }

    // Compute u_vec . v mod C in parallel
    U960 dot_u(const vector<U960> &v) const {
        int nthreads = omp_get_max_threads();
        vector<U960> partial(nthreads);
        for (int t = 0; t < nthreads; ++t) memset(&partial[t], 0, sizeof(U960));
        #pragma omp parallel
        {
            int tid = omp_get_thread_num();
            U960 loc;
            memset(&loc, 0, sizeof(U960));
            #pragma omp for schedule(static)
            for (uint32_t i = 0; i < N; ++i) {
                U960 term = mod_mul_u64(v[i], u_vec[i]);
                mod_add(loc, loc, term);
            }
            partial[tid] = loc;
        }
        U960 tot;
        memset(&tot, 0, sizeof(U960));
        for (int t = 0; t < nthreads; ++t) mod_add(tot, tot, partial[t]);
        return tot;
    }
};

void selftest() {
    init_modulus(COFACTOR_DEC);
    cerr << "MOD_C hex = 0x" << u960_to_hex(MOD_C) << "\n";
    cerr << "MONT_ONE  = 0x" << u960_to_hex(MONT_ONE) << "\n";
    // Verify mont_mul(a*R, b*R) == (a*b)*R mod C, and r48 roundtrip, and reduce_16!
    mt19937_64 rng(999);
    for (int t = 0; t < 1000; ++t) {
        U960 a, b;
        for (int i = 0; i < L64; ++i) { a.w[i] = rng(); b.w[i] = rng(); }
        a.w[L64 - 1] &= (1ULL << 46) - 1; // < C
        b.w[L64 - 1] &= (1ULL << 46) - 1;
        // Test r48 roundtrip + 1000 adds
        R48 ra;
        u960_to_r48(a, ra);
        uint64_t acc[L48] = {0};
        for (int rep = 0; rep < 1025; ++rep)
            for (int k = 0; k < L48; ++k) acc[k] += ra.l[k];
        U960 r1 = r48_to_u960_mod(acc);
        U960 r2 = mod_mul_u64(a, 1025);
        assert(memcmp(&r1, &r2, sizeof(U960)) == 0);

        // Test mont_mul vs mod_mul_u64
        uint64_t s = (rng() & ((1ULL << 60) - 1)) | 1ULL;
        U960 sb; memset(&sb, 0, sizeof(U960)); sb.w[0] = s;
        U960 am = mont_mul(a, MONT_R2);
        U960 sm = mont_mul(sb, MONT_R2);
        U960 pm = mont_mul(am, sm);
        U960 ONE; memset(&ONE, 0, sizeof(U960)); ONE.w[0] = 1;
        U960 p1 = mont_mul(pm, ONE);
        U960 p2 = mod_mul_u64(a, s);
        assert(memcmp(&p1, &p2, sizeof(U960)) == 0);
    }
    cerr << "SELFTEST 1000 random 943-bit arithmetic identities PASSED!\n";
}

template<class Column>
int run_solver(int argc, char **argv) {
    if (argc < 2) {
        cerr << "Usage: --selftest | --phase1 <rels.bin> <seq.bin> [threads] | --phase3 <rels.bin> <poly.bin> <sol.bin> [threads]\n";
        return 1;
    }
    string mode = argv[1];
    if (mode == "--selftest") {
        selftest();
        return 0;
    }
    init_modulus(COFACTOR_DEC);

    if (mode == "--phase1") {
        string rels_path = argv[2], seq_path = argv[3];
        int threads = (argc > 4) ? stoi(argv[4]) : 16;
        omp_set_num_threads(threads);
        Matrix<Column> M;
        M.load(rels_path);
        uint32_t N = M.N;
        uint32_t seq_len = 2 * N;

        vector<U960> v(N), nxt(N);
        vector<R48> v48(N), nxt48(N);
        for (uint32_t i = 0; i < N; ++i) {
            memset(&v[i], 0, sizeof(U960));
            memset(&v48[i], 0, sizeof(R48));
        }
        // Start v_0 = b = D * e_{N-1} = (0, ..., 0, diag[N-1])
        v[N - 1].w[0] = M.diag[N - 1];
        u960_to_r48(v[N - 1], v48[N - 1]);

        vector<U960> seq(seq_len);
        uint32_t start_k = 0;

        // Resume support if checkpoint exists!
        string ckpt_path = seq_path + ".ckpt";
        if (ifstream ck(ckpt_path, ios::binary); ck.good()) {
            ck.read((char *)&start_k, 4);
            ck.read((char *)v.data(), N * sizeof(U960));
            ck.read((char *)seq.data(), start_k * sizeof(U960));
            for (uint32_t i = 0; i < N; ++i) u960_to_r48(v[i], v48[i]);
            cerr << "Resumed Phase 1 from step " << start_k << "/" << seq_len << "\n";
        }

        double t0 = omp_get_wtime();
        for (uint32_t k = start_k; k < seq_len; ++k) {
            seq[k] = M.dot_u(v);
            if (k + 1 < seq_len) {
                M.spmv(v, v48, nxt, nxt48);
                v.swap(nxt);
                v48.swap(nxt48);
            }
            if (k + 1 == 500 || (k + 1) % 2000 == 0 || k + 1 == seq_len) {
                double elapsed = omp_get_wtime() - t0;
                double done = (double)(k + 1 - start_k);
                double ms = elapsed * 1000.0 / done;
                double eta = (seq_len - (k + 1)) * ms / 60000.0;
                cerr << "Phase 1: step " << (k + 1) << "/" << seq_len
                     << " (" << fixed << setprecision(2) << ms << " ms/step, ETA " << eta << " min)\n" << flush;
                if ((k + 1) % 10000 == 0) {
                    ofstream ck(ckpt_path + ".tmp", ios::binary);
                    uint32_t next_k = k + 1;
                    ck.write((char *)&next_k, 4);
                    ck.write((char *)v.data(), N * sizeof(U960));
                    ck.write((char *)seq.data(), next_k * sizeof(U960));
                    ck.close();
                    rename((ckpt_path + ".tmp").c_str(), ckpt_path.c_str());
                }
            }
        }
        ofstream out(seq_path, ios::binary);
        out.write((char *)&N, 4);
        out.write((char *)&seq_len, 4);
        out.write((char *)seq.data(), seq_len * sizeof(U960));
        out.close();
        cerr << "Phase 1 COMPLETE! Saved " << seq_len << " 943-bit terms to " << seq_path << "\n";
        return 0;
    }

    if (mode == "--phase3") {
        string rels_path = argv[2], poly_path = argv[3], sol_path = argv[4];
        int threads = (argc > 5) ? stoi(argv[5]) : 16;
        omp_set_num_threads(threads);
        Matrix<Column> M;
        M.load(rels_path);
        uint32_t N = M.N;

        // Read minimal polynomial coeffs c[0..L-1] where c[k] = (-p_0^{-1} * p_{k+1}) mod C (already negated & divided by p_0!)
        // Then x = sum_{k=0}^{L-1} c[k] * v_k mod C!
        ifstream pin(poly_path, ios::binary);
        uint32_t L;
        pin.read((char *)&L, 4);
        vector<U960> c_mont(L);
        for (uint32_t k = 0; k < L; ++k) {
            U960 raw;
            pin.read((char *)&raw, sizeof(U960));
            c_mont[k] = mont_mul(raw, MONT_R2); // store in Montgomery form for fast mont_mul!
        }
        pin.close();
        cerr << "Loaded Phase 3 polynomial of degree L=" << L << "\n";

        vector<U960> v(N), nxt(N), acc(N);
        vector<R48> v48(N), nxt48(N);
        for (uint32_t i = 0; i < N; ++i) {
            memset(&v[i], 0, sizeof(U960));
            memset(&v48[i], 0, sizeof(R48));
            memset(&acc[i], 0, sizeof(U960));
        }
        v[N - 1].w[0] = M.diag[N - 1];
        u960_to_r48(v[N - 1], v48[N - 1]);

        double t0 = omp_get_wtime();
        for (uint32_t k = 0; k < L; ++k) {
            U960 ck = c_mont[k];
            // acc[i] += ck_raw * v[i] mod C = mont_mul(ck_mont, v[i])!!
            // Wait: check Montgomery! mont_mul(ck_raw * R, v[i]) = ck_raw * v[i] * R * R^{-1} = ck_raw * v[i] mod C!!
            // SO WE DON'T EVEN NEED TO CONVERT v[i] TO MONTGOMERY FORM!!
            #pragma omp parallel for schedule(static)
            for (uint32_t i = 0; i < N; ++i) {
                U960 term = mont_mul(ck, v[i]);
                mod_add(acc[i], acc[i], term);
            }
            if (k + 1 < L) {
                M.spmv(v, v48, nxt, nxt48);
                v.swap(nxt);
                v48.swap(nxt48);
            }
            if ((k + 1) % 2000 == 0 || k + 1 == L) {
                double elapsed = omp_get_wtime() - t0;
                double ms = elapsed * 1000.0 / (k + 1);
                double eta = (L - (k + 1)) * ms / 60000.0;
                cerr << "Phase 3: step " << (k + 1) << "/" << L
                     << " (" << fixed << setprecision(2) << ms << " ms/step, ETA " << eta << " min)\n" << flush;
            }
        }
        ofstream out(sol_path, ios::binary);
        out.write((char *)&N, 4);
        out.write((char *)acc.data(), N * sizeof(U960));
        out.close();
        cerr << "Phase 3 COMPLETE! Saved solution vector of length " << N << " to " << sol_path << "\n";
        return 0;
    }
    return 1;
}

// Matrix files use 16-bit term counts. The number of variables selects the column width.
int main(int argc, char **argv) {
    if (argc < 2 || string(argv[1]) == "--selftest") return run_solver<uint16_t>(argc, argv);
    const string mode = argv[1];
    if ((mode == "--phase1" && argc < 4) || (mode == "--phase3" && argc < 5) ||
        (mode != "--phase1" && mode != "--phase3")) {
        cerr << "Expected --phase1 matrix sequence or --phase3 matrix polynomial solution.\n";
        return 1;
    }
    ifstream input(argv[2], ios::binary);
    uint32_t count, rows;
    if (!input.read(reinterpret_cast<char*>(&count), sizeof(count)) ||
        !input.read(reinterpret_cast<char*>(&rows), sizeof(rows)) || !count || rows < count-1) {
        cerr << "Invalid matrix dimensions.\n";
        return 1;
    }
    if (count > uint32_t(numeric_limits<uint16_t>::max())+1) return run_solver<uint32_t>(argc, argv);
    return run_solver<uint16_t>(argc, argv);
}
