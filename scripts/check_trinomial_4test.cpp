// Fast standalone C++ exact 4-test (reciprocal pair-product gcd) verifier for GF(2)[X] polynomials up to deg 300.
// Uses exact algorithm from check_pair_products.py (Berlekamp-Massey on exterior square bivector X^k ^ X^{k+1}),
// accelerated with 64-bit word bitsets! Single-threaded to avoid interfering with task-255.
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <vector>
#include <algorithm>
#include <string>

struct BitPoly {
    std::vector<uint64_t> w;
    int deg() const {
        for (int i = (int)w.size() - 1; i >= 0; --i) {
            if (w[i]) return (i << 6) + (63 - __builtin_clzll(w[i]));
        }
        return -1;
    }
    void trim() {
        while (!w.empty() && w.back() == 0) w.pop_back();
    }
    void set_bit(int pos) {
        size_t idx = pos >> 6;
        if (idx >= w.size()) w.resize(idx + 1, 0);
        w[idx] |= (1ULL << (pos & 63));
    }
    int get_bit(int pos) const {
        size_t idx = pos >> 6;
        if (idx >= w.size()) return 0;
        return (int)((w[idx] >> (pos & 63)) & 1ULL);
    }
    bool is_zero() const { return deg() < 0; }
};

static BitPoly xor_shift(const BitPoly& a, const BitPoly& b, int shift) {
    BitPoly r = a;
    if (b.is_zero()) return r;
    int ws = shift >> 6, bs = shift & 63;
    int bd = b.deg();
    int max_w = ((bd + shift) >> 6) + 1;
    if ((int)r.w.size() < max_w) r.w.resize(max_w, 0);
    if (bs == 0) {
        for (size_t i = 0; i < b.w.size(); ++i) r.w[i + ws] ^= b.w[i];
    } else {
        for (size_t i = 0; i < b.w.size(); ++i) {
            uint64_t v = b.w[i];
            if (!v) continue;
            r.w[i + ws] ^= (v << bs);
            if (i + ws + 1 < r.w.size()) r.w[i + ws + 1] ^= (v >> (64 - bs));
        }
    }
    r.trim();
    return r;
}

static void xor_shift_inplace(std::vector<uint64_t>& dst, const std::vector<uint64_t>& src, int shift) {
    if (src.empty()) return;
    int ws = shift >> 6, bs = shift & 63;
    size_t need = src.size() + ws + (bs ? 1 : 0);
    if (dst.size() < need) dst.resize(need, 0);
    if (bs == 0) {
        for (size_t i = 0; i < src.size(); ++i) dst[i + ws] ^= src[i];
    } else {
        for (size_t i = 0; i < src.size(); ++i) {
            uint64_t v = src[i];
            if (!v) continue;
            dst[i + ws] ^= (v << bs);
            dst[i + ws + 1] ^= (v >> (64 - bs));
        }
    }
}

static BitPoly poly_mod(BitPoly a, const BitPoly& m) {
    int dm = m.deg();
    int da;
    while ((da = a.deg()) >= dm) {
        xor_shift_inplace(a.w, m.w, da - dm);
        a.trim();
    }
    return a;
}

static BitPoly poly_div_exact(BitPoly a, const BitPoly& m) {
    BitPoly q;
    int dm = m.deg();
    int da;
    while ((da = a.deg()) >= dm) {
        int sh = da - dm;
        q.set_bit(sh);
        xor_shift_inplace(a.w, m.w, sh);
        a.trim();
    }
    if (!a.is_zero()) { fprintf(stderr, "non-exact div!\n"); exit(1); }
    q.trim();
    return q;
}

static BitPoly poly_gcd(BitPoly a, BitPoly b) {
    while (!b.is_zero()) {
        BitPoly r = poly_mod(a, b);
        a = std::move(b);
        b = std::move(r);
    }
    return a;
}

static BitPoly poly_mul(const BitPoly& a, const BitPoly& b) {
    BitPoly r;
    int da = a.deg(), db = b.deg();
    if (da < 0 || db < 0) return r;
    r.w.assign(((da + db) >> 6) + 2, 0);
    for (int i = 0; i <= da; ++i) {
        if (a.get_bit(i)) xor_shift_inplace(r.w, b.w, i);
    }
    r.trim();
    return r;
}

static BitPoly poly_lcm(const BitPoly& a, const BitPoly& b) {
    BitPoly g = poly_gcd(a, b);
    return poly_mul(poly_div_exact(a, g), b);
}

static BitPoly poly_recip(const BitPoly& a) {
    int d = a.deg();
    BitPoly r;
    if (d < 0) return r;
    r.w.assign((d >> 6) + 1, 0);
    for (int i = 0; i <= d; ++i) {
        if (a.get_bit(i)) r.set_bit(d - i);
    }
    r.trim();
    return r;
}

// Fast Berlekamp-Massey over GF(2) on bit sequence s[0..N-1]
// Returns minimal polynomial with constant term 1 (matching check_pair_products.py)!
static BitPoly bm_gf2(const std::vector<uint8_t>& s) {
    int N = (int)s.size();
    std::vector<uint64_t> C(1, 1ULL), B(1, 1ULL);
    int L = 0, m = 1;
    // Also keep reversed window of s in bitset for O(L/64) dot product!
    // Actually even simpler: store s_rev shifted? Better: store s as array of uint64_t words where
    // s_bits[pos] is s[pos], and maintain C reversed!
    // Let's keep it super clean and fast: C[k] for k=0..L; discrepancy d = sum_{k=0}^L C[k] * s[n - k].
    // Store s in reverse order: s_rev[N - 1 - j] = s[j], so s[n - k] = s_rev[(N - 1 - n) + k]!
    int NW = (N >> 6) + 2;
    std::vector<uint64_t> s_rev(NW, 0);
    for (int j = 0; j < N; ++j) {
        if (s[j]) {
            int p = N - 1 - j;
            s_rev[p >> 6] |= (1ULL << (p & 63));
        }
    }
    for (int n = 0; n < N; ++n) {
        // Compute parity of C & (s_rev >> (N - 1 - n)) over 0..L
        int off = N - 1 - n;
        int ow = off >> 6, ob = off & 63;
        int cw = (L >> 6) + 1;
        uint64_t acc = 0;
        if (ob == 0) {
            for (int i = 0; i < cw && i < (int)C.size(); ++i) {
                acc ^= C[i] & s_rev[ow + i];
            }
        } else {
            for (int i = 0; i < cw && i < (int)C.size(); ++i) {
                uint64_t sw = (s_rev[ow + i] >> ob) | (s_rev[ow + i + 1] << (64 - ob));
                acc ^= C[i] & sw;
            }
        }
        int d = __builtin_parityll(acc);
        if (d) {
            std::vector<uint64_t> T = C;
            xor_shift_inplace(C, B, m);
            if (2 * L <= n) {
                L = n + 1 - L;
                B = std::move(T);
                m = 1;
            } else {
                ++m;
            }
        } else {
            ++m;
        }
    }
    // Reverse C of degree L: poly = sum_{k=0}^L C[k] X^{L - k}
    BitPoly res;
    res.w.assign((L >> 6) + 1, 0);
    for (int k = 0; k <= L; ++k) {
        if ((size_t)(k >> 6) < C.size() && ((C[k >> 6] >> (k & 63)) & 1ULL)) {
            res.set_bit(L - k);
        }
    }
    res.trim();
    return res;
}

static void check_trinomial(int n, int a) {
    // Build f(X) = X^n + X^a + 1
    BitPoly f;
    f.set_bit(0);
    f.set_bit(a);
    f.set_bit(n);
    int nw = (n >> 6) + 1;
    int D = n * (n - 1) / 2;
    int NP = 2 * D + 1;
    // Precompute powers[k] = X^k mod f for k = 0..2*D (flat array NP * nw)
    std::vector<uint64_t> pw((size_t)NP * nw, 0);
    pw[0] = 1ULL;
    int hi_w = n >> 6, hi_b = n & 63;
    int a_w = a >> 6, a_b = a & 63;
    for (int k = 1; k < NP; ++k) {
        const uint64_t* prev = &pw[(size_t)(k - 1) * nw];
        uint64_t* cur = &pw[(size_t)k * nw];
        uint64_t carry = 0;
        for (int i = 0; i < nw; ++i) {
            cur[i] = (prev[i] << 1) | carry;
            carry = prev[i] >> 63;
        }
        if ((cur[hi_w] >> hi_b) & 1ULL) {
            cur[hi_w] ^= (1ULL << hi_b);
            cur[a_w] ^= (1ULL << a_b);
            cur[0] ^= 1ULL;
        }
    }

    BitPoly ann;
    ann.set_bit(0); // ann = 1
    std::vector<uint64_t> rows((size_t)n * nw, 0);
    std::vector<uint8_t> seq(2 * D);

    while (true) {
        // Check surviving coordinate of ann on X^k ^ X^{k+1}
        std::fill(rows.begin(), rows.end(), 0);
        int da = ann.deg();
        for (int k = 0; k <= da; ++k) {
            if (!ann.get_bit(k)) continue;
            const uint64_t* pa = &pw[(size_t)k * nw];
            const uint64_t* pb = &pw[(size_t)(k + 1) * nw];
            for (int w = 0; w < nw; ++w) {
                uint64_t va = pa[w];
                while (va) {
                    int bit = __builtin_ctzll(va);
                    int i = (w << 6) + bit;
                    uint64_t* r = &rows[(size_t)i * nw];
                    for (int u = 0; u < nw; ++u) r[u] ^= pb[u];
                    va &= va - 1;
                }
                uint64_t vb = pb[w];
                while (vb) {
                    int bit = __builtin_ctzll(vb);
                    int i = (w << 6) + bit;
                    uint64_t* r = &rows[(size_t)i * nw];
                    for (int u = 0; u < nw; ++u) r[u] ^= pa[u];
                    vb &= vb - 1;
                }
            }
        }
        int ci = -1, cj = -1;
        for (int i = 0; i < n && ci < 0; ++i) {
            const uint64_t* r = &rows[(size_t)i * nw];
            for (int u = 0; u < nw; ++u) {
                if (r[u]) {
                    ci = i;
                    cj = (u << 6) + __builtin_ctzll(r[u]);
                    break;
                }
            }
        }
        if (ci < 0) break;
        int iw = ci >> 6, ib = ci & 63;
        int jw = cj >> 6, jb = cj & 63;
        for (int k = 0; k < 2 * D; ++k) {
            const uint64_t* pa = &pw[(size_t)k * nw];
            const uint64_t* pb = &pw[(size_t)(k + 1) * nw];
            int ai = (int)((pa[iw] >> ib) & 1ULL);
            int aj = (int)((pa[jw] >> jb) & 1ULL);
            int bi = (int)((pb[iw] >> ib) & 1ULL);
            int bj = (int)((pb[jw] >> jb) & 1ULL);
            seq[k] = (uint8_t)((ai & bj) ^ (aj & bi));
        }
        BitPoly sc = bm_gf2(seq);
        ann = poly_lcm(ann, sc);
    }

    BitPoly pairs = poly_lcm(f, ann);
    BitPoly rev = poly_recip(pairs);
    BitPoly f_rev = poly_recip(f);
    int d2 = poly_gcd(f, f_rev).deg();
    int d3 = poly_gcd(pairs, f_rev).deg();
    int d4 = poly_gcd(pairs, rev).deg();
    printf("X^%d + X^%d + 1: deg(pairs)=%d, (d2=%d, d3=%d, d4=%d) => %s\n",
           n, a, pairs.deg(), d2, d3, d4, (d2 == 0 && d3 == 0 && d4 == 0) ? "PASS ALL 4!" : "FAIL");
    fflush(stdout);
}

int main() {
    // Quick sanity check on s=4,5,6,7 + FULL s=8 (deg 253..261)!
    check_trinomial(19, 3);   // s=4 d=3 a=3: FAIL (d4=6)
    check_trinomial(31, 3);   // s=5 d=-1 a=3: PASS
    check_trinomial(63, 3);   // s=6 d=-1 a=3: PASS
    check_trinomial(255, 3);  // s=8 d=-1 a=3: MUST PASS!
    check_trinomial(255, 1);  // s=8 d=-1 a=1: MUST FAIL!
    check_trinomial(257, 2);  // s=8 d=+1 a=2: MUST PASS! (Fermat prime 257!)
    check_trinomial(257, 5);  // s=8 d=+1 a=5: MUST PASS! (Fermat prime 257!)
    check_trinomial(259, 3);  // s=8 d=+3 a=3: MUST FAIL! (4 | 8)
    check_trinomial(259, 7);  // s=8 d=+3 a=7: MUST PASS!
    check_trinomial(261, 5);  // s=8 d=+5 a=5: MUST PASS!
    check_trinomial(261, 4);  // s=8 d=+5 a=4: MUST PASS!
    check_trinomial(261, 1);  // s=8 d=+5 a=1: MUST PASS!
    return 0;
}
