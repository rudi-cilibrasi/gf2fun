// Generate and save all splitting Hermitian circle relations for q = 1024, F_2 model (h0, h1)
// Binary format: uint32_t num_vars, uint32_t num_rels; then for each rel:
//   uint16_t num_terms; followed by num_terms pairs of (uint16_t var_id, int32_t coeff)
// Also dumps var_id -> F_2 minimal polynomial mask table (uint32_t masks[num_vars])
// Compile: g++ -O3 -march=native -fopenmp dump_rel_1229_f2.cpp -o dump_rel_1229_f2
#include <bits/stdc++.h>
#include <omp.h>
using namespace std;

static constexpr int S = 10;
static constexpr int TWO_S = 20;
static constexpr uint32_t Q = 1u << TWO_S;
static constexpr uint32_t QMASK = Q - 1;
static constexpr uint32_t q_val = 1u << S;
static constexpr uint32_t MOD_POLY = (1u << 20) | (1u << 3) | 1u;

uint32_t exp_tbl[2 * Q];
uint32_t log_tbl[Q];
uint32_t frob2[Q];
uint32_t frobq[Q];
uint32_t Fq_elems[q_val];
int32_t Fq_idx[Q]; // index in 0..q-1 for elements of Fq
uint32_t norm_roots[q_val][q_val + 1]; // norm_roots[fq_i][0..q] for nonzero c
uint32_t minpoly_id[Q];
uint8_t minpoly_deg[Q];
vector<uint32_t> var_masks; // minimal polynomial mask over F_2 for each var_id
uint32_t num_vars = 0;

static inline uint32_t fmul(uint32_t a, uint32_t b) {
    if (!a || !b) return 0;
    return exp_tbl[log_tbl[a] + log_tbl[b]];
}
static inline uint32_t finv(uint32_t a) {
    return exp_tbl[QMASK - log_tbl[a]];
}

void init_field() {
    uint32_t x = 1;
    for (uint32_t i = 0; i < QMASK; ++i) {
        exp_tbl[i] = x;
        exp_tbl[i + QMASK] = x;
        log_tbl[x] = i;
        x <<= 1;
        if (x & Q) x ^= MOD_POLY;
    }
    frob2[0] = 0; frobq[0] = 0;
    for (uint32_t a = 1; a < Q; ++a) {
        uint32_t l = log_tbl[a];
        frob2[a] = exp_tbl[(l * 2) % QMASK];
        frobq[a] = exp_tbl[(l * q_val) % QMASK];
    }
    memset(Fq_idx, -1, sizeof(Fq_idx));
    int fq_cnt = 0;
    for (uint32_t a = 0; a < Q; ++a) {
        if (frobq[a] == a) {
            Fq_idx[a] = fq_cnt;
            Fq_elems[fq_cnt++] = a;
        }
    }
    // Precompute norm roots u^{q+1} = c for c in F_q^*
    vector<int> nr_cnt(q_val, 0);
    for (uint32_t u = 1; u < Q; ++u) {
        uint32_t nm = fmul(u, frobq[u]);
        int ci = Fq_idx[nm];
        norm_roots[ci][nr_cnt[ci]++] = u;
    }
    for (int ci = 0; ci < (int)q_val; ++ci) {
        if (Fq_elems[ci] != 0 && nr_cnt[ci] != (int)(q_val + 1)) {
            cerr << "norm_roots mismatch\n"; exit(1);
        }
    }
    // Minimal polynomial over F_2 for each Galois orbit
    vector<uint8_t> seen(Q, 0);
    for (uint32_t a = 0; a < Q; ++a) {
        if (seen[a]) continue;
        uint32_t cur = a;
        vector<uint32_t> orb;
        while (!seen[cur]) {
            seen[cur] = 1;
            orb.push_back(cur);
            cur = frob2[cur];
        }
        // Compute prod_{r in orb} (T + r)
        uint32_t coeffs[21] = {0};
        coeffs[0] = 1;
        int deg = 0;
        for (uint32_t r : orb) {
            for (int i = deg; i >= 0; --i) {
                coeffs[i + 1] ^= coeffs[i];
                coeffs[i] = fmul(coeffs[i], r);
            }
            ++deg;
        }
        uint32_t mask = 0;
        for (int i = 0; i <= deg; ++i) {
            if (coeffs[i] > 1) { cerr << "non-F2 minpoly coeff!\n"; exit(1); }
            if (coeffs[i]) mask |= (1u << i);
        }
        uint32_t id = num_vars++;
        var_masks.push_back(mask);
        for (uint32_t r : orb) {
            minpoly_id[r] = id;
            minpoly_deg[r] = (uint8_t)deg;
        }
    }
}

static inline bool splits_distinct(const uint32_t *P, int d) {
    uint32_t cur[7] = {0, 1, 0, 0, 0, 0, 0};
    int cur_d = 1;
    uint32_t sq[13];
    for (int step = 0; step < TWO_S; ++step) {
        int sq_d = 2 * cur_d;
        int clear_n = max(sq_d, d - 1);
        for (int i = 0; i <= clear_n; ++i) sq[i] = 0;
        for (int i = 0; i <= cur_d; ++i) {
            if (cur[i]) sq[2 * i] = frob2[cur[i]];
        }
        for (int i = sq_d; i >= d; --i) {
            uint32_t c = sq[i];
            if (!c) continue;
            uint32_t lc = log_tbl[c];
            for (int j = 0; j < d; ++j) {
                uint32_t pj = P[j];
                if (pj) sq[i - d + j] ^= exp_tbl[lc + log_tbl[pj]];
            }
            sq[i] = 0;
        }
        cur_d = d - 1;
        while (cur_d > 0 && sq[cur_d] == 0) --cur_d;
        for (int i = 0; i <= cur_d; ++i) cur[i] = sq[i];
    }
    return cur_d == 1 && cur[0] == 0 && cur[1] == 1;
}

// Fast Cantor-Zassenhaus / trace-split root finding for monic squarefree splitting poly P of degree d <= 6 over F_{2^20}
static inline void poly_gcd(const uint32_t *A, int da, const uint32_t *B, int db, uint32_t *G, int &dg) {
    uint32_t a[8], b[8];
    for (int i = 0; i <= da; ++i) a[i] = A[i];
    for (int i = 0; i <= db; ++i) b[i] = B[i];
    while (db >= 0 && !(db == 0 && b[0] == 0)) {
        // reduce a mod b
        uint32_t inv_lc = log_tbl[finv(b[db])];
        while (da >= db) {
            uint32_t c = a[da];
            if (c) {
                uint32_t fac = exp_tbl[log_tbl[c] + inv_lc];
                uint32_t lfac = log_tbl[fac];
                for (int j = 0; j <= db; ++j) {
                    if (b[j]) a[da - db + j] ^= exp_tbl[lfac + log_tbl[b[j]]];
                }
            }
            --da;
        }
        while (da >= 0 && a[da] == 0) --da;
        // swap a, b
        swap(da, db);
        for (int i = 0; i <= max(da, db); ++i) swap(a[i], b[i]);
        if (db < 0) break;
    }
    dg = da;
    uint32_t inv_lc = log_tbl[finv(a[dg])];
    for (int i = 0; i <= dg; ++i) G[i] = a[i] ? exp_tbl[log_tbl[a[i]] + inv_lc] : 0;
}

static inline void poly_div_exact(const uint32_t *A, int da, const uint32_t *B, int db, uint32_t *Qout, int &dq) {
    uint32_t a[8];
    for (int i = 0; i <= da; ++i) a[i] = A[i];
    dq = da - db;
    for (int i = 0; i <= dq; ++i) Qout[i] = 0;
    uint32_t inv_lc = log_tbl[finv(B[db])];
    for (int i = da; i >= db; --i) {
        uint32_t c = a[i];
        if (!c) continue;
        uint32_t fac = exp_tbl[log_tbl[c] + inv_lc];
        Qout[i - db] = fac;
        uint32_t lfac = log_tbl[fac];
        for (int j = 0; j <= db; ++j) {
            if (B[j]) a[i - db + j] ^= exp_tbl[lfac + log_tbl[B[j]]];
        }
    }
}

static void find_roots_rec(const uint32_t *P, int d, uint32_t *roots, int &rcnt, uint32_t &rng_state) {
    if (d == 0) return;
    if (d == 1) {
        roots[rcnt++] = P[0]; // monic: y + P[0] = 0 => y = P[0]
        return;
    }
    if (d == 2) {
        // y^2 + P[1]*y + P[0] = 0; solve directly by trace split below
    }
    // Compute Tr(alpha * y) mod P = sum_{k=0}^{19} (alpha*y)^{2^k} mod P
    while (true) {
        rng_state = rng_state * 1664525u + 1013904223u;
        uint32_t alpha = (rng_state >> 12) & QMASK;
        if (!alpha) alpha = 1;
        // cur = alpha * y
        uint32_t cur[7] = {0, alpha, 0, 0, 0, 0, 0};
        uint32_t tr[7] = {0, alpha, 0, 0, 0, 0, 0};
        int cur_d = 1;
        uint32_t sq[13];
        for (int step = 1; step < TWO_S; ++step) {
            int sq_d = 2 * cur_d;
            int clear_n = max(sq_d, d - 1);
            for (int i = 0; i <= clear_n; ++i) sq[i] = 0;
            for (int i = 0; i <= cur_d; ++i) {
                if (cur[i]) sq[2 * i] = frob2[cur[i]];
            }
            for (int i = sq_d; i >= d; --i) {
                uint32_t c = sq[i];
                if (!c) continue;
                uint32_t lc = log_tbl[c];
                for (int j = 0; j < d; ++j) {
                    if (P[j]) sq[i - d + j] ^= exp_tbl[lc + log_tbl[P[j]]];
                }
                sq[i] = 0;
            }
            cur_d = d - 1;
            while (cur_d > 0 && sq[cur_d] == 0) --cur_d;
            for (int i = 0; i <= cur_d; ++i) {
                cur[i] = sq[i];
                tr[i] ^= sq[i];
            }
        }
        int tr_d = d - 1;
        while (tr_d >= 0 && tr[tr_d] == 0) --tr_d;
        if (tr_d <= 0) continue;
        uint32_t G[8];
        int dg;
        poly_gcd(P, d, tr, tr_d, G, dg);
        if (dg > 0 && dg < d) {
            uint32_t Qp[8];
            int dq;
            poly_div_exact(P, d, G, dg, Qp, dq);
            find_roots_rec(G, dg, roots, rcnt, rng_state);
            find_roots_rec(Qp, dq, roots, rcnt, rng_state);
            return;
        }
    }
}

struct Rel {
    vector<pair<uint16_t, int32_t>> terms;
};

int main(int argc, char **argv) {
    uint32_t h0_mask = (argc > 1) ? stoul(argv[1]) : 37u;
    uint32_t h1_mask = (argc > 2) ? stoul(argv[2]) : 10u;
    string out_path = (argc > 3) ? argv[3] : "rels_1229_f2.bin";
    init_field();

    // Factor h1 over F_2 manually for h1=10 = x^3+x = x*(x+1)^2 (or general)
    // For h1 = 10: factors are x (mask 2, exp 1) and x+1 (mask 3, exp 2).
    vector<pair<uint16_t, int>> h1_facs;
    if (h1_mask == 10u) {
        uint16_t id_x = minpoly_id[0];      // T = x (root 0)
        uint16_t id_x1 = minpoly_id[1];     // T+1 = x+1 (root 1)
        h1_facs.push_back({id_x, 1});
        h1_facs.push_back({id_x1, 2});
    } else {
        cerr << "General h1 factorization not hardcoded yet\n";
        return 1;
    }

    vector<int> h0_bits, h1_bits;
    for (int i = 0; i < 16; ++i) {
        if ((h0_mask >> i) & 1) h0_bits.push_back(i);
        if ((h1_mask >> i) & 1) h1_bits.push_back(i);
    }
    int max_d = max(h0_bits.back(), h1_bits.back()) + 1;

    vector<uint32_t> canon_B;
    {
        vector<uint8_t> seen(Q, 0);
        for (uint32_t B = 0; B < Q; ++B) {
            if (seen[B]) continue;
            canon_B.push_back(B);
            uint32_t cur = B;
            while (!seen[cur]) { seen[cur] = 1; cur = frob2[cur]; }
        }
    }

    int nthreads = omp_get_max_threads();
    vector<vector<Rel>> thread_rels(nthreads);
    double t0 = omp_get_wtime();

    #pragma omp parallel
    {
        int tid = omp_get_thread_num();
        uint32_t rng = 123456789u ^ (tid * 2654435761u);
        vector<int32_t> acc(num_vars, 0);
        vector<uint16_t> touched;
        touched.reserve(1100);

        #pragma omp for schedule(dynamic, 64)
        for (size_t bi = 0; bi < canon_B.size(); ++bi) {
            uint32_t B = canon_B[bi];
            uint32_t Bq = frobq[B];
            uint32_t Bnorm = fmul(B, Bq);
            uint32_t baseR[8] = {0};
            for (int i : h0_bits) { baseR[i + 1] ^= 1; baseR[i] ^= Bq; }
            for (int i : h1_bits) { baseR[i + 1] ^= B; }

            for (uint32_t di = 0; di < q_val; ++di) {
                uint32_t D = Fq_elems[di];
                uint32_t c = Bnorm ^ D;
                if (c == 0) continue;
                uint32_t R[8];
                for (int i = 0; i <= max_d; ++i) R[i] = baseR[i];
                for (int i : h1_bits) R[i] ^= D;
                int d = max_d;
                while (d > 0 && R[d] == 0) --d;
                if (d <= 0) continue;
                if (R[d] != 1) {
                    uint32_t inv_lc = log_tbl[finv(R[d])];
                    for (int i = 0; i < d; ++i)
                        if (R[i]) R[i] = exp_tbl[log_tbl[R[i]] + inv_lc];
                    R[d] = 1;
                }
                if (d > 1 && !splits_distinct(R, d)) continue;
                // Find all d roots
                uint32_t roots[8];
                int rcnt = 0;
                find_roots_rec(R, d, roots, rcnt, rng);
                if (rcnt != d) continue;

                // Build relation
                touched.clear();
                int ci = Fq_idx[c];
                for (uint32_t k = 0; k <= q_val; ++k) {
                    uint32_t gam = B ^ norm_roots[ci][k];
                    uint16_t vid = (uint16_t)minpoly_id[gam];
                    if (acc[vid] == 0) touched.push_back(vid);
                    acc[vid] += (int32_t)(TWO_S / minpoly_deg[gam]);
                }
                for (auto [vid, e] : h1_facs) {
                    if (acc[vid] == 0) touched.push_back(vid);
                    acc[vid] += e * (int32_t)(q_val * TWO_S);
                }
                for (int k = 0; k < d; ++k) {
                    uint32_t delta = roots[k];
                    uint16_t vid = (uint16_t)minpoly_id[delta];
                    if (acc[vid] == 0) touched.push_back(vid);
                    acc[vid] -= (int32_t)(q_val * (TWO_S / minpoly_deg[delta]));
                }
                Rel rel;
                rel.terms.reserve(touched.size());
                for (uint16_t vid : touched) {
                    if (acc[vid] != 0) rel.terms.push_back({vid, acc[vid]});
                    acc[vid] = 0;
                }
                sort(rel.terms.begin(), rel.terms.end());
                if (!rel.terms.empty()) thread_rels[tid].push_back(move(rel));
            }
        }
    }
    uint32_t total = 0;
    for (auto &v : thread_rels) total += (uint32_t)v.size();
    cerr << "Generated " << total << " full relations in " << (omp_get_wtime() - t0) << "s!\n";

    // Write binary file
    ofstream out(out_path, ios::binary);
    out.write((char *)&num_vars, sizeof(num_vars));
    out.write((char *)&total, sizeof(total));
    out.write((char *)var_masks.data(), num_vars * sizeof(uint32_t));
    for (auto &v : thread_rels) {
        for (auto &rel : v) {
            uint16_t nt = (uint16_t)rel.terms.size();
            out.write((char *)&nt, sizeof(nt));
            for (auto &[vid, coef] : rel.terms) {
                out.write((char *)&vid, sizeof(vid));
                out.write((char *)&coef, sizeof(coef));
            }
        }
    }
    out.close();
    cerr << "Saved to " << out_path << "\n";
    return 0;
}
