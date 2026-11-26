"""Standalone exact algebraic prover & empirical cross-checker for six 100%-coverage
shifted dyadic trinomial fourth-exterior-power families:
    T_{s; d, a}(X) = X^{2^s + d} + X^a + 1

Families proved for ALL s >= s_min (and verified against data/shifted-dyadic-trinomial-4test-certificates.json):
  1. Mersenne  2^s - 1  (s >= 3): a in {1, 3}     (period 3, 2 trinomials -- all Mersenne degrees >= 7)
  2. Fermat  2^{2^k}+1  (k >= 1): a in {2, 5}     (2 trinomials -- all Fermat numbers >= 5)
  3. Even      2^s + 2  (s >= 2): a in {1, 7}     (period 12, 2 trinomials)
  4. Odd       2^s - 3  (s >= 4): a in {1, 3, 6}  (period 12, 3 trinomials)
  5. Odd       2^s + 1  (s >= 2): a in {3, 5, 9}  (period 540, 3 trinomials)
  6. Odd       2^s + 3  (s >= 1): a in {3, 4, 7}  (period 84, 3 trinomials)
  7. Odd       2^s + 5  (s >= 1): a in {1, 4, 5}  (period 252, 3 trinomials)

Uses the Universal K(1) = 1 Theorem: any product-one m-tuple of roots of the reciprocal
X^{2^s+d} + X^{2^s+b} + 1 (b = d - a) gives z_i = x_i^a with prod z_i = 1,
K(1) = prod(z_i + 1) = (prod x_i)^{-(2^s+b)} = 1, and z_i^{2^s} = z_i^{-b}(z_i+1)^{-a}.
"""
import json
import random
import sys
import time
from math import gcd as igcd, lcm
from pathlib import Path

from flint import nmod_mpoly_ctx, nmod_poly

REPO_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO_ROOT / "scripts"))
import check_pair_products as cpp  # noqa: E402


def mat_mul(A, B, m, zero):
    C = [[zero] * m for _ in range(m)]
    for i in range(m):
        for j in range(m):
            s = zero
            for r in range(m):
                s = s + A[i][r] * B[r][j]
            C[i][j] = s
    return C


def mat_pow(A, e, m, zero, one):
    P = [[one if i == j else zero for j in range(m)] for i in range(m)]
    B = A
    while e:
        if e & 1:
            P = mat_mul(P, B, m, zero)
        B = mat_mul(B, B, m, zero)
        e >>= 1
    return P


def charpoly_coeffs_3(P, zero):
    s1 = P[0][0] + P[1][1] + P[2][2]
    s2 = (
        P[0][0] * P[1][1] + P[0][1] * P[1][0]
        + P[0][0] * P[2][2] + P[0][2] * P[2][0]
        + P[1][1] * P[2][2] + P[1][2] * P[2][1]
    )
    return s1, s2


def charpoly_coeffs_4(P, zero):
    s1 = P[0][0] + P[1][1] + P[2][2] + P[3][3]
    s2 = zero
    for i in range(4):
        for j in range(i + 1, 4):
            s2 = s2 + P[i][i] * P[j][j] + P[i][j] * P[j][i]
    s3 = zero
    for skip in range(4):
        idx = [i for i in range(4) if i != skip]
        a00, a01, a02 = P[idx[0]][idx[0]], P[idx[0]][idx[1]], P[idx[0]][idx[2]]
        a10, a11, a12 = P[idx[1]][idx[0]], P[idx[1]][idx[1]], P[idx[1]][idx[2]]
        a20, a21, a22 = P[idx[2]][idx[0]], P[idx[2]][idx[1]], P[idx[2]][idx[2]]
        s3 = s3 + (
            a00 * (a11 * a22 + a12 * a21)
            + a01 * (a10 * a22 + a12 * a20)
            + a02 * (a10 * a21 + a11 * a20)
        )
    return s1, s2, s3


def to_uni1(p, z):
    if p == z:
        return nmod_poly([0], 2)
    d = int(p.degrees()[0])
    c = [0] * (d + 1)
    for (e,), coef in p.terms():
        c[e] = int(coef)
    return nmod_poly(c, 2)


def to_uni2(p, z):
    if p == z:
        return nmod_poly([0], 2)
    d = int(p.degrees()[0])
    c = [0] * (d + 1)
    for (ea, ec), coef in p.terms():
        assert ec == 0
        c[ea] = int(coef)
    return nmod_poly(c, 2)


def compose2(poly, A, C, z, o):
    if poly == z:
        return z
    max_ea, max_ec = int(poly.degrees()[0]), int(poly.degrees()[1])
    Ap = [o]
    for _ in range(max_ea):
        Ap.append(Ap[-1] * A)
    Cp = [o]
    for _ in range(max_ec):
        Cp.append(Cp[-1] * C)
    res = z
    for (ea, ec), coef in poly.terms():
        if int(coef):
            res = res + Ap[ea] * Cp[ec]
    return res


def build_M3(u, z, o):
    M = [[z, z, o], [o, z, u + o], [z, o, u]]
    Minv = [[u + o, o, z], [u, z, o], [o, z, z]]
    U = [[M[i][j] + (o if i == j else z) for j in range(3)] for i in range(3)]
    U2 = mat_mul(U, U, 3, z)
    Uinv = [[U2[i][j] + (u + o) * U[i][j] + (u if i == j else z) for j in range(3)] for i in range(3)]
    return M, Minv, U, Uinv


def build_M4(u, w, z, o):
    v = u + w + o
    M = [[z, z, z, o], [o, z, z, w], [z, o, z, v], [z, z, o, u]]
    Minv = [[w, o, z, z], [v, z, o, z], [u, z, z, o], [o, z, z, z]]
    U = [[M[i][j] + (o if i == j else z) for j in range(4)] for i in range(4)]
    U2 = mat_mul(U, U, 4, z)
    U3 = mat_mul(U2, U, 4, z)
    Uinv = [
        [U3[i][j] + u * U2[i][j] + (w + o) * U[i][j] + ((u + w) if i == j else z) for j in range(4)]
        for i in range(4)
    ]
    return M, Minv, U, Uinv


def kc_trim(p):
    while p and p[-1].is_zero():
        p.pop()
    return p


def kc_inv(x, f_mod):
    g, s, _ = x.xgcd(f_mod)
    assert g == nmod_poly([1], 2)
    return s % f_mod


def kc_mul(p, q, f_mod):
    if not p or not q:
        return []
    r = [nmod_poly([0], 2) for _ in range(len(p) + len(q) - 1)]
    for i, a in enumerate(p):
        if not a.is_zero():
            for j, b in enumerate(q):
                if not b.is_zero():
                    r[i + j] = r[i + j] + ((a * b) % f_mod)
    return kc_trim(r)


def kc_mod(p, m, f_mod):
    r = list(p)
    dm = len(m) - 1
    inv_lc = kc_inv(m[-1], f_mod)
    while len(r) - 1 >= dm:
        if not r[-1].is_zero():
            coef = (r[-1] * inv_lc) % f_mod
            shift = len(r) - 1 - dm
            for i in range(dm + 1):
                r[shift + i] = r[shift + i] + ((coef * m[i]) % f_mod)
        r.pop()
    return kc_trim(r)


def kc_div(p, m, f_mod):
    r = list(p)
    dm = len(m) - 1
    q = [nmod_poly([0], 2) for _ in range(max(0, len(r) - dm))]
    inv_lc = kc_inv(m[-1], f_mod)
    while len(r) - 1 >= dm:
        if not r[-1].is_zero():
            coef = (r[-1] * inv_lc) % f_mod
            shift = len(r) - 1 - dm
            q[shift] = coef
            for i in range(dm + 1):
                r[shift + i] = r[shift + i] + ((coef * m[i]) % f_mod)
        r.pop()
    assert kc_trim(r) == []
    return kc_trim(q)


def kc_gcd(p, q, f_mod):
    while q:
        p, q = q, kc_mod(p, q, f_mod)
    if p:
        inv_lc = kc_inv(p[-1], f_mod)
        p = [(c * inv_lc) % f_mod for c in p]
    return p


def kc_powmod(base, exp, modp, f_mod):
    res = [nmod_poly([1], 2)]
    bp = kc_mod(base, modp, f_mod)
    while exp:
        if exp & 1:
            res = kc_mod(kc_mul(res, bp, f_mod), modp, f_mod)
        bp = kc_mod(kc_mul(bp, bp, f_mod), modp, f_mod)
        exp >>= 1
    return res


def kc_deriv(p):
    return kc_trim([p[i] if (i & 1) else nmod_poly([0], 2) for i in range(1, len(p))])


def k_frob(elem, s, f_mod):
    d = f_mod.degree()
    s %= d
    cur = elem
    for _ in range(s):
        cur = (cur * cur) % f_mod
    return cur


def kc_sqfree_factors(p, f_mod):
    p = kc_trim(p)
    if len(p) <= 1:
        return []
    dp = kc_deriv(p)
    if not dp:
        d = f_mod.degree()
        q = [k_frob(p[2 * i], d - 1, f_mod) for i in range(0, len(p) // 2 + 1)]
        return kc_sqfree_factors(q, f_mod)
    g = kc_gcd(p, dp, f_mod)
    if len(g) == 1:
        return [p]
    return kc_sqfree_factors(kc_div(p, g, f_mod), f_mod) + kc_sqfree_factors(g, f_mod)


def kc_edf(g, deg_fac, f_mod):
    if len(g) - 1 == deg_fac:
        return [g]
    rng = random.Random(777)
    d = f_mod.degree()

    def split(poly):
        if len(poly) - 1 == deg_fac:
            return [poly]
        while True:
            r_poly = kc_trim([nmod_poly([rng.randrange(2) for _ in range(d)], 2) for _ in range(len(poly) - 1)])
            if not r_poly:
                continue
            tr = []
            cur = kc_mod(r_poly, poly, f_mod)
            for _ in range(d * deg_fac):
                if len(cur) > len(tr):
                    tr.extend([nmod_poly([0], 2)] * (len(cur) - len(tr)))
                for i, c in enumerate(cur):
                    tr[i] = tr[i] + c
                cur = kc_mod(kc_mul(cur, cur, f_mod), poly, f_mod)
            h = kc_gcd(poly, kc_trim(tr), f_mod)
            if 1 < len(h) < len(poly):
                return split(h) + split(kc_div(poly, h, f_mod))

    return split(g)


def kc_factor_irred(p, f_mod):
    d = f_mod.degree()
    out = []
    f = list(p)
    k = 1
    while len(f) > 1:
        wp = [nmod_poly([0], 2), nmod_poly([1], 2)]
        for _ in range(d * k):
            wp = kc_mod(kc_mul(wp, wp, f_mod), f, f_mod)
        if len(wp) < 2:
            wp.extend([nmod_poly([0], 2)] * (2 - len(wp)))
        wp[1] = wp[1] + nmod_poly([1], 2)
        wp = kc_trim(wp)
        g = kc_gcd(f, wp, f_mod)
        if len(g) > 1:
            f = kc_div(f, g, f_mod)
            out.extend(kc_edf(g, k, f_mod))
        k += 1
    return out


def eval_poly2_in_Kc(mpoly, u_elem, f_mod, z2):
    if mpoly == z2:
        return []
    du = int(mpoly.degrees()[0])
    dw = int(mpoly.degrees()[1])
    up = [nmod_poly([1], 2)]
    for _ in range(du):
        up.append((up[-1] * u_elem) % f_mod)
    res = [nmod_poly([0], 2) for _ in range(dw + 1)]
    for (eu, ew), coef in mpoly.terms():
        if int(coef):
            res[ew] = res[ew] + up[eu]
    return kc_trim(res)


def eval_mpoly_pt(mpoly, u_val, w_val, f_mod):
    du = int(mpoly.degrees()[0])
    dw = int(mpoly.degrees()[1])
    up = [nmod_poly([1], 2)]
    for _ in range(du):
        up.append((up[-1] * u_val) % f_mod)
    wp = [nmod_poly([1], 2)]
    for _ in range(dw):
        wp.append((wp[-1] * w_val) % f_mod)
    res = nmod_poly([0], 2)
    for (eu, ew), coef in mpoly.terms():
        if int(coef):
            res = res + ((up[eu] * wp[ew]) % f_mod)
    return res


def multiplicative_order_mod2(m):
    if m <= 1:
        return 1
    k = 1
    cur = 2 % m
    while cur != 1:
        cur = (cur * 2) % m
        k += 1
    return k


def check_roots_with_xlift(K_poly_in_K, f_mod, d_shift, a_tap):
    b = d_shift - a_tap
    d = f_mod.degree()
    sqf = kc_sqfree_factors(K_poly_in_K, f_mod)
    irreds = []
    for sfac in sqf:
        irreds.extend(kc_factor_irred(sfac, f_mod))

    a_odd = a_tap
    while a_odd % 2 == 0:
        a_odd //= 2

    L = 1
    per_factor = []
    for g in irreds:
        r = len(g) - 1
        P = d * r
        Z = [nmod_poly([0], 2), nmod_poly([1], 2)]
        Zp1 = [nmod_poly([1], 2), nmod_poly([1], 2)]
        lhs_factor = kc_powmod(Zp1, a_tap, g, f_mod)
        if b >= 0:
            lhs_factor = kc_mod(kc_mul(lhs_factor, kc_powmod(Z, b, g, f_mod), f_mod), g, f_mod)
            rhs = [nmod_poly([1], 2)]
        else:
            rhs = kc_powmod(Z, -b, g, f_mod)
        cur = kc_mod(Z, g, f_mod)
        good_z = set()
        for s in range(1, P + 1):
            cur = kc_mod(kc_mul(cur, cur, f_mod), g, f_mod)
            if kc_mod(kc_mul(cur, lhs_factor, f_mod), g, f_mod) == rhs:
                good_z.add(s % P)

        if not good_z:
            return 1, []
        if a_odd == 1:
            L = lcm(L, P)
            per_factor.append((P, good_z))
            continue

        pow2P_mod = pow(2, P, a_odd)
        sm = 0
        t_mult = 0
        cur_p = 1
        for t in range(1, a_odd * a_odd + 5):
            sm = (sm + cur_p) % a_odd
            cur_p = (cur_p * pow2P_mod) % a_odd
            if sm == 0:
                t_mult = t
                break
        assert t_mult > 0
        P_ext = lcm(P * t_mult, multiplicative_order_mod2(a_odd))

        good_x = set()
        order_Z = (1 << P) - 1
        for s0 in range(P_ext):
            if (s0 % P) not in good_z:
                continue
            s_eff = s0
            while s_eff < 10:
                s_eff += P_ext
            g_div = igcd(a_odd, (pow(2, s_eff, a_odd) + b) % a_odd)
            if g_div == 1:
                good_x.add(s0)
                continue
            mod_big = g_div * order_Z
            val_big = (pow(2, s_eff, mod_big) + b) % mod_big
            assert val_big % g_div == 0
            exp_Z = val_big // g_div
            exp_Zp1 = a_tap // g_div
            lhs1 = kc_powmod(Z, exp_Z, g, f_mod)
            lhs2 = kc_powmod(Zp1, exp_Zp1, g, f_mod)
            if kc_mod(kc_mul(lhs1, lhs2, f_mod), g, f_mod) == [nmod_poly([1], 2)]:
                good_x.add(s0)
        L = lcm(L, P_ext)
        per_factor.append((P_ext, good_x))

    valid_s = [s for s in range(L) if all((s % P) in gs for P, gs in per_factor)]
    return L, valid_s


def classify_trinomial(d, a):
    b = d - a
    ctx1 = nmod_mpoly_ctx.get(("u",), 2)
    (u1,) = ctx1.gens()
    z1, o1 = ctx1.constant(0), ctx1.constant(1)
    M3, M3i, U3, U3i = build_M3(u1, z1, o1)
    P3_b = mat_pow(M3i, b, 3, z1, o1) if b >= 0 else mat_pow(M3, -b, 3, z1, o1)
    P3 = mat_mul(P3_b, mat_pow(U3i, a, 3, z1, o1), 3, z1)
    s1_3, s2_3 = charpoly_coeffs_3(P3, z1)
    E1_3 = to_uni1(s1_3 + s2_3 + o1, z1)
    s1_3_uni = to_uni1(s1_3, z1)
    assert not E1_3.is_zero()

    triple_hits = []
    for f_mod, _ in E1_3.factor()[1]:
        deg_u = f_mod.degree()
        u_gen = nmod_poly([0, 1], 2) % f_mod
        u_img = nmod_poly([0], 2)
        for i in range(s1_3_uni.degree(), -1, -1):
            u_img = (u_img * u_gen) % f_mod
            if int(s1_3_uni[i]):
                u_img = u_img + nmod_poly([1], 2)
        if any(k_frob(u_gen, s, f_mod) == u_img for s in range(1, deg_u + 1)):
            K3 = [nmod_poly([1], 2), (u_gen + nmod_poly([1], 2)) % f_mod, u_gen, nmod_poly([1], 2)]
            L, valid_s = check_roots_with_xlift(K3, f_mod, d, a)
            if valid_s:
                triple_hits.append((L, valid_s))

    ctx2 = nmod_mpoly_ctx.get(("u", "w"), 2)
    u2, w2 = ctx2.gens()
    z2, o2 = ctx2.constant(0), ctx2.constant(1)
    M4, M4i, U4, U4i = build_M4(u2, w2, z2, o2)
    P4_b = mat_pow(M4i, b, 4, z2, o2) if b >= 0 else mat_pow(M4, -b, 4, z2, o2)
    P4 = mat_mul(P4_b, mat_pow(U4i, a, 4, z2, o2), 4, z2)
    a1, b1, c1 = charpoly_coeffs_4(P4, z2)
    E1 = a1 + b1 + c1 + o2
    assert E1 != z2
    E2 = compose2(E1, a1, c1, z2, o2)
    Ru = to_uni2(E1.resultant(E2, 1), z2)
    assert not Ru.is_zero()

    quartet_hits = []
    for f_mod, _ in Ru.factor()[1]:
        deg_u = f_mod.degree()
        u_gen = nmod_poly([0, 1], 2) % f_mod
        e1_w = eval_poly2_in_Kc(E1, u_gen, f_mod, z2)
        e2_w = eval_poly2_in_Kc(E2, u_gen, f_mod, z2)
        assert e1_w or e2_w
        g = kc_gcd(e1_w, e2_w, f_mod)
        irreds = []
        for sf in kc_sqfree_factors(g, f_mod):
            irreds.extend(kc_factor_irred(sf, f_mod))
        for ir in irreds:
            r = len(ir) - 1
            if r == 1:
                w_val = ir[0]
                na = eval_mpoly_pt(a1, u_gen, w_val, f_mod)
                nc = eval_mpoly_pt(c1, u_gen, w_val, f_mod)
                if any(
                    k_frob(u_gen, s, f_mod) == na and k_frob(w_val, s, f_mod) == nc
                    for s in range(1, deg_u + 1)
                ):
                    v_val = (u_gen + w_val + nmod_poly([1], 2)) % f_mod
                    K4 = [nmod_poly([1], 2), w_val, v_val, u_gen, nmod_poly([1], 2)]
                    L, valid_s = check_roots_with_xlift(K4, f_mod, d, a)
                    if valid_s:
                        quartet_hits.append((L, valid_s))
            else:
                a1_w = kc_mod(eval_poly2_in_Kc(a1, u_gen, f_mod, z2), ir, f_mod)
                c1_w = kc_mod(eval_poly2_in_Kc(c1, u_gen, f_mod, z2), ir, f_mod)
                P = deg_u * r
                W_cur = [nmod_poly([0], 2), nmod_poly([1], 2)]
                u_cur = u_gen
                frob_s = []
                for s in range(1, P + 1):
                    u_cur = (u_cur * u_cur) % f_mod
                    W_cur = kc_mod(kc_mul(W_cur, W_cur, f_mod), ir, f_mod)
                    u_const = [] if u_cur.is_zero() else [u_cur]
                    if a1_w == u_const and c1_w == W_cur:
                        frob_s.append(s % P)
                if frob_s:
                    quartet_hits.append((P, frob_s))

    L_all = 1
    for L, _ in triple_hits + quartet_hits:
        L_all = lcm(L_all, L)
    bad = {s for s in range(L_all) if any((s % L) in vs for L, vs in triple_hits + quartet_hits)}
    for div in range(1, L_all + 1):
        if L_all % div == 0 and all(((s + div) % L_all in bad) == (s in bad) for s in range(L_all)):
            L_min = div
            bad = sorted(s for s in bad if s < L_min)
            break
    good = sorted(s for s in range(L_min) if s not in bad)
    return L_min, good, bad, Ru.degree()


FAMILIES = [
    ("Mersenne 2^s - 1", -1, [1, 3], [1, 3], 3),
    ("Even 2^s + 2", 2, [1, 7], [1, 7], 2),
    ("Odd 2^s - 3", -3, [1, 3, 6], [1, 3, 6], 4),
    ("Fermat-type 2^s+1", 1, [2, 3, 5, 9], [3, 5, 9], 2),
    ("Odd 2^s + 3", 3, [3, 4, 7], [3, 4, 7], 1),
    ("Odd 2^s + 5", 5, [1, 4, 5], [1, 4, 5], 1),
]


def main() -> None:
    if not __debug__:
        raise RuntimeError("the quartet proof requires Python assertions; run without -O")
    t0 = time.time()
    cert_path = REPO_ROOT / "data" / "shifted-dyadic-trinomial-4test-certificates.json"
    saved = json.loads(cert_path.read_text())
    emp_checks = 0

    for idx, (name, d, taps, cover_taps, s_min) in enumerate(FAMILIES):
        saved_fam = saved["families"][idx]
        assert saved_fam["shift_d"] == d and saved_fam["cover_taps"] == cover_taps
        fam_map = {}
        for j, a in enumerate(taps):
            L, good, bad, degR = classify_trinomial(d, a)
            st = saved_fam["trinomials"][j]
            assert (st["a"], st["deg_Res"], st["period_L"], st["pass_residues"]) == (a, degR, L, good)
            fam_map[a] = (L, set(good))
            for s in range(1, 8):
                n = (1 << s) + d
                if n <= a or n < 5:
                    continue
                poly = (1 << n) | (1 << a) | 1
                assert cpp.gcd(poly, cpp.derivative(poly)) == 1
                d2, d3, d4 = cpp.reciprocal_defects(poly)
                if (s % L) in fam_map[a][1]:
                    assert d2 == 0 and d3 == 0 and d4 == 0
                emp_checks += 1

        L_comb = 1
        for a in cover_taps:
            L_comb = lcm(L_comb, fam_map[a][0])
        assert all(any((s % fam_map[a][0]) in fam_map[a][1] for a in cover_taps) for s in range(L_comb))
        for s in range(s_min, 20):
            n = (1 << s) + d
            assert any(a < n and (s % fam_map[a][0]) in fam_map[a][1] for a in cover_taps)
        if d == 1:
            for k in range(1, 50):
                s_mod = pow(2, k, 180)
                assert (s_mod % fam_map[2][0]) in fam_map[2][1] or (s_mod % fam_map[5][0]) in fam_map[5][1]
        print(f"VERIFIED 100% cover for {name}: taps={cover_taps}, combined period L={L_comb}, s >= {s_min}")

    print(f"All six 100%-coverage shifted dyadic trinomial theorems verified ({emp_checks} empirical s<=7 checks, 0 violations) in {time.time()-t0:.2f}s.")


if __name__ == "__main__":
    main()
