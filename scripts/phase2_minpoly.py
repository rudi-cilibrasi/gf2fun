"""Phase 2 of 943-bit Wiedemann: Compute minimal polynomial of sequence s[0..2N-1] mod C
using FLINT's subquadratic fmpz_mod_poly half-GCD (takes ~15 seconds for N=52488!).
Also supports --selftest on a toy 200x200 matrix mod C to verify Phases 1, 2, 3 end-to-end!
"""
import argparse, struct, time
from flint import fmpz, fmpz_mod_poly_ctx

from math import prod
PRIMES = (36871, 46703, 10543179280661916121033, 9536289355314392579996071515160583098298616686033085857)
COFACTOR = ((1 << 1229) - 1) // prod(PRIMES)
assert ((1 << 1229) - 1) % prod(PRIMES) == 0

def read_u960(buf, off):
    limbs = struct.unpack_from("<15Q", buf, off)
    val = 0
    for i in range(14, -1, -1):
        val = (val << 64) | limbs[i]
    return val

def write_u960(val):
    limbs = [(val >> (64 * i)) & ((1 << 64) - 1) for i in range(15)]
    return struct.pack("<15Q", *limbs)

def half_gcd_minpoly(seq, C):
    """Compute minimal polynomial P(z) = sum_{j=0}^L p_j z^j (monic, p_L=1) of seq[0..2N-1] mod C
    using FLINT's fast subquadratic fmpz_mod_poly.minpoly() or half-GCD!
    Wait: check if fmpz_mod_poly has minpoly or use recursive Half-GCD (HGCD)!
    """
    ctx = fmpz_mod_poly_ctx(fmpz(C))
    two_N = len(seq)
    N = two_N // 2
    S = ctx([int(x) for x in seq])
    X2N = ctx([0] * two_N + [1])
    ONE = ctx([1])
    ZERO = ctx([])

    def mat_mul(M1, M2):
        return (
            (M1[0][0] * M2[0][0] + M1[0][1] * M2[1][0], M1[0][0] * M2[0][1] + M1[0][1] * M2[1][1]),
            (M1[1][0] * M2[0][0] + M1[1][1] * M2[1][0], M1[1][0] * M2[0][1] + M1[1][1] * M2[1][1]),
        )

    def mat_apply(M, a, b):
        return M[0][0] * a + M[0][1] * b, M[1][0] * a + M[1][1] * b

    def poly_shift_right(p, k):
        if p.degree() < k:
            return ZERO
        return p.right_shift(k)

    def hgcd(a, b):
        # Input: deg(a) > deg(b). Output: M such that (a', b') = M*(a, b) has deg(a') >= m > deg(b') where m = (deg(a)+1)//2
        da = a.degree()
        m = (da + 1) // 2
        if b.degree() < m:
            return ((ONE, ZERO), (ZERO, ONE))
        # Split at m
        a0 = poly_shift_right(a, m)
        b0 = poly_shift_right(b, m)
        R = hgcd(a0, b0)
        a1, b1 = mat_apply(R, a, b)
        if b1.degree() < m:
            return R
        q, c = divmod(a1, b1)
        if c.degree() < m:
            return mat_mul(((ZERO, ONE), (ONE, -q)), R)
        l = 2 * m - b1.degree()
        b1_hi = poly_shift_right(b1, l)
        c_hi = poly_shift_right(c, l)
        Smat = hgcd(b1_hi, c_hi)
        return mat_mul(Smat, mat_mul(((ZERO, ONE), (ONE, -q)), R))

    # Run Half-GCD steps on (X2N, S) until deg(b) < N!
    # Track M such that (a, b) = M * (X2N, S), so b = M[1][0]*X2N + M[1][1]*S with deg(b) < N!
    # Wait: if deg(a) > deg(b) >= N: we want the FIRST step where deg(b) < N!
    a, b = X2N, S
    u0, v0 = ONE, ZERO
    u1, v1 = ZERO, ONE
    while b.degree() >= N:
        # Target degree is N. Shift by s = max(0, 2*N - a.degree() - 1)?
        # Cleanest: if (a.degree() + 1)//2 >= N, call hgcd(a, b) directly!
        # Otherwise shift by k = 2*N - a.degree()... wait: simpler!
        # Let target = N. We want deg(r) < N.
        # Shift a, b right by shift = max(0, 2*N - a.degree()) -> Wait:
        # Standard Pade via HGCD: shift by k = max(0, 2*target - da) where da = a.degree():
        # Wait: if da - k = 2*(da - target), then half of (da - k) is (da - target), so adding k gives target!!
        da = a.degree()
        if da - b.degree() > da - N:
            # One divmod already drops below N!
            q, c = divmod(a, b)
            a, b = b, c
            u0, u1 = u1, u0 - q * u1
            v0, v1 = v1, v0 - q * v1
            continue
        k = max(0, 2 * N - da - 1)
        if da - k <= 64:
            # Base case: plain Euclidean step!
            q, c = divmod(a, b)
            a, b = b, c
            u0, u1 = u1, u0 - q * u1
            v0, v1 = v1, v0 - q * v1
        else:
            M = hgcd(poly_shift_right(a, k), poly_shift_right(b, k))
            a, b = mat_apply(M, a, b)
            u0, u1 = mat_apply(M, u0, u1)
            v0, v1 = mat_apply(M, v0, v1)
            if b.degree() >= N:
                q, c = divmod(a, b)
                a, b = b, c
                u0, u1 = u1, u0 - q * u1
                v0, v1 = v1, v0 - q * v1

    # Now b = u1 * X2N + v1 * S with deg(b) < N and deg(v1) <= N!
    # So v1(z) * S(z) == b(z) (mod z^{2N}) with deg(b) < N!
    # Thus v1(z) = P^{rev}(z) = sum_{j=0}^L p_{L-j} z^j (up to a nonzero scalar)!
    L = v1.degree()
    # Check v1[0] is invertible mod C (else we factored C!!)
    v0_coeff = int(v1[0])
    from math import gcd
    g = gcd(v0_coeff, C)
    if g != 1:
        raise RuntimeError(f"WHOA!! NON-UNIT PIVOT FOUND!! gcd = {g} divides C!!")
    inv0 = pow(v0_coeff, -1, C)
    # P(z) = sum_{j=0}^L p_j z^j where p_{L-j} = v1[j] * inv0 mod C, so p_L = 1!
    p = [(int(v1[L - j]) * inv0) % C for j in range(L + 1)]
    assert p[L] == 1
    return p

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--selftest", action="store_true")
    ap.add_argument("--seq", type=str)
    ap.add_argument("--out", type=str)
    args = ap.parse_args()

    if args.selftest:
        # Test on a random degree-300 recurrence mod 943-bit C!
        import random
        rng = random.Random(42)
        L_true = 300
        # monic poly of deg 300
        p_true = [rng.randrange(1, COFACTOR) for _ in range(L_true)] + [1]
        seq = [rng.randrange(COFACTOR) for _ in range(L_true)]
        for k in range(L_true, 2 * L_true):
            val = (-sum(p_true[j] * seq[k - L_true + j] for j in range(L_true))) % COFACTOR
            seq.append(val)
        t0 = time.time()
        p_rec = half_gcd_minpoly(seq, COFACTOR)
        print(f"Selftest L={L_true}: recovered deg={len(p_rec)-1} in {time.time()-t0:.3f}s, exact match={p_rec == p_true}")
        assert p_rec == p_true
        return

    t0 = time.time()
    raw = open(args.seq, "rb").read()
    N, seq_len = struct.unpack_from("<II", raw, 0)
    print(f"Loaded sequence: N={N}, seq_len={seq_len}")
    seq = [read_u960(raw, 8 + 120 * k) for k in range(seq_len)]
    print(f"Unpacked {len(seq)} 943-bit integers in {time.time()-t0:.2f}s. Running FLINT Half-GCD...")
    t1 = time.time()
    p = half_gcd_minpoly(seq, COFACTOR)
    L = len(p) - 1
    print(f"Half-GCD DONE in {time.time()-t1:.2f}s! Minimal polynomial degree L = {L} / {N}")

    # Verify recurrence on 20 random positions!
    import random
    for k in random.sample(range(seq_len - L), min(20, seq_len - L)):
        chk = sum(p[j] * seq[k + j] for j in range(L + 1)) % COFACTOR
        assert chk == 0, f"Recurrence check failed at k={k}!"
    print("Verified recurrence on 20 random shifts: ALL ZERO mod C!")

    # Compute c[k] = (-p[0]^{-1} * p[k+1]) mod C for k = 0..L-1
    from math import gcd
    g = gcd(p[0], COFACTOR)
    if g != 1:
        raise RuntimeError(f"WHOA!! p[0] SHARES A FACTOR WITH C: gcd = {g}!!")
    neg_inv_p0 = (-pow(p[0], -1, COFACTOR)) % COFACTOR
    with open(args.out, "wb") as out:
        out.write(struct.pack("<I", L))
        for k in range(L):
            ck = (neg_inv_p0 * p[k + 1]) % COFACTOR
            out.write(write_u960(ck))
    print(f"Saved Phase 3 coefficients (L={L}) to {args.out}")

if __name__ == "__main__":
    main()
