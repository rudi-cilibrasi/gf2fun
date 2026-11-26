"""Verify degree-two Frobenius models and the embeddings of both binary pentanomials."""

import argparse
import gzip
import json
from concurrent.futures import ProcessPoolExecutor

from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_degree_1229 import COFACTOR, KNOWN
from check_factor_base import DATA
from period_coordinate import CANDIDATES, DEGREE, period_polynomial, mask_of


CERTIFICATE = DATA / "degree-1229-height-two-models.json.gz"
Q = 1024


def binary_polynomial(mask, ring):
    return ring([mask >> i & 1 for i in range(mask.bit_length())])


def scalar(mask, field):
    return field([mask >> i & 1 for i in range(mask.bit_length())])


def pack_relative(poly):
    def bits(c):
        return sum(int(bit) << i for i, bit in enumerate(c.to_list()))
    return hex(sum(bits(c) << (10*i) for i, c in enumerate(poly)))


def check_pencil(row, theta_mask):
    field = fq_default_ctx(modulus=fmpz_mod_poly_ctx(2)([1, 0, 0, 1] + [0]*16 + [1]), var="w")
    ring = fq_default_poly_ctx(field)
    t = ring.gen()
    theta = scalar(theta_mask, field)
    if theta**10+theta**3+1 != 0:
        raise ArithmeticError("incorrect embedding of the ten-bit constants")
    h0 = binary_polynomial(row["u"], ring)(theta)
    h1 = t**2+t+binary_polynomial(row["v"], ring)(theta)
    record = row["sample_pencil"]
    b, d = scalar(record["b"], field), scalar(record["d"], field)
    quadratic = ring([scalar(c, field) for c in record["quadratic"]])
    linear = t+scalar(record["linear_root"], field)
    if (d**Q != d or d == b**(Q+1) or quadratic.degree() != 2
            or not quadratic.leading_coefficient().is_one() or not quadratic.is_irreducible()):
        raise ArithmeticError("invalid quadratic pencil")
    numerator = (t+b)*h0 + (b**Q*t+d)*h1
    if numerator.monic() != quadratic*linear:
        raise ArithmeticError("the quadratic and linear cofactor do not reconstruct the numerator")
    # The finite projective source is the norm circle of radius d+N(b) centered at bar(b).
    radius = (d+b**(Q+1))**(Q//2)
    generator = field.gen()**(Q-1)
    if generator**(Q+1) != 1 or any(generator**((Q+1)//p) == 1 for p in (5, 41)):
        raise ArithmeticError("incorrect norm-one torus generator")
    product, point = ring.one(), field.one()
    for _ in range(Q+1):
        product *= t+(b**Q+radius*point)
        point *= generator
    if product != t**(Q+1)+b*t+b**Q*t**Q+d:
        raise ArithmeticError("the 1,025 finite roots do not reconstruct the Hermitian source")


def verify(args):
    row, theta_mask, base_record, period_mask, task = args
    field = fq_default_ctx(modulus=fmpz_mod_poly_ctx(2)([1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1]), var="z")
    ring = fq_default_poly_ctx(field)
    x = ring.gen()
    packed = int(row["relative_modulus_packed_hex"], 16)
    coefficients = [scalar((packed >> (10*i)) & 1023, field) for i in range(DEGREE+1)]
    g = ring(coefficients)
    u, v = scalar(row["u"], field), scalar(row["v"], field)
    parent = x**(2*Q+1)+x**(Q+1)+v*x+u
    if (packed >> (10*(DEGREE+1)) or g.degree() != DEGREE or not g.leading_coefficient().is_one()
            or parent % g != 0 or not g.is_irreducible()):
        raise ArithmeticError("invalid relative degree-1229 factor")
    conjugate, norm = g, ring.one()
    for i in range(10):
        if i and conjugate == g:
            raise ArithmeticError("the relative modulus has a short binary orbit")
        norm *= conjugate
        conjugate = ring([c*c for c in conjugate])
    binary_mask = int(row["binary_modulus_hex"], 16)
    if conjugate != g or norm != binary_polynomial(binary_mask, ring) or norm.degree() != 10*DEGREE:
        raise ArithmeticError("the absolute modulus differs from the binary coefficient norm")
    def coord(value):
        return binary_polynomial(int(value, 16), ring) % g
    if coord(row["constant_generator_hex"]) != ring([field.gen()]):
        raise ArithmeticError("the binary and relative presentations have different constants")
    y = x.pow_mod(Q, g)
    if (x*(y*y+y+v)) % g != ring([u]):
        raise ArithmeticError("the height-two Frobenius equation failed")
    period = coord(row["period_hex"])
    if binary_polynomial(period_mask, ring).compose_mod(period, g) != 0:
        raise ArithmeticError("incorrect Gauss period")
    base = coord(row["certified_generator_hex"])
    if binary_polynomial(int(base_record["modulus_hex"], 16), ring).compose_mod(base, g) != 0:
        raise ArithmeticError("the transported generator is not a root of the certified binary modulus")
    roots = {}
    for name, taps in CANDIDATES.items():
        r = coord(row["sparse_root_hex"][name])
        old_expression = binary_polynomial(int(base_record["sparse_root_hex"][name], 16), ring)
        if old_expression.compose_mod(base, g) != r or (1+sum((r.pow_mod(i, g) for i in (*taps, DEGREE)), ring.zero())) != 0:
            raise ArithmeticError(f"the {name} sparse root or its embedding failed")
        roots[name] = r
    check_pencil(row, theta_mask)
    if task:
        r = roots[task]
        return {"candidate": task, "u": row["u"], "v": row["v"], "q": Q,
                "constant_modulus_hex": "0x409", "bits_per_coefficient": 10,
                "relative_modulus_packed_hex": row["relative_modulus_packed_hex"],
                "sparse_root_packed_hex": pack_relative(r), "primitive_generator_packed_hex": pack_relative(base),
                "K": str(KNOWN), "C": str(COFACTOR), "base_packed_hex": pack_relative(base.pow_mod(KNOWN, g)),
                "target_packed_hex": pack_relative(r.pow_mod(KNOWN, g))}
    return row["u"], row["v"]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=1)
    parser.add_argument("--model", type=int, nargs=2, metavar=("U", "V"), help="select one coefficient pair")
    parser.add_argument("--task", choices=CANDIDATES, help="export the selected sparse root's forward-log task")
    args = parser.parse_args()
    if args.jobs < 1:
        parser.error("--jobs must be positive")
    with gzip.open(CERTIFICATE, "rt") as stream:
        record = json.load(stream)
    if record["q"] != Q or int(record["constant_modulus_hex"], 16) != 0x409:
        raise ValueError("incorrect base-field parameters")
    old = next(r for r in json.loads((DATA / "degree-1229-frobenius-models.json").read_text()) if r["q"] == Q)
    per = mask_of(period_polynomial(DEGREE))
    selected = args.model or ([3, 1019] if args.task else None)
    rows = [row for row in record["models"] if not selected or [row["u"], row["v"]] == selected]
    if not rows:
        parser.error("unrecognized height-two model")
    items = [(row, record["constant_generator_in_quadratic_extension"], old, per, args.task) for row in rows]
    if args.task:
        print(json.dumps(verify(items[0]), indent=2))
        return
    with ProcessPoolExecutor(max_workers=args.jobs) as pool:
        for u, v in pool.map(verify, items):
            print(f"u={u}, v={v}: relative degree 1229, binary degree 12290, both sparse roots "
                  "and the primitive binary generator verified. The sample quadratic leaves one linear factor.", flush=True)


if __name__ == "__main__":
    main()
