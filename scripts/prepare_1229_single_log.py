"""Build both sides of the single remaining discrete logarithm for a sparse degree-1229 candidate."""

import argparse
import json
from math import gcd

from check_1229_frobenius_models import TABLE, power_basis_expression
from check_1229_single_log import verify_single_scalar
from check_degree_1229 import COFACTOR, KNOWN, check_known_order
from check_factor_base import DATA, irreducible, modulus, polynomial
from period_coordinate import CANDIDATES, DEGREE, coordinate, mask_of


CERT = DATA / "degree-1229-q1024-certificate.json"


def prepare(taps):
    if len(taps) != 3 or not 0 < taps[0] < taps[1] < taps[2] < DEGREE:
        raise ValueError("expected three distinct increasing interior exponents")
    sparse = modulus(DEGREE, taps)
    if not irreducible(sparse):
        raise ValueError("the supplied pentanomial is reducible")
    check_known_order(sparse)
    model, = (r for r in json.loads(TABLE.read_text()) if r["q"] == 1024)
    field_mask = int(model["modulus_hex"], 16)
    if field_mask != int(json.loads(CERT.read_text())["modulus_hex"], 16):
        raise ArithmeticError("the field and projected-log certificates disagree")
    field = polynomial(field_mask)
    period_in_field = polynomial(int(model["period_hex"], 16))
    period_in_sparse = coordinate(sparse)
    x_in_period = power_basis_expression(mask_of(period_in_field), 2, field_mask)
    r_in_period = power_basis_expression(mask_of(period_in_sparse), 2, mask_of(sparse))
    x_in_sparse = x_in_period.compose_mod(period_in_sparse, sparse)
    r_in_field = r_in_period.compose_mod(period_in_field, field)
    x = polynomial(2)
    if (field.compose_mod(x_in_sparse, sparse) != 0 or sparse.compose_mod(r_in_field, field) != 0
            or r_in_field.compose_mod(x_in_sparse, sparse) != x):
        raise ArithmeticError("the field maps do not identify the two roots")
    return sparse, field, x_in_sparse, r_in_field


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    candidate = parser.add_mutually_exclusive_group()
    candidate.add_argument("--candidate", choices=CANDIDATES, help="default: product")
    candidate.add_argument("--taps", type=int, nargs=3, metavar=("A", "B", "C"))
    log = parser.add_mutually_exclusive_group()
    log.add_argument("--forward-log", type=int, help="d with (x^K)^d = r^K")
    log.add_argument("--reverse-log", type=int, help="e with (r^K)^e = x^K")
    args = parser.parse_args()
    taps = args.taps or CANDIDATES[args.candidate or "product"]
    sparse, field, x_in_sparse, r_in_field = prepare(taps)
    x = polynomial(2)
    base = x.pow_mod(KNOWN, field)
    target = r_in_field.pow_mod(KNOWN, field)
    if args.forward_log is not None:
        d = args.forward_log
        if not 0 <= d < COFACTOR or base.pow_mod(d, field) != target:
            raise ValueError("the supplied forward logarithm does not satisfy the projected field identity")
        index = gcd(d, COFACTOR)
        if index != 1:
            print(f"The root has exact index {index} in the full multiplicative group.")
            return
        verify_single_scalar(sparse, x_in_sparse, pow(d, -1, COFACTOR), CERT)
    elif args.reverse_log is not None:
        verify_single_scalar(sparse, x_in_sparse, args.reverse_log, CERT)
    else:
        print(json.dumps({
            "taps": list(taps), "known_part_K": str(KNOWN), "cofactor_C": str(COFACTOR),
            "model_modulus_hex": hex(mask_of(field)), "sparse_modulus_hex": hex(mask_of(sparse)),
            "sparse_root_in_model_hex": hex(mask_of(r_in_field)),
            "model_root_in_sparse_hex": hex(mask_of(x_in_sparse)),
            "forward_base_in_model_hex": hex(mask_of(base)),
            "forward_target_in_model_hex": hex(mask_of(target)),
        }, indent=2))


if __name__ == "__main__":
    main()
