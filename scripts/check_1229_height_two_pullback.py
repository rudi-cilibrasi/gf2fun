"""Reduce linear norms to the leaves of a degree-two rational map over F_(2^20)."""

import argparse
import gzip
import json
from array import array
from math import gcd

from flint import fmpz_mod_poly_ctx, fq_default_ctx, fq_default_poly_ctx

from check_1229_height_two import CERTIFICATE, DEGREE, LINEAR_CONSTANT_MODULUS, Q, scalar


INFINITY = Q**2
GROUP_ORDER = (1 << DEGREE)-1
TEST_LEAVES = {(3, 1019): (3, 5, 9), (6, 246): (2, 7, 8), (6, 285): (2, 8, 11),
               (6, 454): (2, 7, 23), (7, 88): (2, 5, 15)}


def slots(initial=-1):
    return array("i", [initial]) * (INFINITY + 1)


class Constants:
    def __init__(self, theta):
        self.log = slots()
        self.power = slots()
        z = 1
        for i in range(INFINITY-1):
            self.power[i], self.log[z] = z, i
            z <<= 1
            if z & INFINITY:
                z ^= LINEAR_CONSTANT_MODULUS
        if z != 1 or min(self.log[1:INFINITY]) != 0:
            raise ArithmeticError("the residue of the binary variable does not generate the constants")
        self.real = [0]*Q
        for i in range(10):
            term = self.power[(i*self.log[theta]) % (INFINITY-1)]
            for j in range(1 << i):
                self.real[(1 << i)+j] = self.real[j] ^ term
        if len(set(self.real)) != Q or self.multiply(self.real[512], theta) != self.real[9]:
            raise ArithmeticError("incorrect embedding of the ten-bit polynomial basis")
        self.conjugate = slots()
        self.key = slots()
        for z in range(INFINITY):
            bar = self.power[(Q*self.log[z]) % (INFINITY-1)] if z else 0
            self.conjugate[z], self.key[z] = bar, min(z, bar)
        self.conjugate[INFINITY] = self.key[INFINITY] = INFINITY
        self.labels = [z for z in range(INFINITY+1) if self.key[z] == z]

        # Absolute trace is linear in the twenty binary coordinates.
        self.trace_mask = 0
        for i in range(20):
            z, tr = 1 << i, 0
            for _ in range(20):
                tr ^= z
                z = self.multiply(z, z)
            if tr not in (0, 1):
                raise ArithmeticError("the absolute trace left the binary field")
            self.trace_mask |= tr << i

    def multiply(self, a, b):
        return self.power[(self.log[a]+self.log[b]) % (INFINITY-1)] if a and b else 0

    def divide(self, a, b):
        if not b:
            raise ZeroDivisionError
        return self.power[(self.log[a]-self.log[b]) % (INFINITY-1)] if a else 0


class Pullback:
    def __init__(self, field, u, v):
        self.field = field
        self.parent, self.left, self.right = slots(), slots(), slots()
        degree = slots(0)
        u, v = field.real[u], field.real[v]
        for t in field.labels:
            if t == INFINITY:
                c = 0
            else:
                h = field.multiply(t, t) ^ t ^ v
                c = field.key[field.divide(u, h)] if h else INFINITY
            self.parent[t] = c
            if degree[c] == 0:
                self.left[c] = t
            elif degree[c] == 1:
                self.right[c] = t
            else:
                raise ArithmeticError("a quadratic fiber has more than two conjugacy classes")
            degree[c] += 1

        self.leaves = []
        for c in field.labels:
            if degree[c] == 1:
                self.right[c] = self.left[c]
            nonsplit = c not in (0, INFINITY) and ((field.divide(u, c) & field.trace_mask).bit_count() % 2)
            if bool(nonsplit) != (degree[c] == 0):
                raise ArithmeticError("the Artin-Schreier trace criterion differs from the graph fiber")
            if nonsplit:
                self.leaves.append(c)
        if len(self.leaves) != Q**2//4 or len(field.labels) != (Q**2+Q)//2+1:
            raise ArithmeticError("incorrect projective orbit census")

        # Removing all incoming trees leaves directed cycles. Store their predecessors.
        order = list(self.leaves)
        for t in order:
            c = self.parent[t]
            degree[c] -= 1
            if degree[c] == 0:
                order.append(c)
        self.predecessor = {}
        self.cycles = []
        for t in field.labels:
            if degree[t] == 0:
                continue
            cycle = []
            c = t
            multiplier = 1
            while degree[c]:
                degree[c] = 0
                p = self.parent[c]
                self.predecessor[p] = c
                multiplier = (multiplier * Q * (1 + (self.left[p] == self.right[p]))) % GROUP_ORDER
                cycle.append(c)
                c = p
            if c != t or gcd(1-multiplier, GROUP_ORDER) != 1:
                raise ArithmeticError("a cycle failed its unit determinant test")
            self.cycles.append(cycle)
        self.pole = self.leaf_form(INFINITY)
        self.scale = pow(1-sum(self.pole.values()), -1, GROUP_ORDER)

    def leaf_form(self, c):
        """Coefficients of V_c on shifted leaves, including the geometric series on its cycle."""
        pending = []
        if c in self.predecessor:
            node, weight = c, 1
            while True:
                pred = self.predecessor[node]
                left, right = self.left[node], self.right[node]
                if left != right:
                    pending.append((right if left == pred else left, weight*Q % GROUP_ORDER))
                weight = weight*Q*(1+(left == right)) % GROUP_ORDER
                node = pred
                if node == c:
                    break
            inverse = pow(1-weight, -1, GROUP_ORDER)
            pending = [(t, w*inverse % GROUP_ORDER) for t, w in pending]
        else:
            pending.append((c, 1))
        result = {}
        while pending:
            t, w = pending.pop()
            a, b = self.left[t], self.right[t]
            if a < 0:
                result[t] = w
            elif a == b:
                pending.append((a, 2*Q*w % GROUP_ORDER))
            else:
                w = Q*w % GROUP_ORDER
                pending.extend(((a, w), (b, w)))
        return result

    def reduce(self, mask):
        c = self.field.key[mask]
        coeffs = self.leaf_form(c)
        correction = (sum(coeffs.values())-1) * self.scale % GROUP_ORDER
        if correction:
            for t, w in self.pole.items():
                coeffs[t] = (coeffs.get(t, 0)+correction*w) % GROUP_ORDER
        return {t: w for t, w in coeffs.items() if w}

    def single_leaf(self, t):
        """Evaluate all nonzero V coordinates when one shifted leaf is one."""
        if self.left[t] >= 0:
            raise ValueError("the specified coordinate is not a leaf")
        values, weight = {}, 1
        while t not in self.predecessor:
            values[t] = weight
            t = self.parent[t]
            weight = weight*Q*(1+(self.left[t] == self.right[t])) % GROUP_ORDER
        cycle, multiplier = {}, 1
        while t not in cycle:
            cycle[t] = weight
            t = self.parent[t]
            step = Q*(1+(self.left[t] == self.right[t]))
            weight, multiplier = weight*step % GROUP_ORDER, multiplier*step % GROUP_ORDER
        inverse = pow(1-multiplier, -1, GROUP_ORDER)
        values.update((c, w*inverse % GROUP_ORDER) for c, w in cycle.items())
        return values


def check_circle_rank(graph, u, v):
    """Test the zero-center circle rows on explicit solutions of the pullback equations."""
    field = graph.field
    real = {a: i for i, a in enumerate(field.real)}
    # A difference at two sibling leaves vanishes at every other vertex.
    parent = list(range(Q))
    def component(i):
        while i != parent[i]:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i
    for t in graph.leaves:
        mate = field.key[t ^ 1]
        if t >= mate or graph.left[mate] >= 0:
            continue
        d, e = (real[field.multiply(c, field.conjugate[c])] for c in (t, mate))
        if v not in (d, e):
            parent[component(d)] = component(e)
    large = {component(i) for i in range(1, Q) if i not in (1, v)}
    if len(large) != 1 or component(1) in large or component(v) in large or component(1) == component(v):
        raise ArithmeticError("the differences of sibling leaves have unexpected radius components")

    columns = []
    for leaf in TEST_LEAVES[u, v]:
        values = graph.single_leaf(leaf)
        common = -(Q+1)*values.get(INFINITY, 0)
        rows = [0]*Q
        for c, w in values.items():
            if c == INFINITY:
                continue
            bar = field.conjugate[c]
            mult = 1 + (c != bar)
            rows[real[field.multiply(c, bar)]] += mult*w
            h = field.multiply(c, c) ^ c ^ field.real[v]
            if not h:
                common += Q*mult*w
            elif c:
                d = real.get(field.divide(field.multiply(c, field.real[u]), h))
                if d is not None:
                    rows[d] -= Q*mult*(1+(d == u))*w
        columns.append(((rows[1]+common) % GROUP_ORDER, (rows[v]+common) % GROUP_ORDER,
                        (sum(rows[1:])-rows[1]-rows[v]+(Q-3)*common) % GROUP_ORDER))
    a, b, c = columns
    det = sum(a[i]*(b[(i+1)%3]*c[(i+2)%3]-b[(i+2)%3]*c[(i+1)%3]) for i in range(3))
    if gcd(det, GROUP_ORDER) != 1:
        raise ArithmeticError("the three remaining radius coordinates have a nonunit determinant")


def check_field(model, constants, mask, coefficients):
    """Multiply the exported linear norms in the certified quotient and take their full binary-field norms."""
    field = fq_default_ctx(modulus=fmpz_mod_poly_ctx(2)([1, 0, 0, 1] + [0]*6 + [1]), var="z")
    ring = fq_default_poly_ctx(field)
    x = ring.gen()
    packed = int(model["relative_modulus_packed_hex"], 16)
    elements = [scalar(i, field) for i in range(Q)]
    g = ring([elements[(packed >> (10*i)) & (Q-1)] for i in range(DEGREE+1)])
    real = dict(zip(constants.real, elements))

    def relative_norm(c):
        bar = constants.conjugate[c]
        return x*x + real[c ^ bar]*x + real[constants.multiply(c, bar)]

    numerator, denominator = ring.one(), relative_norm(mask)
    for t, w in coefficients.items():
        if w <= GROUP_ORDER//2:
            numerator = numerator * relative_norm(t).pow_mod(w, g) % g
        else:
            denominator = denominator * relative_norm(t).pow_mod(GROUP_ORDER-w, g) % g
    residual = numerator * denominator.inverse_mod(g) % g
    norm_exponent = ((1 << (10*DEGREE))-1) // ((1 << DEGREE)-1)
    if residual.pow_mod(norm_exponent, g) != 1:
        raise ArithmeticError("the exported reduction failed direct full-group powering")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--model", type=int, nargs=2, metavar=("U", "V"))
    group = parser.add_mutually_exclusive_group()
    group.add_argument("--leaves", action="store_true", help="print the reduced factor base, one mask per line")
    group.add_argument("--reduce", type=lambda z: int(z, 0), metavar="MASK", help="print a linear norm as a sum of leaf logarithms")
    parser.add_argument("--field-check", action="store_true", help="also multiply the exported factors in the certified field")
    parser.add_argument("--circle-rank", action="store_true", help="certify the additional rank of all zero-center circles")
    args = parser.parse_args()
    if args.reduce is not None and not 0 <= args.reduce < INFINITY:
        parser.error("a linear norm requires a twenty-bit constant")
    if args.field_check and args.reduce is None:
        parser.error("--field-check requires --reduce MASK")
    selected = args.model or ([3, 1019] if args.reduce is not None or args.leaves else None)
    with gzip.open(CERTIFICATE, "rt") as stream:
        record = json.load(stream)
    models = [r for r in record["models"] if selected is None or [r["u"], r["v"]] == selected]
    if not models:
        parser.error("unrecognized model")
    field = Constants(record["constant_generator_in_quadratic_extension"])
    for row in models:
        graph = Pullback(field, row["u"], row["v"])
        if args.circle_rank:
            check_circle_rank(graph, row["u"], row["v"])
        if args.reduce is not None:
            coeffs = graph.reduce(args.reduce)
            if args.field_check:
                check_field(row, field, args.reduce, coeffs)
            print(json.dumps({"model": [row["u"], row["v"]], "mask": hex(args.reduce), "modulus": str(GROUP_ORDER),
                              "leaf_coefficients": [[hex(t), str(w)] for t,w in sorted(coeffs.items())]}, indent=2))
        elif args.leaves:
            for t in graph.leaves:
                print(hex(t))
        else:
            cycles = sorted(len(cycle) for cycle in graph.cycles)
            print(f"u={row['u']}, v={row['v']}: {len(graph.leaves):,} free leaf logarithms, "
                  f"{len(field.labels)-1-len(graph.leaves):,} independent pullbacks. "
                  f"Cycle lengths {cycles}, pole support {len(graph.pole):,}.")
            if args.circle_rank:
                print("All 1,023 zero-center circle rows add independent constraints modulo the full group order.")


if __name__ == "__main__":
    main()
