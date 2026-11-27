"""Certify the full orders of a quaternary projective orbit inside the binary degree-2458 field."""

import argparse
import csv
import gzip
import json
import subprocess
from collections import Counter
from itertools import permutations
from math import gcd, prod
from pathlib import Path

from check_degree_1229 import COFACTOR, KNOWN, PRIMES


DATA = Path(__file__).resolve().parents[1] / "data"


def constant_logs(labels):
    # The constant model uses the residue of T modulo T^18+T^12+T^10+T+1.
    omega = 1
    for _ in range(((1 << 18)-1)//3):
        omega <<= 1
        if omega >> 18:
            omega ^= 0x41403
    if labels != [0, 1, omega, omega ^ 1]:
        raise ValueError("incorrect constant subfield labels")
    with gzip.open(DATA / "degree-1229-q512-quaternary-logs.csv.gz", "rt", newline="") as stream:
        logs = {int(row["mask"], 0): int(row["exponent"]) for row in csv.DictReader(stream)
                if int(row["mask"], 0) in labels}
    return [logs[t] for t in labels] + [0]  # The point at infinity represents the constant one.


def check(gp):
    row = json.loads((DATA / "degree-2458-projective-orders.json").read_text())
    model = next(m for m in json.loads((DATA / "degree-1229-quaternary-models.json").read_text())
                 if m["id"] == 21149)
    rank = json.loads((DATA / "degree-1229-q1024-quaternary-rank.json").read_text())
    logs = constant_logs(row["log_labels_by_F4_constant"])
    relative = row["relative_primes"]
    plus = 2**1229 + 1
    primes = [*PRIMES, *relative]
    if (prod(relative) != plus or len(set(primes)) != len(primes)
            or prod(primes)*COFACTOR != (1 << 2458)-1 or gcd(prod(primes), COFACTOR) != 1):
        raise ValueError("incorrect coprime decomposition of the group order")

    # Relative norms at the four constants have projected logarithms in the
    # published table. A direct field check here also fixes the choice of omega.
    sparse = sum(1 << i for i in (0, 910, 971, 1229, 2458))
    program = f"""
check() = {{
  my(f=Mod(1,2)*Pol(binary({int(model["binary_modulus_hex"], 16)})),r,w,z,u,
     M=2^2458-1,Q=2^1229+1,K={KNOWN},C={COFACTOR},P={primes},E={logs},T,L,W);
  if(!polisirreducible(f) || !vecmin(apply(isprime,P)),error("field or prime test"));
  r=ffgen(f,'a);
  w=subst(Pol(binary({int(model["constant_generator_hex"], 16)})),x,r);
  if(w^2+w+1!=0,error("constant generator"));
  if(fromdigits(Vec(liftall(minpoly(r^Q))),2)!={int(rank["norm_minimal_polynomial_hex"], 16)},
     error("primitive norm polynomial"));
  T=[r,r+1,r+w,r+w+1,r^0]; L=[r^0,w,w+1]; u=(r^Q)^K;
  for(i=1,5,if(T[i]^(Q*K)!=u^E[i],error("projected norm log")));
  for(i=1,5,for(j=1,5,if(i!=j,for(t=1,3,
    z=L[t]*T[i]/T[j]; W=fromdigits(Vec(liftall(minpoly(z))),2);
    if(logint(W,2)!=2458,error("projective degree"));
    print([i,j,t,prod(h=1,#P,if(z^(M/P[h])==1,P[h],1)),hammingweight(W)])))));
  f=Mod(1,2)*Pol(binary({sparse}));
  if(!polisirreducible(f),error("reducible sparse polynomial"));
  r=ffgen(f,'b); W=fromdigits(Vec(liftall(minpoly(r^Q))),2);
  if(logint(W,2)!=1229 || hammingweight(W)!=631 ||
     !vecmin(apply(h->r^(M/h)!=1,P)) || r^(M/C)==1,error("sparse norm or order test"));
  print("verified");
}};
iferr(check(),err,print(err);quit(1));
"""
    result = subprocess.run([gp, "-fq", "-s", "256M"], input=program, text=True, capture_output=True)
    lines = result.stdout.splitlines()
    if result.returncode or result.stderr or len(lines) != 61 or lines[-1] != "verified":
        raise ArithmeticError(f"field verification failed: {result.stderr}{lines[-1:]}")
    counts, minimum, weights = Counter(), {}, {}
    expected = ((i,j,t) for i,j in permutations(range(1,6),2) for t in range(1,4))
    for line, indices in zip(lines[:-1], expected, strict=True):
        i,j,t,known_index,weight = json.loads(line)
        if (i,j,t) != indices:
            raise ValueError("projective elements are out of order")
        index = gcd(logs[i-1]-logs[j-1],COFACTOR) * known_index
        if j == 5 and t == 1 and i in (1,2) and index != 1:
            raise ValueError("the coordinate or its binary translate is not primitive")
        counts[index] += 1
        if index == 1:
            weights[indices] = weight
        minimum[index] = min(minimum.get(index,2459),weight)
    if ({str(i):c for i,c in counts.items()} != row["indices"]
            or {str(i):w for i,w in minimum.items()} != row["min_weight_by_index"]):
        raise ValueError("projective order or minimum-weight census disagreement")
    if {point for point,w in weights.items() if w == minimum[1]} != {(1,4,2),(4,1,3)}:
        raise ValueError("unexpected lightest primitive images")
    print(f"Degree 2458: exact indices {dict(sorted(counts.items()))}, "
          f"minimum primitive weight in the orbit {minimum[1]}.")
    print("The sparse root passes every known prime test and its full-order index divides the degree-1229 cofactor.")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp")
    check(parser.parse_args().gp)
