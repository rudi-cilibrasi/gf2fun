"""Verify a quadratic Frobenius model and both embedded sparse roots using PARI/GP."""

import argparse
import json
import subprocess
from pathlib import Path


TABLE = Path(__file__).resolve().parents[1] / "data" / "degree-1229-quadratic-frobenius.json"


def multiply(a, b, q, modulus):
    product = 0
    while b:
        if b & 1:
            product ^= a
        a <<= 1
        if a & q:
            a ^= modulus
        b >>= 1
    return product


def norm_exponents(record):
    q = record["q"]
    u, v = record["u"], record["v"]
    modulus = int(record["constant_modulus_hex"], 16)
    poly = {0: u, q: v, q+1: u, 2*q: 1}
    norm = {0: 1}
    for _ in range(q.bit_length()-1):
        result = {}
        for i, c in poly.items():
            for j, d in norm.items():
                result[i+j] = result.get(i+j, 0) ^ multiply(c, d, q, modulus)
        norm = {j: d for j, d in result.items() if d}
        poly = {i: multiply(c, c, q, modulus) for i, c in poly.items()}
    if any(c != 1 for c in norm.values()):
        raise ArithmeticError("nonbinary coefficient norm")
    return sorted(norm)


def verify(record, gp):
    q = record["q"]
    exponents = norm_exponents(record)
    if q != 1024 or exponents != record["norm_exponents"]:
        raise ArithmeticError("incorrect parent norm")
    sparse = record["sparse_root_hex"]
    expressions = record["sparse_in_period_hex"]
    # All decimal GP inputs below are integers parsed from the certificate.
    degrees = record["norm_factor_degrees"]
    if degrees != [[70, 1], [100, 1], [290, 1], [2800, 1], [4930, 1], [12290, 1]]:
        raise ArithmeticError("incorrect absolute degree pattern")
    script = f"""
binarypol(n) = Mod(1,2)*Pol(digits(n,2));
value(n,a) = subst(binarypol(n),x,a);
check(b) = if(!b,error("certificate check failed"));
f=binarypol({int(record['binary_modulus_hex'],16)}); check(poldegree(f)==12290 && polisirreducible(f));
ex={exponents}; parent=Mod(1,2)*sum(i=1,#ex,x^ex[i]); check(parent%f==0);
fa=factormod(parent,2,1); check(vector(matsize(fa)[1],i,[fa[i,1],fa[i,2]])=={degrees});
t=ffgen(f,'w); check(subst(f,x,t)==0); y=t^{q}; z=value({int(record['constant_generator_hex'],16)},t);
check(value({int(record['constant_modulus_hex'],16)},z)==0 && z^{q}==z);
u=value({record['u']},z); v=value({record['v']},z);
check(u*y*t==y^2+v*y+u && u*y!=0);
r=value({int(sparse['product'],16)},t); s=value({int(sparse['seroussi'],16)},t);
check(r^1229+r^77+r^50+r^27+1==0 && s^1229+s^15+s^6+s^2+1==0);
check(r^(2^1229)==r && s^(2^1229)==s && r!=1 && s!=1 && r!=0 && s!=0);
period=value({int(record['period_hex'],16)},t); check(period!=0 && znorder(Mod(2,2459))==2458);
a=t^0+t^0; b=period; bits=digits(2459,2);
for(i=1,#bits,odd=a*b+period;if(bits[i],a=odd;b=b^2,b=odd;a=a^2));
check(a==0 && value({int(expressions['product'],16)},period)==r && value({int(expressions['seroussi'],16)},period)==s);
check(gcd(10,2^1229-1)==1);
print("quadratic-model-verified");
quit
"""
    result = subprocess.run([gp, "-fq", "-s", "256M"], input=script, text=True,
                            capture_output=True, check=True)
    if result.stderr or result.stdout.strip() != "quadratic-model-verified":
        raise ArithmeticError(result.stderr or result.stdout)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="path to PARI/GP")
    args = parser.parse_args()
    verify(json.loads(TABLE.read_text()), args.gp)
    print("Verified the degree-12290 binary modulus, the quadratic Frobenius equation over F_1024,"
          " and both sparse roots in its degree-1229 binary subfield.")
