"""Check the forward Frobenius models and good binary lifts using PARI/GP."""

import argparse
import json
import math
import subprocess
from pathlib import Path

from check_1229_quadratic_model import TABLE as PERIOD_TABLE, multiply


TABLE = Path(__file__).resolve().parents[1] / "data" / "degree-1229-forward-descent.json"
TAPS = {"product": (27, 50, 77), "seroussi": (2, 6, 15)}


def pari(gp, body):
    script = """
binpol(n) = Mod(1,2)*Pol(digits(n,2));
value(n,a) = subst(binpol(n),x,a);
check(b) = if(!b,error("certificate check failed"));
""" + body + '\nprint("verified");\nquit\n'
    proc = subprocess.run([gp, "-fq", "-s", "512M"], input=script, text=True,
                          capture_output=True, check=True)
    if proc.stderr or proc.stdout.strip() != "verified":
        raise ArithmeticError(proc.stderr or proc.stdout)


def constant_extension(record):
    q, d, n = (record[key] for key in ("q", "constant_degree", "degree"))
    s = q.bit_length() - 1
    m = 18*s
    if (q != 2**s or q <= 61 or s % 2 == 0 or m % d or
            math.gcd(m//d, n) != 1 or record["c"] == 0):
        raise ArithmeticError("invalid constant field or Frobenius parameters")
    return m


def check_model(record, periods, gp):
    d, n, q = (record[key] for key in ("constant_degree", "degree", "q"))
    b = record["pole"]
    D = d*n
    m = constant_extension(record)
    L = record["lift_degree"]
    h, rem = divmod(L, m)
    if n != 1229 or b not in (1, 2) or rem or h < 2 or h & (h-1) or L <= D:
        raise ArithmeticError("incorrect lift degree or parent polynomial")
    # Over the small constant field the uniform degree is twice the witness degree.
    relative_degree = L//d
    if (1 << (d*(relative_degree-n))) <= 2*(n+3+2*q+8):
        raise ArithmeticError("insufficient margin in uniform lift estimate")
    modulus = record["constant_modulus"]
    body = f"""
f=binpol({record['binary_modulus_hex']}); check(poldegree(f)=={D} && polisirreducible(f));
cc=binpol({modulus}); check(poldegree(cc)=={d} && polisirreducible(cc));
t=ffgen(f,'w); z=value({record['constant_generator_hex']},t); check(subst(cc,x,z)==0);
aa=value({record['a']},z); bb=value({record['b']},z); c=value({record['c']},z);
check(aa*bb*c!=0 && t^({q}+{b})==aa*t^2+bb*t+c);
p=value({record['period_hex']},t); check(p!=0 && isprime(2459) && znorder(Mod(2,2459))==2458);
u=t*0; v=p; bits=digits(2459,2);
for(i=1,#bits,w=u*v+p;if(bits[i],u=w;v=v^2,v=w;u=u^2));
check(u==0);
independent(vv)=matdet(matrix(4,4,i,j,vv[j]^(2^({d}*(i-1)))))!=0;
good(F)={{
  check(poldegree(F)=={L} && polisirreducible(F));
  my(y=ffgen(F,'ylift), ybar=y^(2^{L//2}), test);
  check(y!=0 && y!=ybar);
  check(independent([y^0,y,y^2,y^{b}*y^{q}]));
  check(independent([y^0,y,y^2,y^{b}*ybar^{q}]));
  test=if({b}==1,y*ybar,1/y+1/ybar); check(test^(2^{d})!=test);
}};
binarynorm(P)={{
  my(g=P, acc=P, co);
  for(i=2,{d},g=Pol(apply(a->a^2,Vec(g)));acc*=g);
  co=Vec(acc); check(sum(i=1,#co,co[i]!=0 && co[i]!=1)==0);
  Mod(1,2)*Pol(apply(a->a!=0,co))
}};
zz=ffgen(cc,'cbase); one=zz^0;
parent=one*x^{q+b}+value({record['a']},zz)*x^2+value({record['b']},zz)*x+value({record['c']},zz);
basepol=gcd(f*one,parent); basepol/=pollead(basepol); check(poldegree(basepol)=={n});
"""
    for family, taps in TAPS.items():
        root = record["sparse_root_hex"][family]
        low = record["lift_low_multipliers"][family]
        relative_low = record["relative_lift_low_multipliers"][family]
        i, j, k = taps
        body += f"""
rep=binpol({root}); r=subst(rep,x,t); check(r==value({periods[family]},p));
check(r^{n}+r^{k}+r^{j}+r^{i}+1==0 && r^(2^{n})==r);
candidate=rep+f*(x^{L-D}+binpol({low}));
check(candidate%f==rep); good(candidate);
relative=(rep*one)%basepol;
g=relative+basepol*(x^{relative_degree-n}+binpol({relative_low})*one);
check(poldegree(g)=={relative_degree} && g%basepol==relative); good(binarynorm(g));
"""
    pari(gp, body)
    print(f"At degree {n} with q={q}, each sparse root has two verified lifts. "
          f"The binary lift has {d} orbits of good degree-{h} factors "
          f"and the relative lift has one orbit of size {m//d}.", flush=True)


def coefficient_norm(record):
    d = record["constant_degree"]
    size, modulus = 1 << d, record["constant_modulus"]
    poly = {0: record["c"], 1: record["b"], 2: record["a"], record["q"]+record["pole"]: 1}
    norm = {0: 1}
    for _ in range(d):
        product = {}
        for i, a in poly.items():
            for j, b in norm.items():
                product[i+j] = product.get(i+j, 0) ^ multiply(a, b, size, modulus)
        norm = {i: a for i, a in product.items() if a}
        poly = {i: multiply(a, a, size, modulus) for i, a in poly.items()}
    if set(norm.values()) != {1}:
        raise ArithmeticError("coefficient norm did not descend to the binary field")
    return sorted(norm)


def check_gap(record, gp):
    n = record["degree"]
    d = record["constant_degree"]
    constant_extension(record)
    pari(gp, f"""
cc=binpol({record['constant_modulus']}); check(poldegree(cc)=={d} && polisirreducible(cc));
ex={coefficient_norm(record)}; parent=Mod(1,2)*sum(i=1,#ex,x^ex[i]);
degs=factormod(parent,2,1)[,1]; check(sum(i=1,#degs,degs[i]=={n*d})>=1);
""")
    print(f"The degree-{n} coefficient norm has an absolute degree-{n*d} factor.",
          flush=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gp", default="gp", help="path to PARI/GP")
    args = parser.parse_args()
    data = json.loads(TABLE.read_text())
    periods = json.loads(PERIOD_TABLE.read_text())["sparse_in_period_hex"]
    for model in data["degree_1229"]:
        check_model(model, periods, args.gp)
    common = data["first_gaps"]
    for model in common["models"]:
        check_gap({**common, **model}, args.gp)


if __name__ == "__main__":
    main()
