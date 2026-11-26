"""Check Frobenius models, good lifts, and explicit norm identities using PARI/GP."""

import argparse
import csv
import json
import math
import subprocess
from pathlib import Path

from check_1229_quadratic_model import TABLE as PERIOD_TABLE, multiply


TABLE = Path(__file__).resolve().parents[1] / "data" / "degree-1229-forward-descent.json"
FACTORS = TABLE.with_name("degree-1229-norm-factors.json")
QUOTIENTS = TABLE.with_name("degree-1229-norm-quotients.json")
WHEEL = TABLE.with_name("degree-1229-period-wheel.csv")
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


def check_model(record, periods, factors, quotients, gp, quotients_only=False):
    d, n, q = (record[key] for key in ("constant_degree", "degree", "q"))
    b = record["pole"]
    D = d*n
    m = constant_extension(record)
    L = record["lift_degree"]
    h, rem = divmod(L, m)
    if n != 1229 or b not in (1, 2) or rem or h < 2 or h & (h-1) or L <= D or factors["m"] != m:
        raise ArithmeticError("incorrect lift degree or parent polynomial")
    # Over the small constant field the uniform degree is twice the witness degree.
    relative_degree = L//d
    if (1 << (d*(relative_degree-n))) <= 2*(n+3+2*q+8):
        raise ArithmeticError("insufficient margin in uniform lift estimate")
    targets = factors["period_targets"]
    with WHEEL.open(newline="") as table:
        expected = [int(row["mask"]) for row in csv.DictReader(table)
                    if d == 6 and int(row["degree"]) <= 6]
    if [row["mask"] for row in targets] != expected:
        raise ArithmeticError("incorrect period targets")
    if d == 6 and [row["target"] for row in quotients] != [*TAPS, *expected]:
        raise ArithmeticError("incorrect targets in degree-16 norm quotients")
    modulus = record["constant_modulus"]
    body = f"""
f=binpol({record['binary_modulus_hex']}); check(poldegree(f)=={D} && polisirreducible(f));
cc=binpol({modulus}); check(poldegree(cc)=={d} && polisirreducible(cc));
t=ffgen(f,'w); z=value({record['constant_generator_hex']},t); check(subst(cc,x,z)==0);
aa=value({record['a']},z); bb=value({record['b']},z); c=value({record['c']},z);
check(aa*bb*c!=0 && t^({q}+{b})==aa*t^2+bb*t+c);
p=value({record['period_hex']},t); check(p!=0 && p^(2^{n})==p && isprime(2459) && znorder(Mod(2,2459))==2458);
u=t*0; v=p; bits=digits(2459,2);
for(i=1,#bits,w=u*v+p;if(bits[i],u=w;v=v^2,v=w;u=u^2));
check(u==0);
independent(vv)=matdet(matrix(4,4,i,j,vv[j]^(2^({d}*(i-1)))))!=0;
good(F,degree)={{
  check(poldegree(F)==degree && polisirreducible(F));
  my(y=ffgen(F,'ylift), ybar=y^(2^(degree/2)), test);
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
kp=binpol({factors['modulus']}); check(poldegree(kp)=={m} && polisirreducible(kp));
xi=ffgen(kp,'kgen); zk=value({factors['base_generator']},xi); check(subst(cc,x,zk)==0);
ctab=vector(2^{d},i,value(i-1,zk));
inlarge(a)=ctab[1+fromdigits(liftall(Vec((a*one).pol)),2)];
normcheck(g,coeffs,h)={{
  check(poldegree(g)=={m//d}*h && pollead(g)==1); good(binarynorm(g),{m}*h);
  my(v=Polrev(apply(a->value(a,xi),coeffs)), prod=v);
  check(poldegree(v)==h && pollead(v)==1);
  for(i=2,{m//d},v=Pol(apply(a->a^(2^{d}),Vec(v)));prod*=v);
  check(prod==Pol(apply(inlarge,Vec(g))));
}};
relativecheck(residue,low,coeffs)={{
  my(g=residue+basepol*(x^{relative_degree-n}+binpol(low)*one));
  check(g%basepol==residue); normcheck(g,coeffs,{h});
}};
"""
    for family, taps in TAPS.items():
        root = record["sparse_root_hex"][family]
        low = record["lift_low_multipliers"][family]
        relative_low = record["relative_lift_low_multipliers"][family]
        coefficients = [int(c, 16) for c in factors["sparse"][family]]
        i, j, k = taps
        body += f"""
rep=binpol({root}); r=subst(rep,x,t); check(r==value({periods[family]},p));
check(r^{n}+r^{k}+r^{j}+r^{i}+1==0 && r^(2^{n})==r);
"""
        if quotients_only:
            continue
        body += f"""
candidate=rep+f*(x^{L-D}+binpol({low}));
check(candidate%f==rep); good(candidate,{L});
relativecheck((rep*one)%basepol,{relative_low},{coefficients});
"""
    body += f"periodmod=Mod(binpol({record['period_hex']})*one,basepol);\n"
    for row in ([] if quotients_only else targets):
        coefficients = [int(c, 16) for c in row["coefficients_hex"]]
        body += (f"residue=lift(subst(binpol({row['mask']})*one,x,periodmod));"
                 f"relativecheck(residue,{row['low_multiplier']},{coefficients});\n")
    if quotients:
        body += quotient_checks(record, quotients)
    pari(gp, body)
    if quotients:
        print(f"Verified {len(quotients)} norm quotients of optimal degree 16.", flush=True)
        print(f"Verified {len(quotients)} single linear norms over the degree-7410 constant field.",
              flush=True)
    if quotients_only:
        return
    print(f"At degree {n} with q={q}, each sparse root has two verified lifts. "
          f"The binary lift has {d} orbits of good degree-{h} factors "
          f"and the relative lift has one orbit of size {m//d}.", flush=True)
    if targets:
        print(f"Verified explicit norms of good degree-{h} factors for all {len(targets)} "
              "listed period targets of degree at most six.", flush=True)


def quotient_checks(record, rows):
    """Reconstruct both monic polynomials in the rational approximation to each target."""
    if record["constant_degree"] != 6:
        raise ValueError("the quotient certificates use the degree-six constant field")
    body = """
quotientcheck(residue,shift,seed,top,bottom,linearseed)={
  check(poldegree(residue)==1228);
  my(p0=basepol,p1=residue,b0=0*zz,b1=one,qr,bb);
  while(poldegree(p1)>poldegree(b1),
    qr=divrem(p0,p1); bb=b0+qr[1]*b1; p0=p1; p1=qr[2]; b0=b1; b1=bb);
  my(d0=max(poldegree(p0),poldegree(b0)), d1=max(poldegree(p1),poldegree(b1)));
  check(d0==615 && d1==614);
  my(mat=[polcoef(p0,d0),polcoef(p1,d1);polcoef(b0,d0),polcoef(b1,d1)]);
  check(p0*b1-b0*p1==basepol && matdet(mat)!=0);
  check((p0-residue*b0)%basepol==0 && (p1-residue*b1)%basepol==0);
  my(c=matsolve(mat,[one,one]~), s=Pol(apply(a->value(a,zz),digits(seed,64))));
  check(poldegree(s)<624-d0);
  my(u=c[1]*x^(624-d0)+s, v=c[2]*x^(624-d1)+value(shift,zz));
  my(num=u*p0+v*p1, den=u*b0+v*b1);
  check(den%basepol!=0 && (num-residue*den)%basepol==0);
  normcheck(num,top,16); normcheck(den,bottom,16);
  my(low=Pol(apply(a->value(a,zz),digits(linearseed,64))));
  check(poldegree(low)<6);
  my(g=residue+basepol*(x^6+low), absolute=binarynorm(g));
  check(poldegree(g)==1235 && pollead(g)==1 && poldegree(absolute)==7410 && polisirreducible(absolute));
};
"""
    for item in rows:
        target = item["target"]
        if target in TAPS:
            residue = f"(binpol({record['sparse_root_hex'][target]})*one)%basepol"
        elif isinstance(target, int) and target > 0:
            residue = f"lift(subst(binpol({target})*one,x,periodmod))"
        else:
            raise ValueError(f"unknown quotient target {target}")
        top = [int(mask, 16) for mask in item["numerator_hex"]]
        bottom = [int(mask, 16) for mask in item["denominator_hex"]]
        body += (f"quotientcheck({residue},{int(item['shift'])},{int(item['seed'])},"
                 f"{top},{bottom},{int(item['linear_norm_seed'])});\n")
    return body


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
    parser.add_argument("--quotients-only", action="store_true",
                        help="replay the smaller norm quotients and their degree lower bounds")
    args = parser.parse_args()
    data = json.loads(TABLE.read_text())
    periods = json.loads(PERIOD_TABLE.read_text())["sparse_in_period_hex"]
    factors = {entry["constant_degree"]: entry for entry in json.loads(FACTORS.read_text())}
    quotients = json.loads(QUOTIENTS.read_text())
    for model in data["degree_1229"]:
        d = model["constant_degree"]
        if d == 6 or not args.quotients_only:
            check_model(model, periods, factors[d], quotients if d == 6 else [], args.gp,
                        args.quotients_only)
    if args.quotients_only:
        return
    common = data["first_gaps"]
    for model in common["models"]:
        check_gap({**common, **model}, args.gp)


if __name__ == "__main__":
    main()
