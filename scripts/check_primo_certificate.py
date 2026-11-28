"""Verify a mixed PRIMO format-3 or format-4 certificate for a specified integer with PARI/GP."""

import configparser
import gzip
import json
import subprocess
from math import gcd

from flint import fmpz


# PARI's ECPP step verifier returns the child prime that suffices to prove the parent.
# For Lucas steps, the lower left matrix entry at exponent k is the Lucas number U_k.
GP_CHECK = """
install("primecertisvalid_ecpp_worker", "G", "ecstep");
checkstep(v) = {
  my(n=v[1], q=v[2], s, b, a);
  if (#v==3, return(ecstep(v[3])==q));
  s=v[3];
  if (#v==4, b=Mod(v[4],n); return(b^(n-1)==1 && gcd(lift(b^s)-1,n)==1));
  a=Mod(1,n)*[v[4],-v[5];1,0];
  (a^(n+1))[2,1]==0 && gcd(lift((a^s)[2,1]),n)==1
};
default(nbthreads,min(8,default(nbthreads)));
"""


def primo_integer(value):
    return int(value.replace("$", "0x"), 0)


def check_primo(path, candidate, gp):
    certificate = configparser.ConfigParser(interpolation=None, allow_no_value=True)
    with gzip.open(path, "rt", encoding="ascii") as stream:
        certificate.read_file(stream)
    header = certificate["PRIMO - Primality Certificate"]
    version = header.getint("Format")
    if version == 3:
        n = int(certificate["Candidate"]["N$"], 16)
    elif version == 4:
        n = primo_integer(certificate["Candidate"]["N"])
    else:
        raise ValueError("unsupported PRIMO format")
    if n != candidate:
        raise ValueError("PRIMO certificate does not match the requested prime")
    steps = []
    count = header.getint("TestCount")
    for i in range(1, count + 1):
        record = certificate[str(i)]
        if version == 3:
            kind = record.getint("Type")
            fields = {1: {"s", "r", "b"}, 2: {"s", "r", "q"},
                      3: {"s", "r", "a", "b", "t"}, 4: {"s", "r", "j", "t"}}
            if i == count:
                if kind != 0 or set(record) != {"type"}:
                    raise ValueError("missing terminal PRIMO step")
                break
            if kind not in fields or set(record) != {"type"} | {k+"$" for k in fields[kind]}:
                raise ValueError(f"invalid format-3 record at PRIMO step {i}")
            data = {k: int(record[k+"$"], 16) for k in fields[kind]}
            if kind in (3, 4):
                data["w"] = n + 1 - data["s"] * data["r"]
        else:
            data = {k: primo_integer(v) for k, v in record.items()}
        s = data["s"]
        if n <= 3 or n % 2 == 0 or s <= 0:
            raise ValueError(f"invalid parent or cofactor at PRIMO step {i}")
        if "w" in data:
            w, t = data["w"], data["t"]
            q, remainder = divmod(n+1-w, s)
            if "j" in data:
                j = data["j"]
                a, b = 3*j*(1728-j) % n, 2*j*(1728-j)**2 % n
            else:
                a, b = data["a"], data["b"]
            # Twist the curve by L so that the abscissa T yields an explicit point.
            ell = (pow(t, 3, n) + a*t + b) % n
            if gcd(ell * (4*pow(a, 3, n) + 27*pow(b, 2, n)), n) != 1:
                raise ValueError(f"singular curve at PRIMO step {i}")
            point = [t*ell % n, ell*ell % n]
            steps.append([n, q, [n, w, s, a*ell*ell % n, point]])
        else:
            sign = 1 if "q" in data else -1
            q, remainder = divmod(n+sign, s)
            if (q-sign)**2 <= n:
                raise ValueError(f"child too small at PRIMO step {i}")
            if sign == -1:
                steps.append([n, q, s, data["b"]])
            else:
                lucas_q = data["q"]
                lucas_p = 2 if lucas_q % 2 else 1
                if gcd(2*lucas_q*(lucas_p**2-4*lucas_q), n) != 1:
                    raise ValueError(f"singular Lucas sequence at PRIMO step {i}")
                steps.append([n, q, s, lucas_p, lucas_q])
        if remainder or not 1 < q < n or ("r" in data and data["r"] != q):
            raise ValueError(f"broken prime chain at PRIMO step {i}")
        n = q
    if not steps or n >= 2**64 or not fmpz(n).is_prime():
        raise ValueError("invalid terminal prime in PRIMO certificate")
    # The 16,008-digit certificate exceeds GP's parser stack as a single vector.
    # The chain links and terminal prime above bind the independent step checks.
    for first in range(0, len(steps), 64):
        batch = steps[first:first+64]
        encoded = json.dumps(batch, separators=(",", ":"))
        program = GP_CHECK + f"print(vecmin(parapply(checkstep,{encoded})));\n"
        result = subprocess.run([gp, "-qf", "-s", "96M"], input=program,
                                text=True, capture_output=True, check=True)
        if result.stdout.splitlines() != ["1"] or result.stderr.strip():
            raise ValueError(f"PARI rejected PRIMO steps {first+1} to {first+len(batch)}. "
                             f"{result.stderr[:300]}")
