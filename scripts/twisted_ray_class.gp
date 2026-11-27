\\ Frobenius at the unique prime above two, identified on an integral basis.
twisted_frobenius_two(b) = {
  my(d = poldegree(b.pol), dec = idealprimedec(b, 2));
  if(#dec != 1 || dec[1].e != 1 || dec[1].f != d, error("two is not inert"));
  my(pr = nfmodprinit(b, dec[1]), auts = nfgaloisconj(b), matches = List());
  for(i = 1, #auts,
    my(ok = 1);
    for(j = 1, d,
      my(v = b.zk[j]);
      if(nfmodpr(b, nfgaloisapply(b, auts[i], v), pr) != nfmodpr(b, v, pr)^2,
        ok = 0; break));
    if(ok, listput(matches, auts[i])));
  if(#matches != 1, error("Frobenius is not unique"));
  matches[1]
};

\\ Return the class number, ordinary two-ray class number, and order of
\\ the quotient of the ray class group by the image of Frobenius minus two.
twisted_ray_quotient(p, d) = {
  if(!isprime(p) || p%8 != 5 || znorder(Mod(2,p)) != p-1 || (p-1)%d || d < 2,
    error("ineligible prime or subfield degree"));
  my(f = if(((p-1)/2)%d == 0, p, 3*p));
  my(field = galoissubcyclo(f, [-1, lift(Mod(2,f)^d)], 2, 'y));
  if(poldegree(field[1]) != d || field[2] != f, error("wrong field or conductor"));
  my(b = bnfinit(field[1], 1));
  if(!bnfcertify(b), error("uncertified class group or units"));
  my(r = bnrinit(b, 2, 1), rank = #r.cyc);
  if(gcd(r.no, 2^d-1) == 1, return([b.no, r.no, 1]));
  my(s = bnrgaloismatrix(r, twisted_frobenius_two(b)));
  my(rel = concat(matdiagonal(r.cyc), s - 2*matid(rank)));
  my(h = mathnf(rel), quotient = abs(matdet(h)));
  if(r.no%quotient || denominator(matinverseimage(h, (2^d-1)*matid(rank))) != 1,
    error("invalid ray quotient presentation"));
  [b.no, r.no, quotient]
};
