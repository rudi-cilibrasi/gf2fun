\\ Use proven prime factors when computing number-field discriminants.
default(factor_proven, 1);

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

\\ Construct E_d. In degrees two through four, the formulas avoid enumerating
\\ residues modulo p. Certify the candidate by Galois symmetry, inertness,
\\ signature, and field discriminant, even when its power basis has an index.
twisted_ray_field(p, d) = {
  if(p < 5 || !isprime(p) || znorder(Mod(-2,p)) != p-1 || d < 2 || (p-1)%d,
    error("ineligible prime or subfield degree"));
  my(f = if(((p-1)/2)%d == 0, p, 3*p));
  if(d > 4,
    my(field = galoissubcyclo(f, [-1, lift(Mod(2,f)^d)], 2, 'y));
    if(poldegree(field[1]) != d || field[2] != f, error("wrong field or conductor"));
    return(field[1]));
  my(y = 'y, pol, disc);
  if(d == 2,
    pol = y^2-y+(1-f)/4; disc = f,
    d == 3,
    my(v = qfbsolve(Qfb(1,1,7),p), L = 2*v[1]+v[2]);
    if(L%3 != 1, L = -L);
    if(4*p != L^2+27*v[2]^2, error("invalid cubic parameters"));
    pol = y^3+y^2-((p-1)/3)*y-((L+3)*p-1)/27; disc = p^2,
    my(v = qfbcornacchia(1,p), a = if(v[1]%2, v[1], v[2]));
    if(v[1]^2+v[2]^2 != p || a%2 != 1, error("invalid quartic parameters"));
    pol = y^4-6*p*y^2+9*p*a^2; disc = 9*p^3);
  if(denominator(pol) != 1 || !polisirreducible(pol), error("invalid defining polynomial"));
  my(nf = nfinit(pol), dec = idealprimedec(nf,2));
  if(nf.disc != disc || nf.sign != [d,0] || #nfgaloisconj(nf) != d,
    error("wrong discriminant, signature or automorphism count"));
  if(#dec != 1 || dec[1].f != d, error("two is not inert"));
  pol
};

\\ Return the class number, ordinary two-ray class number, and order of
\\ the quotient of the ray class group by the image of Frobenius minus two.
twisted_ray_quotient(p, d) = {
  my(b = bnfinit(twisted_ray_field(p, d), 1));
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

\\ Test the p-index character using the prime above 2 in two imaginary
\\ quadratic orders. H only has to principalize the prime in the maximal
\\ order and be prime to p. Both properties are checked exactly.
twisted_conductor_class(p, H = 0) = {
  if(p < 5 || !isprime(p) || znorder(Mod(-2,p)) != p-1, error("ineligible prime"));
  my(delta = if(p%8 == 5, -3*p, -p), disc = delta*p^2);
  if(H == 0, H = quadclassunit(delta).no);
  if(H < 1 || H%p == 0, error("invalid principalization exponent"));
  my(prime = Qfb(2,1,(1-delta)/8), principal = Qfb(1,1,(1-delta)/4));
  if(qfbred(prime^H) != qfbred(principal), error("the prime above two was not principalized"));
  my(lifted = qfbred(Qfb(2,1,(1-disc)/8)^H), identity = qfbred(Qfb(1,1,(1-disc)/4)));
  if(qfbred(lifted^p) != identity, error("the lifted form is outside the conductor kernel"));
  [H, lifted == identity, Vec(lifted)]
};
