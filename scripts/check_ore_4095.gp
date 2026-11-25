\\ Independent PARI/GP verification of all degree-4095 lifts from sparse degree-12 seeds.
\\ Run from the repository root with gp -q -f scripts/check_ore_4095.gp.

default(parisizemax, 1000000000);
ps = read("data/mersenne-4095-factors.json");
ds = Set(ps);
M = 2^4095-1;
fa = matrix(#ds, 2, i, j, if(j == 1, ds[i], sum(k = 1, #ps, ps[k] == ds[i])));
cert = read("data/ore-4095-primecert.json");

checkfactorization() = {
  if(factorback(fa) != M, error("incorrect factorization product"));
  if(cert[1][1] != vecmax(ds) || !primecertisvalid(cert), error("invalid ECPP certificate"));
  for(i = 1, #ds-1, if(!isprime(ds[i]), error("composite factor")));
};

checkseed(e) = {
  my(p = Mod(1,2) * sum(i=1,#e, x^e[i]));
  if(!polisirreducible(p), return());
  my(a = ffgen(p,'t));
  if(fforder(a,4095) != 4095, return());
  my(f = Mod(1,2) * sum(i=1,#e, x^(2^e[i]-1)));
  if(!polisirreducible(f), error("reducible lift"));
  my(z = ffgen(f,'t));
  if(subst(f,x,z) != 0, error("wrong quotient generator"));
  my(index = M / fforder(z,[M,fa]));
  print(e, " ", index);
  mapput(counts,index,mapget(counts,index)+1);
};

\\ Initialize the expected indices so a new index raises an error.
run() = {
  checkfactorization();
  counts = Map([1,0; 7,0]);
  for(a=1,11,checkseed([0,a,12]));
  for(a=1,9, for(b=a+1,10, for(c=b+1,11,checkseed([0,a,b,c,12]))));
  if(mapget(counts,1) != 12 || mapget(counts,7) != 6, error("unexpected census"));
  print("verified 12 primitive lifts and 6 of exact index seven");
};

iferr(run(), E, print(E); quit(1));
quit(0);
