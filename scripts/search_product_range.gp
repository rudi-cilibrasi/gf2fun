\\ Called by check_product_range.py with a complete factor list for 2^n-1.
findproduct(n, ps, {leastspan=0}) = {
  my(M = 2^n-1, ds = Set(ps));
  my(fa = matrix(#ds, 2, i, j, if(j == 1, ds[i], sum(k=1, #ps, ps[k] == ds[i]))));
  if(factorback(fa) != M, error("incorrect group order"));
  for(first = 3, if(leastspan, 3, 4),
    forstep(top = first, n-1, if(leastspan, 1, 2),
      for(u = 1, (top-1) \ 2,
        my(v = top-u, f = Mod(1,2)*(x^n + x^top + x^u + x^v + 1));
        if(polisirreducible(f),
          my(a = ffgen(f,'t));
          if(subst(f,x,a) != 0, error("incorrect field generator"));
          if(fforder(a,[M,fa]) == M, return([u,v]))
        )
      )
    )
  );
  error("exhausted product family in degree ", n);
};
