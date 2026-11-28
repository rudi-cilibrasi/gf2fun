\\ The Python checker supplies canonical binary masks and the point coordinates.
binpol(mask) = Mod(1,2)*Pol(digits(mask,2));
value(mask,a) = subst(binpol(mask),x,a);
pack(a) = fromdigits(liftall(Vec(a.pol)),2);
check(b) = if(!b,error("elliptic ray certificate failed"));

check(poldegree(binpol(cmask))==d && polisirreducible(binpol(cmask)));
check(poldegree(binpol(emask))==n && polisirreducible(binpol(emask)) && gcd(n,d)==1);
z=ffgen(binpol(cmask),'zc); a=ffgen(binpol(emask),'ap); unit=a^0;
modulus=unit*binpol(cmask); Z=Mod(unit*x,modulus); one=Z^0;
embed(c) = Mod(unit*binpol(pack(c*z^0)),modulus);
curve=ellinit([1,value(curvea,z),0,0,value(curveb,z)],z);
G=apply(i->value(i,z),generator); T=apply(i->value(i,z),translation);
Xb=Mod(Polrev(apply(i->value(i,a),xs)),modulus);
Yb=Mod(Polrev(apply(i->value(i,a),ys)),modulus);

check(ellcard(curve)==card && ellisoncurve(curve,G) && ellorder(curve,G,card)==card);
check(ellisoncurve(curve,T) && ellorder(curve,T,card)==n && rows<=card/n);
check(Yb^2+Xb*Yb==Xb^3+embed(value(curvea,z))*Xb^2+embed(value(curveb,z)));
slope=(Yb+embed(T[2]))/(Xb+embed(T[1]));
nextx=slope^2+slope+Xb+embed(T[1])+embed(value(curvea,z));
check(nextx==Xb^(2^d) && slope*(Xb+nextx)+nextx+Yb==Yb^(2^d));

\\ Each step returns the sum and the line numerator and denominator evaluated at B.
miller_step(r,s) = {
  if(#r==1,return([s,one,one]));
  if(#s==1,return([r,one,one]));
  my(rx=r[1],ry=r[2],sx=s[1],sy=s[2]);
  if(rx==sx && ry+sy==rx,return([[0],Xb+embed(rx),one]));
  my(m=if(rx==sx,rx+ry/rx,(ry+sy)/(rx+sx)), h=elladd(curve,r,s));
  [h,Yb+embed(m)*Xb+embed(ry+m*rx),Xb+embed(h[1])]
};
target(p) = {
  my(r=p,top=one,bottom=one,bits=digits(card,2),step);
  for(i=2,#bits,
    step=miller_step(r,r); r=step[1]; top=top^2*step[2]; bottom=bottom^2*step[3];
    if(bits[i],step=miller_step(r,p); r=step[1]; top*=step[2]; bottom*=step[3]));
  check(r==[0] && top!=0 && bottom!=0);
  norm(top)/norm(bottom)
};
uT=target(T); print(0,",",pack(uT*unit));
P=G;
for(i=1,rows-1,u=target(P);print(i,",",pack(u*unit));P=elladd(curve,P,G));
\\ Independently check the direction of the Frobenius recurrence on one translated point.
check(target(G)==(target(elladd(curve,G,T))/uT)^(2^d));
quit
