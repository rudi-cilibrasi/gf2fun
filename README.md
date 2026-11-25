# Primitive binary pentanomials

Does every positive degree $n$ have a primitive polynomial over $\mathbb F_2$ with at most five terms? This is Conjecture 4.3.5 in the *Handbook of Finite Fields*. The all-degree question remains open here. A primitive polynomial is monic and irreducible, and the residue of $X$ has multiplicative order $2^n-1$. [Stephen D. Cohen, “Weights of primitive polynomials”](https://archive.ymsc.tsinghua.edu.cn/pacm_download/672/12637-dingjt-p2.pdf#page=133)

The [research note](results.pdf) gives the proofs, examples, and references. Its [LaTeX source](results.tex) is included.

## Results

- **Primitive witnesses.** Lean proves the statement for every $1\le n\le320$. For every $5\le n\le320$ it verifies the shape $X^n+(X^u+1)(X^v+1)$, where $0<u<v$ and $u+v<n$. One example is $X^{24}+X^4+X^3+X+1$. The same exponent relation appears in the pentanomial entries of Table 4.8 of the *Handbook of Applied Cryptography*. Published minimum-weight tables cover degrees 2 through 640 with unrestricted interior exponents. [Lean degree coverage](GF2Sparse/Coverage.lean) · [Table 4.8 and its construction](https://cacr.uwaterloo.ca/hac/about/chap4.pdf#page=37) · [Minimum-weight tables](https://people.math.carleton.ca/~daniel/hff/)
- **Three tests for every degree with at most three ones in binary.** For every such $n\ge4$, a squarefree binary polynomial with at most five terms has no product of one, two or three roots equal to 1. For odd $n>7$ one of the four trinomials $X^n+X^a+1$ with $a=3,4,5,7$ works. For $n\equiv2\pmod4$ above 11 the choices are $3,7,11$. Two commuting Frobenius powers reduce the infinitely many degrees to 2,628 and 171 unordered residue pairs. [Proof in the note](results.pdf#page=24) · [Reproduce the finite calculation](scripts/check_binary_degree_triples.py)
- **Three tests for signed binary degrees.** Every $n\ge4$ expressible as a sum of at most three signed powers of two has a squarefree polynomial of weight at most five passing the first three root-product tests. At every odd such degree there is a trinomial with coprime exponents. For $n=2^s-2^t-1$ with $1\le t\le s-2$, two integer gcds determine exactly which powers of two work as the inner exponent, and at least one always works. [Proof and choice of exponent](results.pdf#page=27) · [Lean test and 999-one example](GF2Sparse/SignedTriples.lean) · [Reproduce the finite cases](scripts/check_binary_degree_triples.py)
- **Thirty-two consecutive degrees after every sum of two powers of two.** For $s,t\ge1$ and $1\le e\le32$, write $n=2^s+2^t+e$. Except in degree 8, some trinomial $X^n+X^a+1$ with $a\le21$ and $\gcd(n,a)=1$ passes all three root-product tests. Degree 8 has a primitive pentanomial. The finite calculation checks every residue pair for all 32 offsets. [Proof and examples](results.pdf#page=25) · [Calculation](scripts/check_binary_degree_triples.py)
- **A limit on fixed trinomial searches.** For every bound $A$, there are arbitrarily large prime degrees $n$ where *every* $X^n+X^a+1$ with $1\le a\le A$ has three distinct roots with product 1. This holds in any prescribed reduced arithmetic progression. The note extends the obstruction to any finite list of rational affine rules for $a$ and to their cubic-sampled pentanomials. [Lean proof for bounded exponents](GF2Sparse/TripleObstruction.lean) · [Proof for affine rules](results.pdf#page=26)
- **Restrictions on every primitive support in prime degrees.** Fix finitely many rational slopes and a width around each slope times the degree. In every reduced arithmetic progression there are arbitrarily large prime degrees where every polynomial supported in those bands has a proper factor. For example, in prime degree 1307 the bands within two of $0,1307/2,1307$ force a factor of degree at most five. The note also proves a growing-width bound for rational slopes and a fixed-width result for arbitrary real slopes. [Lean proof and degree-1307 example](GF2Sparse/PrimeGrid.lean) · [Proofs in the note](results.pdf#page=26)
- **Arbitrarily many tests on one sequence.** For $s=1+j!$, $n=2^s-1$ and $u=(n-1)/3$, the squarefree pentanomial $X^n+(X^u+1)^3$ has exponent gcd 1. Lean proves that for every fixed $k$, all sufficiently large members have no product-one selection of one through $k$ roots, even with repetitions. These members pass the first $k$ exterior-power tests. The proof bounds the field degrees of roots in any short product relation and then excludes those field degrees by the choice of $s$. [Lean proof for the factorial sequence](GF2Sparse/ShortProducts.lean) · [Explicit degree bound](results.pdf#page=19) · [Lean interpolation bound](GF2Sparse/FibreBound.lean)
- **Arbitrarily many tests in power-of-two degrees.** For every fixed $k$, infinitely many powers of two have squarefree, exponent-gcd-one pentanomials passing all $k$ tests. For any fixed $u<v$, a bound on the degrees of roots in a short product relation makes those relations periodic in $s$ for $X^{2^s}+(X^u+1)(X^v+1)$. Choosing $u=1$ and $v=2^t-1$ transfers the trinomial construction to five terms. [Period bound and dyadic construction](results.pdf#page=20)
- **A primitive degree-1024 witness and an exact first failure.** Lean certifies $X^{1024}+X^{85}+X^{51}+X^{34}+1$. For infinitely many $s>10$, the same four lower terms give a squarefree pentanomial of degree $2^s$ that passes ranks 1 through 1023 and fails at rank 1024. [Full-order certificate](GF2Sparse/DyadicExample1024.lean) · [Proof of the first failure](results.pdf#page=21)
- **An irreducible pentanomial of degree $2^{127}-1$ passing 126 tests.** Let $n=2^{127}-1$ and $u=(n-1)/3$. Lean checks Ore's construction for $X^n+X+1$ and proves that cubing its roots gives the irreducible pentanomial $1+X(X^u+1)^3$. The trinomial roots and zero form a 127-dimensional binary vector space. Summing products of linear functions over this space rules out every product-one selection of fewer than 127 roots, even with repetitions. Coprime polynomials evaluated at one root give a multiplicative order greater than $2^{2^{61}}$. Applying the same root-space argument to a published primitive trinomial of Brent and Zimmermann gives an explicit irreducible pentanomial of degree $2^{74,207,281}-1$ passing the first 74,207,280 tests. [Root-product and order bounds](results.pdf#page=21) · [Brent and Zimmermann, Table 1](https://maths-people.anu.edu.au/~brent/pd/rpb266.pdf) · [Lean proof of all 126 tests](GF2Sparse/AdditiveOrbit.lean) · [Lean irreducibility proofs](GF2Sparse/Linearized.lean) · [Ore's construction in Brent, Larvala and Zimmermann](https://maths-people.anu.edu.au/~brent/pd/rpb199.pdf#page=8)
- **An all-degree sieve.** Fix $B$ and put $L=\operatorname{lcm}_{1\le d\le B}(2^d-1)$. For every $n>L+2$, the explicit polynomial $X^n+(X^L+1)(X^2+1)$ is squarefree and has no irreducible divisor of degree at most $B$. Allowing all three interior exponents to vary gives at least $LM^3$ distinct squarefree pentanomials with this property whenever $n>6LM$. [Explicit construction](GF2Sparse/LocalFactors.lean) · [Counting proof](GF2Sparse/Many.lean)
- **Odd factor count in every large degree.** For every $n>128L$, at least $n^2/(6144L^2)$ degree-$n$ pentanomials are squarefree, avoid factors of degree at most $B$, and have an odd number of irreducible factors. The exponents have gcd 1 and all fifteen unordered pair sums are distinct. Any reducible candidate in this family has a factor between degrees $B+1$ and $\lfloor n/3\rfloor$. The paper proof computes the discriminant modulo 8 in both parities. The even-degree calculation also follows from Theorem 6 of Kim and Kim. Lean certifies primitive examples from the two constructions in degrees 200 and 521. [Proof in the note](results.pdf#page=3) · [Lean examples](GF2Sparse/ParityExamples.lean) · [Reproducible factor checks](scripts/check_parity_sieve.py) · [Kim and Kim](https://doi.org/10.1155/2014/482837)
- **Four exponents in arithmetic progression.** In odd degrees $n\ge5$, cubing roots gives a bijection between primitive trinomials and primitive pentanomials containing a four-term arithmetic progression. In even degrees there are no such primitive pentanomials. The forward sampling construction goes back to Kashiwagi and Uchimura. [Lean bijection](GF2Sparse/Progressions.lean) · [Original construction](https://doi.org/10.9746/sicetr1965.18.747)
- **An exact order test by substitution.** Write $N=2^n-1$. A binary polynomial $f$ of positive degree $n$ with $f(0)=1$ is primitive exactly when $f(X^N)$ is irreducible. If $f$ is irreducible and its roots have order $h$, then $f(X^N)$ has exactly $N/h$ distinct irreducible factors, all of degree $nh$. Substitution preserves the number of terms and raises the degree to $nN$. [Lean proof](GF2Sparse/Dilation.lean) · [Butler on substitution](https://doi.org/10.1112/jlms/s1-30.4.480)
- **A norm test for five-term compositions.** Suppose $f=h^4+h+1$ with $h(0)=0$ and $\deg h=m>0$. If every prime divisor of $m$ is 3 or 5, then $f$ is irreducible exactly when $X^{(2^{4m}-1)/15}\equiv h\pmod f$. For every $m$, this congruence supplies the full 3-part and 5-part of the required order. The degree-20 pentanomial $X^{20}+X^{16}+X^5+X+1$ is primitive. In degree 184, $X^{184}+X^{46}+X^4+X+1$ passes the congruence and splits into two degree-92 factors. [Proof for any primitive outer polynomial](results.pdf#page=7) · [Lean proofs of both criteria](GF2Sparse/CompositionNorm.lean) · [Which exponent pairs give five terms](GF2Sparse/FrobeniusPairs.lean) · [Checked examples](GF2Sparse/NormExamples.lean)
- **Order bounds.** In the quotient by $X^n+(X^u+1)(X^v+1)$, the order of $X$ is at least $n^2/(2(u+v))$ for distinct positive $u,v$ with $u+v<n$. When $n$ is a power of two and $d=u+v$, the stronger bound $d^{s(s+1)/2}$ holds modulo every divisor of degree at least $s d^s$, for each positive $s$. At fixed $d$ the bound for the full quotient grows faster than every fixed power of $n$. [Quadratic bound](GF2Sparse/OrderBound.lean) · [Iterate bound](GF2Sparse/IterateOrder.lean)
- **Restrictions on the exponents.** In infinitely many degrees divisible by eight, the three interior exponents of any irreducible pentanomial must have arbitrarily large spread. Lean also proves an obstruction for exponents near a fixed rational grid. The note extends it to finite sets of real slopes and gives a quantitative bound within any prescribed residue class. [Local factors](GF2Sparse/LocalFactors.lean) · [Rational grids](GF2Sparse/Grid.lean)
- **Quadratic lifts.** If an irreducible binary polynomial of weight at most five satisfies $f(X+1)=f(X)$, its degree is 2, 4, 6, 8, or $2^u+4$ for $u\ge3$. In each of the latter degrees only two explicit families, together containing at most $2u$ candidates, survive the support and trace conditions. Primitive examples occur in degrees 2, 4, 6, 8, 12 and 20. For an irreducible outer polynomial $H$ of degree $m$ and $q=2^m$, Lean proves the exact test for $H(X^2+X)$ to be primitive. It requires $H$ to be primitive, its next-to-leading coefficient to equal 1, and $x^{q-1}$ to have order $q+1$ for a root $x$ of the lift. The last condition follows from the first two whenever $q+1$ is prime. [Support classification](results.pdf#page=9) · [Lean trace and order proof](GF2Sparse/QuadraticLift.lean)
- **A determinant test for primitivity.** For a monic degree-$n$ binary polynomial with constant term 1 and companion matrix $C$, primitivity is equivalent to $\det(I+\bigwedge^k C)=1$ for $1\le k\le\lfloor n/2\rfloor$. Each column of $\bigwedge^k C$ has at most four entries for a pentanomial. In every even degree $2m\ge4$, some irreducible polynomial passes all tests below $m$ and fails at $m$. A consequence for sparse primitive polynomials of degree greater than 8 is that a nonidentity binary Möbius symmetry of the roots forces degree $2^u+4$ and one of the quadratic-lift supports or its reciprocal. [Paper proof and matrices](results.pdf#page=11) · [Lean proof of the conjugate-product test](GF2Sparse/ConjugateProducts.lean) · [Independent finite check](scripts/check_exterior.py)
- **A sieve for reciprocal root pairs.** For every fixed $B$ and every sufficiently large degree $n$, at least $c_B\varphi(n)$ distinct product pentanomials are squarefree, have exponent gcd 1, avoid factors of degrees through $B$, and have no pair of mutually inverse roots. They all pass the first two exterior-power tests. The proof also gives an exact squarefreeness test using a polynomial of degree independent of $n$. For every fixed pair of construction parameters $L,P$, the root orders of $Y^{2(P+L)}+Y^L+1$ give an infinite progression of degrees in which every candidate is reducible. The family contains the primitive example $X^{55}+X^{46}+X^{25}+X^{21}+1$. [Proof and counting argument](results.pdf#page=11) · [Lean tests and progression obstruction](GF2Sparse/ReciprocalSieve.lean) · [Reproducible gcd checks](scripts/check_reciprocal_sieve.py)
- **An exact test for triples of trinomial roots.** For $T=X^n+X^a+1$ with $\gcd(n,a)=1$, let $D=n^2-na+a^2$. The roots in product-one triples form disjoint three-cycles among the roots of $\gcd(T,X^D-1)$. The only exceptions in this gcd are the two nontrivial cube roots of unity, if present. Thus one polynomial gcd detects both inverse pairs and triples. For every $Q=2^s$, the trinomial $X^{Q+3}+X^Q+1$ and its reciprocal pass all three tests. [Proof and counts](results.pdf#page=13) · [Lean root-order bound](GF2Sparse/TripleRoots.lean) · [Independent exterior-power check](scripts/check_trinomial_triples.py)
- **Five terms passing the first three tests.** For every $Q=2^s$ with $s\ge3$, the squarefree pentanomial $F_Q=X^Q+X^5+X^3+X^2+1$ has no three roots with product 1, even with repetition. Odd substitutions $F_Q(X^m)$ retain this property and give every degree divisible by eight. The examples in degrees 8 and 16 are primitive. [Proof in the note](results.pdf#page=14) · [Lean proof in every multiple of eight](GF2Sparse/DyadicTriples.lean) · [Reproduce the polynomial certificate](scripts/check_dyadic_triples.py)
- **Five terms in degrees near powers of two.** The same lower terms $X^5+X^3+X^2+1$ pass the first three tests in every degree $2^s+7$ and $2^s+9$. For eleven offsets $d$ in total, the exact criterion in degree $n=2^s+d>5$ is $n\not\equiv0,5\pmod7$. Lean verifies the full primitive order in degree $265=2^8+9$. [Proof and offsets](results.pdf#page=15) · [Degree-265 primitive witness](GF2Sparse/ShiftedExample.lean) · [Reproduce the classification](scripts/check_shifted_triples.py)
- **Four exterior powers with one gcd.** Let $D$ be the squarefree polynomial whose roots are all pair products, including squares. The first four tests pass exactly when $D$ is coprime to its reciprocal. The algorithm only needs powers of $X$ modulo the original polynomial. The dyadic five-term construction passes rank four in degrees $8,16,32,64,128,256,512,1024$. Its first failure in degrees 32, 64, 128 and 1024 is rank five. [Proof and algorithm](results.pdf#page=16) · [Lean lemma on products with repetition](GF2Sparse/RootProducts.lean) · [Lean quintic factor criterion](GF2Sparse/DyadicFactors.lean) · [Reproduce the fourth test](scripts/check_pair_products.py)
- **The fourth test is periodic in the dyadic exponent.** Every root in a product-one quartet of $F_{2^s}$ has degree at most 62,500. Consequently the fourth test depends only on $s$ modulo $\operatorname{lcm}(1,\ldots,62500)$. This gives infinite progressions of exponent-gcd-one pentanomials passing the first four tests and an infinite progression whose first failure is rank five. [Proof of periodicity](results.pdf#page=17) · [Exact finite-field calculation](scripts/check_quartic_period.py)
- **Four tests in every multiple of eight.** No four roots of $F_{2^s}=X^{2^s}+X^5+X^3+X^2+1$ have product 1, even allowing repetitions. For $s\ge3$ and odd $m$, every $F_{2^s}(X^m)$ passes the first four tests. The first failure is exactly rank five when $s\equiv0,1,2\pmod5$. Three binary resultants leave just four quartics to rule out. [Proof in the note](results.pdf#page=18) · [Exact resultant calculation](scripts/check_dyadic_quartets.py)

The Lean target for an all-degree proof is `GF2Sparse.Conjecture`. The gap is to force exact order $2^n-1$ for at least one candidate in each degree. That order implies irreducibility by exhausting all nonzero residues of the quotient. [Formal statement and order criterion](GF2Sparse/Basic.lean)

## Contributing

For a proof attempt, one open subproblem is to find a squarefree pentanomial in every sufficiently large degree that passes the first three exterior-power tests. The dyadic construction supplies four tests in every multiple of eight. The reciprocal-root sieve supplies the first two tests for all sufficiently large degrees. The third asks that no three distinct roots have product 1. Passing all ranks through half the prescribed degree on the same candidate proves it primitive. One explicit sequence of reducible pentanomials passes arbitrarily many tests. At degree 511 its polynomial has exactly seven factors of degree 73, and all factors in its degree-$2^{513}-1$ example have degree 262657. [Determinant criterion and sieve](results.pdf#page=11) · [Splitting-field obstruction](results.pdf#page=22) · [Lean factor degrees](GF2Sparse/ShortProducts.lean)

For a computational contribution, choose a degree interval beyond the checked-in range and run it on your own machine. The example below searches degrees 321 through 328 with Python and SymPy, using published factorizations to speed up discovery. Lean checks the primality proofs, the product of the supplied factors, and the polynomial orders. [Cunningham Project](https://homes.cerias.purdue.edu/~ssw/cun/) · [Pinned JSON transcription](https://github.com/postvakje/Reformatted-Cunningham-Project-tables/blob/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json)

~~~sh
curl -fsSL https://raw.githubusercontent.com/postvakje/Reformatted-Cunningham-Project-tables/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json -o /tmp/gf2-cunningham.json &&
  python3 scripts/make_witnesses.py --factor-table /tmp/gf2-cunningham.json --start 321 328 > /tmp/gf2-321-328.lean &&
  cp /tmp/gf2-321-328.lean GF2Sparse/Witnesses321To328.lean &&
  lake build GF2Sparse.Witnesses321To328 &&
  lake env leanchecker -v GF2Sparse.Witnesses321To328
~~~

A pull request can include the generated table and the corresponding interval theorem. Existing tables can be checked independently, so contributors can work on disjoint ranges. [Combining verified intervals](GF2Sparse/Coverage.lean)

## Verification

From the repository root, with Lean managed by elan, run

~~~sh
lake exe cache get
lake build
LEAN_NUM_THREADS=3 lake env leanchecker -v GF2Sparse
~~~

The checked-in witnesses contain the integer factorizations, their primality certificates, and the binary polynomial exponentiation checks. To reproduce the search with Python and SymPy, run

~~~sh
python3 scripts/make_witnesses.py 128 > /tmp/gf2-witnesses.lean
cmp /tmp/gf2-witnesses.lean GF2Sparse/Witnesses.lean
python3 scripts/make_witnesses.py --start 129 192 > /tmp/gf2-129-192.lean
cmp /tmp/gf2-129-192.lean GF2Sparse/Witnesses129To192.lean
python3 scripts/make_witnesses.py --start 193 256 > /tmp/gf2-193-256.lean
cmp /tmp/gf2-193-256.lean GF2Sparse/Witnesses193To256.lean
~~~

The four tables for degrees 257 through 320 use intervals of sixteen. To reproduce one of them with the factor table downloaded above, run

~~~sh
python3 scripts/make_witnesses.py --factor-table /tmp/gf2-cunningham.json --start 257 272 > /tmp/gf2-257-272.lean &&
  cmp /tmp/gf2-257-272.lean GF2Sparse/Witnesses257To272.lean
~~~

Lean verifies the certificates independently of the search. The root module imports all the results. [Certificate checker](GF2Sparse/Certificate.lean) · [Prime proofs and range coverage](GF2Sparse/Table.lean)

The degree-1024 certificate uses 64-bit blocks of the exponent. With the same downloaded factor table, it can be regenerated and replayed with

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/make_witnesses.py --factor-table /tmp/gf2-cunningham.json --start 1024 --block-size 64 1024 > /tmp/gf2-1024.lean &&
  cmp /tmp/gf2-1024.lean GF2Sparse/DyadicExample1024.lean &&
  lake build GF2Sparse.DyadicExample1024 &&
  lake env leanchecker -v GF2Sparse.DyadicExample1024
~~~

To reproduce the 424 factor-parity checks across all eight degree classes modulo 8, run

~~~sh
python3 scripts/check_parity_sieve.py
~~~

For an exhaustive count with distinct exponent pair sums, run

~~~sh
python3 scripts/check_parity_sieve.py --sidon-count 12
~~~

In degree 12 this gives zero primitive pentanomials among the 14 such supports. Lean independently proves the obstruction. The ordinary five-term conjecture allows repeated pair sums. [Degree-12 proof](GF2Sparse/ParityExamples.lean)

To reproduce the all-exponent quartet elimination in an isolated Python environment, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_dyadic_quartets.py
~~~

To compare the exterior-power test with direct order checks on all 4,095 monic binary polynomials of degrees 1 through 12 with constant term 1, run

~~~sh
python3 scripts/check_exterior.py 12
~~~
