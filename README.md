# Primitive binary pentanomials

Does every positive degree $n$ have a primitive polynomial over $\mathbb F_2$ with at most five terms? This is Conjecture 4.3.5 in the *Handbook of Finite Fields*. The all-degree question remains open here. A primitive polynomial is monic and irreducible, and the residue of $X$ has multiplicative order $2^n-1$. [Stephen D. Cohen, “Weights of primitive polynomials”](https://archive.ymsc.tsinghua.edu.cn/pacm_download/672/12637-dingjt-p2.pdf#page=133)

The [research note](results.pdf) gives the proofs, examples, and references. Its [LaTeX source](results.tex) is included.

## Results

- **An order bound for every irreducible pentanomial with exponent gcd one.** Its degree $n$ and root order $h$ satisfy $16h^3\ge5n^4$, strengthened to $16h^3\ge5n^4+10n^2+1$ in odd degree. The proof also gives a support-dependent test for a proposed period. It recovers the full order 63 of $X^6+X^4+X^3+X+1$ from two short intervals of exponents. [Proof](results.pdf#page=51) · [Check the bounds](scripts/check_exponent_spans.py)
- **Three-root test for odd-degree pentanomials with four exponents in arithmetic progression.** Among the irreducibles, the only exceptions are $X^{9d}+X^{6d}+X^{3d}+X^d+1$ and their reciprocals, with $d=73^j$. Their roots have exact order $73^{j+1}$. For odd-degree irreducibles of this shape with exponent gcd one, the root order is at least $n(n-1)+1$. [Proof](results.pdf#page=50) · [Lean sampling theorems](GF2Sparse/ProgressionTriples.lean) · [Independent check](scripts/check_trinomial_triples.py)
- **All exceptional irreducible trinomials for the three-root test.** Three roots multiply to one, with repetition allowed, precisely for $X^{bd}+X^d+1$ and their reciprocals with $(b,d)=(2,3^j),(3,7^j),(9,73^j)$, $j\ge0$. Lean checks the exclusion of every coprime tap above degree nine. Direct Frobenius-orbit checks reproduce all 13 exceptions through degree 192. [Classification and proof](results.pdf#page=49) · [Lean](GF2Sparse/TrinomialOrder.lean) · [Independent check](scripts/check_trinomial_triples.py)
- **A sharp trinomial order bound.** If $\gcd(n,a)=1$, the period of $X$ modulo $X^n+X^a+1$ is at least $n(n-1)+1$. For $a=1$ equality holds exactly when $n-1$ is a power of two. Every irreducible trinomial with $1<a<n-1$ and coprime exponents passes the first three root-product tests. [Proof](results.pdf#page=48) · [Lean quotient-ring bound and sharp family](GF2Sparse/TrinomialOrder.lean)
- **Subfield restrictions on trinomial orders.** For an irreducible trinomial with coprime exponents, every quotient of two distinct roots has the full degree $n$. If $n$ has at most two distinct prime divisors, the root order has a prime-power divisor $L$ with $\operatorname{ord}_L(2)=n$. In degree 15, every such root order is divisible by 151. [Proof and exterior-square factor degrees](results.pdf#page=52) · [Lean divisibility exclusion](GF2Sparse/TrinomialOrder.lean)
- **Primitive witnesses.** Lean proves the statement for every $1\le n\le544$. For every $5\le n\le544$ it verifies the shape $X^n+(X^u+1)(X^v+1)$, where $0<u<v$ and $u+v<n$. The degree-544 witness is $X^{544}+X^{99}+X^{65}+X^{34}+1$. The same exponent relation appears in the pentanomial entries of Table 4.8 of the *Handbook of Applied Cryptography*. Published minimum-weight tables cover degrees 2 through 640 with unrestricted interior exponents. [Lean degree coverage](GF2Sparse/Coverage.lean) · [Table 4.8 and its construction](https://cacr.uwaterloo.ca/hac/about/chap4.pdf#page=37) · [Minimum-weight tables](https://people.math.carleton.ca/~daniel/hff/)
- **Consecutive computational witnesses through degree 1228.** PARI/GP finds a primitive product pentanomial in every degree from 5 through 1228. FLINT independently verifies all 1,224 full orders and proves the 4,381 distinct integer factors prime. The final row gives $X^{1228}+X^{33}+X^{18}+X^{15}+1$. [Degrees 5–1206](data/product-witnesses-5-1206.csv) · [Degrees 1207–1228](data/product-witnesses-1207-1228.csv) · [Independent checker](scripts/check_product_range.py)
- **Every even degree through 2292.** For every even $6\le n\le2292$ the table gives a primitive $X^n+(1+X^u)(1+X^v)$ with $u+v\le299$. FLINT checks the 1,144 full orders using 6,794 distinct prime factors. The bound 299 is sharp in degree 2016. Of the 22,052 shorter supports in this family, 22,027 are reducible and the remaining 25 have proper root order. Degrees two and four are covered by the small Lean certificates. [All even-degree witnesses](data/even-least-span-6-2292.csv) · [Supplemental order factors](data/mersenne-even-2182-2292-extra.json) · [Sharpness check](scripts/check_even_span.py) · [Proof](results.pdf#page=55)
- **Six open degrees through 1280.** In the interval from 1230 through 1280, PARI/GP found 46 primitive product pentanomials. FLINT verified their exact orders and the 673 distinct prime factors used. Combining the intervals leaves 1229, 1231, 1237, 1243, 1249, and 1259 open in this project. In degree 1280 the interior exponents are 6, 49, and 55. [Witnesses](data/product-witnesses-1230-1280.csv) · [Complete order factorizations](data/mersenne-1230-1280-factors.json) · [Proof](results.pdf#page=54)
- **The first unresolved consecutive degree is 1229.** Lean proves that $X^{1229}+X^{77}+X^{50}+X^{27}+1$ is irreducible. If $K$ is the product of the four known prime factors of $2^{1229}-1$, its root order is $Kt$ with $t>1$ dividing the remaining 284-digit cofactor. A sieved product excludes every cofactor prime through 818,085,338,814,611,457. Both candidate root orders exceed $2^{345}$, and the cofactor has at most 15 prime factors counted with multiplicity. Proving that $t$ equals the cofactor would extend the consecutive range. [Product certificate](GF2Sparse/Degree1229.lean) · [Seroussi certificate](GF2Sparse/Seroussi1229.lean) · [Independent check](scripts/check_degree_1229.py) · [Sieved divisor check](scripts/check_1229_wheel.py) · [Factorization](https://factordb.com/index.php?query=2%5E1229-1)
- **A route around the unresolved factorization.** For either degree-1229 candidate, 3,399 specified logarithms in a Gauss period coordinate would prove full order. The checker derives 6,779 polynomial values from those inputs. The original 3,531-row list also suffices. Both lists use the same coordinate and accept the same submission format. The requested exponents remain open. The character-sum and counting methods already certify examples in degrees 47, 61, and 89 without factoring their group orders. Lean checks their 213 logarithm identities. [Smaller target list](data/degree-1229-period-compact.csv) · [Original target list](data/degree-1229-period-targets.csv) · [Relation checker](scripts/check_period_relations.py) · [Character-sum and counting proofs](results.pdf#page=44) · [Lean logarithm checks](GF2Sparse/FactorBaseExamples.lean)
- **Twelve primitive pentanomials in degree 4095.** One is $X^{4095}+X^{255}+X^3+X+1$. FLINT and PARI/GP independently check every sparse primitive degree-12 seed. Twelve lifts have full root order and the other six have exact index seven. The factor list and the elliptic-curve primality certificate for its 425-digit prime are included. Lean also verifies the six seventh-power obstructions. [Exact orders and seed list](results.pdf#page=37) · [FLINT check](scripts/check_ore_lifts.py) · [PARI/GP check](scripts/check_ore_4095.gp) · [Lean obstructions](GF2Sparse/OreNormObstructions.lean)
- **Larger primitive witnesses.** Lean certifies product pentanomials in degrees 1279, 2203, 2281, 3217, 4253, 4423, 9689 and 11213. The last is $X^{11213}+X^{153}+X^{83}+X^{70}+1$. It also certifies two published examples, Seroussi’s pentanomial $X^{9941}+X^{29}+X^{12}+X^{10}+1$ and the Kurita–Matsumoto trinomial $X^{44497}+X^{8575}+1$. The certificates check both Lucas–Lehmer primality and the polynomial power. [Packed squaring proof](GF2Sparse/PackedSquare.lean) · [Degree 11213](GF2Sparse/PackedMersenne11213.lean) · [Degree 44497](GF2Sparse/PackedMersenne44497.lean) · [Seroussi’s table](https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/98/HPL-98-135.pdf) · [Published trinomial table](https://maths-people.anu.edu.au/~brent/pd/rpb199.pdf)
- **Irreducible lifts of the same weight.** Replacing each exponent $i$ by $2^i-1$ takes a primitive degree-$s$ seed to an irreducible of degree $2^s-1$. Lean proves the converse and shows that every lifted polynomial passes all root-product tests of lengths below $s$. This supplies sparse irreducibles for every $1\le s\le544$, and the seed in degree 11213 gives an irreducible pentanomial of degree $2^{11213}-1$ passing 11212 tests. The degree-44497 seed gives a trinomial passing 44496 tests. For these irreducible lifts of degree $n=2^s-1$ with $s\ge5$, the logarithm base two of the root order exceeds $\sqrt{n+1}-\tfrac12\log_2(n+1)$. In the degree-$2^{2203}-1$ example the order exceeds $2^{2^{1102}-1101}$. [Lean order bound](GF2Sparse/OreOrder.lean) · [General equivalence](GF2Sparse/OreLift.lean) · [Certified examples](GF2Sparse/OreExamples.lean)
- **Prime divisors forced into lifted orders.** Every Ore root from a primitive degree-11 seed has order divisible by a prime $q$ with $\operatorname{ord}_q(2)=2047$. The analogous result holds for degree-15 seeds with $\operatorname{ord}_q(2)=32767$. The proof separates products of conjugates and works without factoring either lifted group order. The integer lower bound from mixed seed degrees also gives $\log_2\operatorname{ord}(r)\ge \tfrac32\log_2(3)\sqrt{n+1}-O(\log n)$ for all primitive seeds, where $n$ is the lifted degree. [Divisor theorem and proof](results.pdf#page=39) · [Lean proof of the integer bound](GF2Sparse/OreOrderCounts.lean) · [Arithmetic checker](scripts/check_ore_components.py)
- **Two nonprimitive lifts in degree 2047.** The primitive seeds with interior exponents $(2,3,7)$ and $(4,8,9)$ give lifts whose root orders omit 47. Lean checks explicit 47th roots of $X$ for both. The other 44 sparse primitive seeds pass all seven known prime-factor tests. A 549-digit cofactor remains in the order calculation. [Lean exclusions](GF2Sparse/OreIndexFortySeven.lean) · [Reproduce all 46 checks](scripts/check_ore_2047.py)
- **Full-order Ore lifts.** Lean verifies the primitive trinomials $X^{511}+X^{15}+1$ and $X^{1023}+X^7+1$. Of the 83 primitive binary trinomials and pentanomials in seed degrees 2 through 10, 81 have primitive lifts. The two exceptions give irreducible degree-63 pentanomials of exact root order $(2^{63}-1)/7$. [Primitive certificates](GF2Sparse/OrePrimitiveExamples.lean) · [Both exceptions in Lean](GF2Sparse/OreIndexSeven.lean) · [Reproduce the census](scripts/check_ore_lifts.py)
- **Exact degrees of Ore-root norms.** Take a primitive degree-$s$ seed, a lifted root $r$, and a divisor $b$ of $s$. Set $m=(2^s-1)/(2^b-1)$. The norm of $r$ to the degree-$m$ field has degree exactly $m$, and its conjugates span a binary space of dimension $(s/b)^b$. When $s=2b$, adding one to the norm gives a normal basis generator. [Proof in the research note](results.pdf#page=33) · [Lean proofs of the norm algorithm and the criterion for a given expansion](GF2Sparse/OreNorms.lean)
- **A normal basis from any primitive seed.** For every nonzero binary subspace of the additive Ore roots, take the product of its nonzero elements. Distinct subspaces give distinct elements of the root's multiplicative subgroup. Summing the products for the successive spans of $r,r^2,\ldots,r^{2^{s-1}}$ gives a normal basis generator of the entire lifted field of degree $2^s-1$. [Exterior-power proof](results.pdf#page=35) · [Independent finite-field checks](scripts/check_ore_bases.py)
- **Reciprocal primitive seeds have the same lifted root order.** In seed degree $s$, every root of the reciprocal lift is a product of exactly $2^{s-1}-1$ distinct roots of the original lift. The two root sets generate the same multiplicative group. This explains why the two degree-63 exceptions occur together and proves primitivity of two further trinomials, $X^{511}+X^{31}+1$ and $X^{1023}+X^{127}+1$. [Lean reciprocity proof](GF2Sparse/OreReciprocal.lean) · [Both trinomial proofs](GF2Sparse/OreReciprocalExamples.lean) · [Proof in the note](results.pdf#page=32)
- **Exact factor degrees from seed orders.** For any constant-one seed, the largest irreducible factor degree in its Ore lift equals the multiplicative order of $X$ modulo the seed. If the seed is irreducible, every factor has that degree. The two exceptional degree-63 examples each give a second pentanomial of degree $2^{63}-1$ with exactly seven distinct irreducible factors of degree 1,317,624,576,693,539,401. [General Lean proof](GF2Sparse/OreFactors.lean) · [Exact factor counts](GF2Sparse/OreFactorExamples.lean)
- **Three-root test for dyadic taps.** For a root of $X^n+X^{2^i}+1$, membership in a product-one triple is equivalent to $(1+x)^m=x^m+1$, where $m=n-2^i$. Every irreducible such trinomial above degree nine passes the first three tests. For $n=2^i+2^b(2^{2j}-2^j+1)$ with $j$ coprime to six, the trinomial passes for all $i,b$. [Lean criterion](GF2Sparse/DyadicTap.lean) · [Lean family and degree bound](GF2Sparse/KasamiTriples.lean) · [Complete counts and proof](results.pdf#page=41)
- **Translating whole intervals of witnesses.** For arbitrarily large common shifts $T$, changing just the leading term in each checked pentanomial of degree $5\le j\le544$ gives 540 consecutive squarefree, exponent-gcd-one pentanomials. At degree $T+j$, the shortest selection of roots with product 1 has length exactly $j$. Each enlarged polynomial contains its original seed as a factor. The same theorem transfers the degree-2203 witness to arbitrarily high degrees with first failure exactly 2203. [Lean proof for all 540 tails](GF2Sparse/TranslatedInterval.lean) · [General transfer theorem](GF2Sparse/ShiftedPeriods.lean) · [Proof for simultaneous translations](results.pdf#page=30)
- **Three tests for every degree with at most three ones in binary.** For every such $n\ge4$, a squarefree binary polynomial with at most five terms has no product of one, two or three roots equal to 1. For odd $n>7$ one of the four trinomials $X^n+X^a+1$ with $a=3,4,5,7$ works. For $n\equiv2\pmod4$ above 11 the choices are $3,7,11$. Two commuting Frobenius powers reduce the infinitely many degrees to 2,628 and 171 unordered residue pairs. [Proof in the note](results.pdf#page=24) · [Reproduce the finite calculation](scripts/check_binary_degree_triples.py)
- **Three tests for signed binary degrees.** Every $n\ge4$ expressible as a sum of at most three signed powers of two has a squarefree polynomial of weight at most five passing the first three root-product tests. At every odd such degree there is a trinomial with coprime exponents. For $n=2^s-2^t-1$ with $1\le t\le s-2$, two integer gcds determine exactly which powers of two work as the inner exponent, and at least one always works. [Proof and choice of exponent](results.pdf#page=27) · [Lean choice for every $s,t$](GF2Sparse/SignedDegreeChoices.lean) · [Lean 999-one example](GF2Sparse/SignedTriples.lean) · [Reproduce the finite cases](scripts/check_binary_degree_triples.py)
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

The equivalent Ore target asks for a constant-one irreducible of degree $2^s-1$ for every $s>0$, using at most five exponents of the form $2^i-1$. The Lean theorem `conjecture_iff_sparseOreIrreducible` converts a proof of this target directly into the original conjecture. [Formal equivalence](GF2Sparse/OreConjecture.lean)

## Contributing

In degree 1229, every primitive witness of weight at most five must have exactly five terms. Proper factors exclude all 1,228 trinomials and, by power sampling, 1,866 pentanomial supports including every four-term arithmetic progression. The `--trinomials` option of the degree-1229 checker replays the complete exclusion. [Factor table](data/degree-1229-trinomial-factors.csv) · [Lean exclusion](GF2Sparse/Trinomial1229.lean) · [Proof](results.pdf#page=53)

The five other gaps through 1280 each have an irreducible product pentanomial with a partially certified order. The public JSON records its taps, the known prime factors, the exact remaining cofactor, and a divisor-search residue. For each candidate the checker proves that the root order includes the full known part and at least one cofactor prime above $10^{13}$. The five degrees can be investigated independently. [Open-degree candidates and cofactors](data/open-degrees-1231-1259.json) · [Checker](scripts/check_open_degrees.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_open_degrees.py
~~~

Both degree-1229 candidates pass the first nine exterior-power tests. One known prime divisor of their root orders suffices. The checker compares 77,221,860 exact residues for ranks one through eight, then tests all 3,662,491,560 five-term windows needed for rank nine. The full run took 142 seconds with 16 threads and about 1.7 GiB of memory. [Proof](results.pdf#page=52) · [Integer checker](scripts/check_1229_short_products.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/check_1229_short_products.cpp -lgmpxx -lgmp -o /tmp/gf2-check-1229-products
OMP_NUM_THREADS=16 /tmp/gf2-check-1229-products --nine
~~~

The two degree-1229 candidate fields also admit a common polynomial coordinate. Let $r$ be the root of the selected candidate and $a=z+z^{-1}$ for an element $z$ of order 2459. To obtain the exact mask of $a$ in the power basis of $r$, run the command below. It checks $a\ne0$, $D_{2459}(a)=0$, and the degree-1229 period polynomial at $a$. Here $D_j(z+z^{-1})=z^j+z^{-j}$. The residues $\pm2^k$ for $0\le k<1229$ exhaust the nonzero residues modulo 2459, so $D_j(a)$ for each such residue is a known Frobenius power of $a$. Lean proves the signed Frobenius identity, the degree of every order-2459 period, and the subgroup step for an invertible coefficient. [Coordinate construction](scripts/period_coordinate.py) · [Lean proofs](GF2Sparse/GaussPeriod.lean)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/period_coordinate.py
~~~

For a proof attempt, one open subproblem is to find a squarefree pentanomial in every sufficiently large degree that passes the first three exterior-power tests. The dyadic construction supplies four tests in every multiple of eight. The reciprocal-root sieve supplies the first two tests for all sufficiently large degrees. The third asks that no three distinct roots have product 1. Passing all ranks through half the prescribed degree on the same candidate proves it primitive. One explicit sequence of reducible pentanomials passes arbitrarily many tests. At degree 511 its polynomial has exactly seven factors of degree 73, and all factors in its degree-$2^{513}-1$ example have degree 262657. [Determinant criterion and sieve](results.pdf#page=11) · [Splitting-field obstruction](results.pdf#page=22) · [Lean factor degrees](GF2Sparse/ShortProducts.lean)

For the all-degree three-test problem it suffices to handle $p$ and $2p$ for each prime $p\ge5$. A squarefree, constant-one witness in either seed degree gives one in each odd multiple by substituting $X^m$ for $X$. Seeds 6 and 9 handle the remaining powers of three and their doubles, and the existing construction covers multiples of four. The signed-power theorem supplies some of these prime and twice-prime degrees. [Reduction and signed-degree proof](results.pdf#page=29)

For degree 2047, determining whether one of the 44 remaining lifts is primitive would settle the order of an explicit sparse candidate. The partial census includes all known prime divisors and a separate test proving that at least one prime in the remaining cofactor divides each order. [Partial census](scripts/check_ore_2047.py) · [Remaining integer cofactor](https://factordb.com/index.php?id=1000000000000002047)

For a Lean contribution, Section 28 gives an explicit normal basis in the field generated by an Ore root. The Vandermonde criterion for independence is formalized. The remaining step is to formalize the expansion of the Moore determinant that supplies its distinct nodes. [Written proof](results.pdf#page=35) · [Lean criterion](GF2Sparse/OreNorms.lean)

For work on the first unresolved degree, run the degree-1229 checker below. It prints the exact 284-digit cofactor. A factor of this integer would narrow the remaining order tests. A complete factorization, together with a nonidentity power for each remaining prime divisor, would certify the displayed pentanomial.

For the period-coordinate targets, a submission row `mask,exponent` means $B_{\rm mask}(a)=r^{\rm exponent}$ for one named candidate. Bit $i$ of the mask is the coefficient of $T^i$. Contributors can take disjoint rows. The checker accepts partial lists and verifies each supplied or derived exponent in the chosen field. [Download the 3,399 targets](data/degree-1229-period-compact.csv) · [Original 3,531 targets](data/degree-1229-period-targets.csv) · [Polynomial identities](data/degree-1229-period-relations.jsonl)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_period_relations.py --compact
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_period_relations.py --candidate seroussi --logs /path/to/period-logs.csv
~~~

To regenerate all 2,345 degree-1229 rows, enumerate the smooth Dickson substitutions and factor three specified pairs of affine supports. [Dickson fibre enumeration](scripts/period_fibres.py) · [Affine support witnesses](data/degree-1229-period-supports.csv)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/find_period_relations.py 1229 --factor-degree 16 --fibres --supports data/degree-1229-period-supports.csv > /tmp/gf2-period1229.jsonl
cmp /tmp/gf2-period1229.jsonl data/degree-1229-period-relations.jsonl
~~~

The period method has a complete degree-89 example. One supplied exponent and 214 polynomial identities recover all 71 values through degree eight and prove full order for both the Gauss period and the sparse root. The first command checks it. The second regenerates the relations. The search can also extend the degree-1229 relation file with `--seed`. [Working relation search](scripts/find_period_relations.py) · [Degree-89 certificate](data/degree-89-period-relations.jsonl)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_period_relations.py --example-89
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/find_period_relations.py 89 --factor-degree 10 --target-degree 8 --spans 16 20 24 28 32 36 40 > /tmp/gf2-period89.jsonl
cmp /tmp/gf2-period89.jsonl data/degree-89-period-relations.jsonl
~~~

The power-basis route for Seroussi’s polynomial has a separate list of 4,993 masks evaluated at $r$. [Download the power-basis targets](data/degree-1229-seroussi-targets.csv)

Encode a monic binary polynomial by its coefficient bits. A row `mask,exponent` asserts that this polynomial equals the indicated power of $X$ in the field. The checker accepts independent partial lists, verifies each equality, and reports whether their combined degree counts force full order. To reproduce a complete smaller example and check a partial degree-1229 submission, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_factor_base.py 47
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/find_factor_base_logs.py 47 --taps 1 4 5 --factor-degree 8 > /tmp/gf2-logs47.csv
cmp /tmp/gf2-logs47.csv data/factor-base-47.csv
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_factor_base.py 1229 --seroussi --extended-index --logs /path/to/logs.csv
~~~

The `--extended-index` option replays both large progression products. Omitting it uses the shorter trial bound and a sufficient set of 5,678 values. The example uses Seroussi’s taps 2, 6 and 15. Omit `--seroussi` for the product pentanomial with taps 27, 50 and 77. Each list must use a single field modulus. [Published progression residues](data/degree-1229-progression-products.json)

For a computational contribution, choose a degree interval beyond the Lean-verified range and run it on your own machine. The example below certifies degrees 545 through 560 from their public CSV witnesses with Python, SymPy and FLINT. The published factorizations give the orders to test, and FLINT speeds up the search for primality certificates. Lean checks the primality proofs, the product of the supplied factors, and the polynomial orders. [Cunningham Project](https://homes.cerias.purdue.edu/~ssw/cun/) · [Pinned JSON transcription](https://github.com/postvakje/Reformatted-Cunningham-Project-tables/blob/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json)

~~~sh
curl -fsSL https://raw.githubusercontent.com/postvakje/Reformatted-Cunningham-Project-tables/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json -o /tmp/gf2-cunningham.json &&
  uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/make_packed_table.py 545 560 --factor-table /tmp/gf2-cunningham.json > /tmp/gf2-545-560.lean &&
  cp /tmp/gf2-545-560.lean GF2Sparse/Witnesses545To560.lean &&
  lake build GF2Sparse.Witnesses545To560 &&
  lake env leanchecker -v GF2Sparse.Witnesses545To560
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

The eleven tables for degrees 257 through 432 use intervals of sixteen. To reproduce one of them with the factor table downloaded above, run

~~~sh
python3 scripts/make_witnesses.py --factor-table /tmp/gf2-cunningham.json --start 257 272 > /tmp/gf2-257-272.lean &&
  cmp /tmp/gf2-257-272.lean GF2Sparse/Witnesses257To272.lean
~~~

Lean verifies the certificates independently of the search. The root module imports all the results. [Certificate checker](GF2Sparse/Certificate.lean) · [Prime proofs and range coverage](GF2Sparse/Table.lean)

The seven tables for degrees 433 through 544 use packed binary squaring for the full power and each prime-factor test. To reproduce an interval, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/make_packed_table.py 433 448 --factor-table /tmp/gf2-cunningham.json > /tmp/gf2-433-448.lean &&
  cmp /tmp/gf2-433-448.lean GF2Sparse/Witnesses433To448.lean
~~~

To check every row in the 1230–1280 table and print the five degrees skipped by that table, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --available --start 1230 --end 1280 --factor-table data/mersenne-1230-1280-factors.json --verify data/product-witnesses-1230-1280.csv
~~~

For a new search, `--least-span` visits supports in increasing order of $u+v$ and breaks ties by $u$. An even `--start` with `--step 2` selects the even degrees. The `--jobs` option distributes both the PARI search and the independent FLINT verification across workers.

To verify all 1,144 even-degree rows, use the pinned Cunningham table downloaded above and the nine supplemental factorizations. Substituting `--least-span --search` for `--verify` and its CSV path regenerates the table with PARI/GP.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --factor-table /tmp/gf2-cunningham.json --factor-table data/mersenne-even-2182-2292-extra.json --start 6 --end 2292 --step 2 --jobs 8 --verify data/even-least-span-6-2292.csv
uv run --no-project --with python-flint==0.9.0 python scripts/check_even_span.py --factor-table /tmp/gf2-cunningham.json --jobs 8
~~~

To check both CSV files through degree 1228, run the first two commands. The first interval uses the pinned factor table downloaded above. The second includes its complete factorizations in the repository. The last command repeats the first search with PARI/GP.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --factor-table /tmp/gf2-cunningham.json --end 1206 --verify data/product-witnesses-5-1206.csv
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --factor-table data/mersenne-1207-1228-factors.json --start 1207 --end 1228 --verify data/product-witnesses-1207-1228.csv
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --factor-table /tmp/gf2-cunningham.json --end 1206 --search --jobs 4 > /tmp/gf2-product-range.csv &&
  cmp /tmp/gf2-product-range.csv data/product-witnesses-5-1206.csv
~~~

The Ore lift census and its two large full-order certificates use the same factor table.

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_lifts.py --factor-table /tmp/gf2-cunningham.json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_lifts.py --factor-table /tmp/gf2-cunningham.json --lean > /tmp/gf2-ore.lean &&
  cmp /tmp/gf2-ore.lean GF2Sparse/OrePrimitiveExamples.lean
~~~

To verify all eighteen degree-4095 orders, run either of these independent checks from the repository root. Both use the checked-in factors.

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_lifts.py --seed-degree 12 --factor-table data/mersenne-4095-factors.json
gp -q -f scripts/check_ore_4095.gp
~~~

The 425-digit prime also has a CoqPrime proof. The generator converts the stored PARI certificate into 67 elliptic steps and a Pocklington proof for the terminal prime. The proof uses Coq’s standard 63-bit integer operations and specifications. With Coq 8.18 and CoqPrime installed, the following commands compile and replay the proof. [CoqPrime](https://github.com/thery/coqprime)

~~~sh
uv run --no-project --with sympy python scripts/make_ore_prime_certificate.py /tmp/ore4095-coq --jobs 8 --check
(cd /tmp/ore4095-coq && coqchk -silent -bytecode-compiler yes Ore4095Prime)
~~~

To reproduce the degree-4095 norm obstruction and cross-check both ways of computing the norm, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_norms.py 12 4 --direct --factor-table /tmp/gf2-cunningham.json
~~~

To check a normal basis in degree 4095 or exhaust all subspaces for each primitive sparse degree-six seed, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_bases.py 12 --factor-table /tmp/gf2-cunningham.json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_bases.py 6 --all-subspaces --factor-table /tmp/gf2-cunningham.json
~~~

To regenerate the six seventh-power certificates and replay them in the kernel, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/make_ore_index_witnesses.py > /tmp/gf2-ore-index.lean &&
  cmp /tmp/gf2-ore-index.lean GF2Sparse/OreNormObstructions.lean &&
  lake build GF2Sparse.OreNormObstructions && lake env leanchecker -v GF2Sparse.OreNormObstructions
~~~

The degree-44497 Lean build used about 30 GiB of peak memory on the development machine. To regenerate the certificate and replay it in the kernel, run

```sh
python3 scripts/make_packed_mersenne.py --trinomial 44497 8575 --block 256 > /tmp/gf2-44497.lean &&
  cmp /tmp/gf2-44497.lean GF2Sparse/PackedMersenne44497.lean &&
  env LEAN_NUM_THREADS=1 lake build GF2Sparse.PackedMersenne44497 &&
  env LEAN_NUM_THREADS=1 lake env leanchecker -v GF2Sparse.PackedMersenne44497
```

The first command checks the degree-1229 field arithmetic. The second replays the complete sieved divisor bound in six blocks. Each of the four new blocks used about 25 GiB on the reference run.

```sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_degree_1229.py
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_wheel.py --threads 4
```

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
