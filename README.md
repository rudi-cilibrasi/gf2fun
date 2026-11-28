# Primitive binary pentanomials

Does every positive degree $n$ have a primitive polynomial over $\mathbb F_2$ with at most five terms? This is Conjecture 4.3.5 in the *Handbook of Finite Fields*. The all-degree question remains open here. A primitive polynomial is monic and irreducible, and the residue of $X$ has multiplicative order $2^n-1$. [Stephen D. Cohen, “Weights of primitive polynomials”](https://archive.ymsc.tsinghua.edu.cn/pacm_download/672/12637-dingjt-p2.pdf#page=133)

**Degree 1229 is the first gap in this repository.** Every positive degree through 1228 has a verified witness. In degree 1229 all trinomials are reducible, and 639,144 of the 639,166 irreducible pentanomials pass the four known prime-index tests. The remaining cofactor has at most 14 prime factors. A counterexample would require one of them to exclude at least 22,827 surviving reciprocal pairs. Every surviving root has order exceeding $2^{349}$. A 14-bit index for the pairs failing each remaining prime would prove at least 90,196 primitive pairs. The required bound on these failure classes is open. [Census](data/degree-1229-pentanomial-census.csv) · [Divisor bound and coding argument](results.pdf#page=387)

**More than $2^{655}$ primitive polynomials in degree 1229 have at most 301 terms.** More than $2^{654}$ can have their first 516 interior coefficients zero. At 303 terms the corresponding counts exceed $2^{658}$ and $2^{657}$. The proof bounds the error by counting short descriptions of the additive characters that contribute to it. [301-term proof](results.pdf#page=389) · [303-term count](results.pdf#page=388) · [Exact calculation for both bounds](scripts/check_1229_signed_weight.py) · [Lean arithmetic](GF2Sparse/SignedWeight1229.lean)

Every irreducible degree-1229 pentanomial passes the first ten tests involving products of conjugate roots. If any of the 639,144 survivors is nonprimitive, more than 270 billion subsets of at most 596 conjugates have product one. Its first failing subset must have size between 11 and 596. [Proof and counts](results.pdf#page=201) · [Reproduce the upper bound](scripts/check_1229_failure_ranks.py)

The [research note](results.pdf) gives the proofs, examples, and references. Its [LaTeX source](results.tex) is included.

## Results

- **Degree 41,681 has exactly fourteen primitive trinomials, forming seven reciprocal pairs.** The smallest tap is 3,429. The pentanomial with interior taps 5,535, 11,070 and 36,146 also has full order $2^{41681}-1$. With degrees 41,681 and 53,381 included, the 85-degree trinomial census covers 577,649 reciprocal classes, of which 143 are irreducible and 135 primitive. [Primitive taps](data/mers-project-trinomial-census.csv) · [Factorization and certificate replay](results.pdf#page=363)

- **A 20-bit index describes every exceptional pentanomial in degree $1229m$ for any product $m>1$ of the four known primes, with arbitrary powers.** Here exceptional means that no prime in the root order has binary degree divisible by both 1229 and a prime of $m$. At $m=36{,}871\cdot46{,}703$ there are exactly 639,144 exceptions. Multiplying their three base taps by $m$ decodes them. The same count holds for the product of all four known primes, where an unrestricted tap rank takes 888 bits. Taking $m=2^{1229}-1$ makes the exceptional set correspond exactly to the primitive degree-1229 pentanomials, whose number remains open. [Proof and decoder](results.pdf#page=375) · [Lean base tests](GF2Sparse/OrderPrimePartitions.lean) · [Finite verifier](scripts/check_multiprime_supports.py)

- **Two bits identify every exceptional pentanomial in degree $5\cdot31^j$ for all $j\ge1$.** Exactly four irreducible pentanomials have no root-order prime whose binary degree is divisible by 155. Take any three of $31^j,2\cdot31^j,3\cdot31^j,4\cdot31^j$ as the interior exponents. All four have root order $31^{j+1}$. In degree 148,955 an unrestricted support rank takes 49 bits. [Proof](results.pdf#page=381) · [Verifier and expanded examples](scripts/check_five_31_tower.py)

- **For an irreducible trinomial $X^n+X^k+1$ of degree $n=p^i q^j$ with distinct odd primes $p<q$ and $i,j\ge1$, the root order contains a prime of binary degree $n$ exactly when $q$ does not divide $k$.** Both prime powers are unrestricted. For pentanomials and $p\ge5$, failure means that the root lies in the product of the maximal subfields or every tap is divisible by $q$. The remaining tower is $5\cdot31^j$ with $j\ge2$, where eight triples of tap residues can also occur in the necessary condition. [Trinomial theorem](results.pdf#page=372) · [Pentanomial theorem and 9-bit codes in degrees 15,025 and 45,025](results.pdf#page=378) · [Cyclotomic verifier](scripts/check_cyclotomic_row_isolation.py)

- **In degree $pq$ with distinct odd primes $p<q$ and $p\le10{,}000$ or $pq>(p+1)^3$, a sparse irreducible misses a full-degree prime in its root order exactly when it is $G(X^q)$.** A full-degree prime $\ell$ satisfies $\operatorname{ord}_{\ell}(2)=pq$. In degrees 45,314,459 and 57,397,987 there are exactly 639,156 and 639,154 exceptional pentanomials. Each has a 20-bit index among the exceptions given the degree, compared with 74 or 75 bits for unrestricted three-tap supports. [Theorem and proof](results.pdf#page=364) · [Exact counts and incompressibility argument](results.pdf#page=367) · [Verifier](scripts/check_kummer_sparse_orders.py)

- **An explicit 1,221-bit trace record in degree 1229 has exactly two irreducible representatives.** Both are pentanomials. One fails the 36,871 order test, leaving only the polynomial with interior taps $(136,138,604)$ as a possible primitive representative. A second, 1,219-bit record also has just two irreducibles, and both fail known tests. A modular inverse lists all monic candidates for any record with one known irreducible representative. [Proof and explicit records](results.pdf#page=360) · [Decoder and exhaustive checks](scripts/check_trace_fibres.py)

- **In degree 1229 more than 97% of all 1,200-bit power-trace records each occur for over 100,000 primitive polynomials.** All six binary projective images of each root are primitive. Among 1,180-bit records, fewer than one in 524,288 can have at most $2^{37}$ representatives. Given the trace locations, every such exception has a 1,161-bit rank. The proof works in large degrees for almost all records of up to $n-(2+\varepsilon)\log_2 n$ bits. A degree-1229 pentanomial's three taps take only 29 bits to specify, so its record can still lie in the exceptional set. [Proof and incompressibility argument](results.pdf#page=357) · [Verifier](scripts/check_trace_incompressibility.py)

- **In degree 1229 every prescription of 598 bits of initial power-trace data is realized by more than $2^{618}$ primitive polynomials.** The traces can be prescribed at any binary closed points, including zero and infinity. For every counted root $r$, both $1+r$ and $r/(1+r)$ are primitive too. Yet two pentanomials agree on the first 1,364 inverse and 1,058 positive power traces despite differing at the 36,871 order test. In all sufficiently large degrees the theorem permits nearly half the degree in prescribed bits. [Proof](results.pdf#page=353) · [Sharp sparse comparisons](results.pdf#page=356) · [Verifier](scripts/check_prescribed_root_traces.py)

- **In every sufficiently large degree, at least $2^{n/2}$ primitive polynomials have at most $\log_2 n+O(\sqrt{\log n\,\log\log n})$ odd-degree terms.** All those terms lie in the last $2\log_2 n+O(1)$ odd positions. In even degree any block of that length works. In degree 1229 more than $2^{617}$ primitive polynomials have at most eleven odd-degree terms, all between exponents 1197 and 1229. The inverse roots have their first 1196 power traces zero. [All-degree proof](results.pdf#page=344) · [Degree 1229](results.pdf#page=346) · [Verifier](scripts/check_sparse_odd_coefficients.py) · [Lean arithmetic](GF2Sparse/OddCoefficientBounds.lean)

- **A quadratic family of 8,193 degree-1229 polynomials contains at least 8,163 primitive members.** Each unknown prime can exclude at most two parameter values. The only pentanomials in the tested interval are the two starting examples, whose orders remain open. A quadratic family with 31 five-term positions passing the four known tests at distinct residues modulo each cofactor prime would settle the degree. In degree 10 the same counting argument finds one primitive member among five pentanomials, and all four exclusions occur. [Incompressibility argument](results.pdf#page=342) · [Computed examples](results.pdf#page=343) · [Lean root count](GF2Sparse/SubgroupCover.lean)

- **If a primitive binary polynomial of degree greater than one has at most five terms, the positive exponents of its translate $f(X+1)$ have gcd 1, 3 or 5.** When the gcd exceeds one, the translate is a trinomial and just three explicit families are possible. The values 3 and 5 occur in degrees 6 and 20. Through degree 262,146 the remaining candidates for primitivity in these families are in degrees 4,098 and 262,146. [Proof and families](results.pdf#page=339) · [Verifier](scripts/check_cubic_components.py) · [Lean identities](GF2Sparse/CubicComponents.lean)

- **Exactly four irreducible trinomials or pentanomials have the form $G(X^3+X)$ or $G(X^3+X^2)$.** They are all primitive, in degrees 3, 3, 9 and 12. Including every cubic substitution adds exactly two primitive examples through degree 4,097, in degrees 6 and 66. In degree 4,098 there is just one possible cubic substitution witness, and its full order is open. [Classification](results.pdf#page=337) · [All cubic substitutions](results.pdf#page=340)

- **For almost every product of a fixed number of distinct odd primes, every sparse irreducible root order has a prime connecting any chosen partition of the degree factors.** For a partition $n=st$ with $s,t>1$, this prime divides neither $2^s-1$ nor $2^t-1$. Through 70,000 the property holds in exactly 20,201 of the 21,436 odd squarefree composite degrees. The other 1,235 have explicit sparse counterexamples to this order property. [Proof and exact counts](results.pdf#page=335) · [Witnesses](data/squarefree-order-prime-exceptions.csv) · [Lean dilation criterion](GF2Sparse/OrderPrimePartitions.lean)

- **For a density-one set of semiprime degrees $n$, every sparse irreducible root has a prime divisor $\ell$ of its order with $\operatorname{ord}_{\ell}(2)=n$.** Among the 14,424,896 degrees $pq\le10^8$ with distinct odd primes $p<q$, precisely 221 allow an exception. They are exactly the pairs with $q\mid2^p-1$, and each has an explicit irreducible trinomial or pentanomial demonstrating the exception. [Density proof and exact count](results.pdf#page=333) · [221 witnesses](data/semiprime-full-degree-prime-exceptions.csv) · [Verifier](scripts/check_semiprime_order_primes.py)

- **Across every degree $3q$ and $5q$ with $q$ prime and larger than the first factor, exactly four reciprocal pairs miss a full-degree prime in the root order.** One pair in degree 21 has order 49. Three pairs in degree 155 have order 961. In degree 253 all 23 exceptions have order 47,081. [Classification and proof](results.pdf#page=334) · [Exhaustive verifier](scripts/check_semiprime_order_exceptions.cpp)

- **No sparse irreducible of odd degree can have a root from two proper subfields of coprime degrees if the smaller degree is at most 1,000.** This covers every odd degree through one million. For distinct odd primes $p<q$, the root order in degree $pq$ contains a prime power of binary multiplicative degree $pq$ whenever $p\le10{,}000$ or $pq>(p+1)^3$. The second condition has no upper bound on $p$. One example has degree 1,002,402,160,679, where a prime divisor of full binary degree is forced. [Degree bound](results.pdf#page=329) · [Finite cases and example](results.pdf#page=331) · [Lean square identity](GF2Sparse/SubfieldSquare.lean)

- **The 31st power of a sparse irreducible root has degree $n/\gcd(31,g)$ outside two explicit families.** The exceptions are the degree-five irreducibles and four degree-ten pentanomials with $X$ replaced by $X^{3^i}$. In each exception the degree falls to $n/5$. [Proof and polynomials](results.pdf#page=332) · [Verifier](scripts/check_subfield_square.py)

- **The seventh power of a sparse irreducible root has degree $n/\gcd(7,g)$, with two exceptions up to reciprocation.** Here $g$ is the gcd of the polynomial's exponents. The exceptions have degrees 3 and 6 and root orders 7 and 21. As a consequence, for every prime $q>3$ and every sparse irreducible of degree $3q$, its root order contains a prime that first divides $2^d-1$ at $d=3q$. The two exceptions to this prime-divisor conclusion are $X^{21}+X^7+1$ and its reciprocal, both of root order 49. [Proof and trace calculation](results.pdf#page=327) · [Verifier](scripts/check_seventh_power_degree.py) · [Lean trace identities](GF2Sparse/SeventhPowerDegree.lean)

- **In degree 7 and every prime degree $n\ge13$, the eight powers $z^{\pm1},z^{\pm3},z^{\pm5},z^{\pm7}$ of any sparse irreducible root have distinct degree-$n$ minimal polynomials.** In all odd degrees greater than one, only four families have any collision. Their normalized degrees are 3, 5, 9 and 11. Among the first six powers the only exceptions are the two irreducible cubics with $X$ replaced by $X^{7^i}$. For example, $3\equiv5\cdot2^{5309}$ modulo 3,118,439 rules out that root order in degree 6,067. [Odd-degree theorem and exhaustive calculation](results.pdf#page=324) · [Signed exceptions](data/sparse-power-orbit-exceptions.csv) · [Independent prime-degree argument](results.pdf#page=323)

- **In every degree, the third and fifth powers of a sparse irreducible root can be conjugate up to inversion in exactly three families, counting reciprocals.** Their base degrees and root orders are $(3,7)$, $(8,17)$ and $(12,91)$. The last family includes the irreducible $X^{1092}+X^{910}+X^{819}+X^{91}+1$, of root order $8281$. [Polynomials, exponents and proof](results.pdf#page=326) · [Verifier](scripts/check_power_orbit_collisions.py)

- **For any number of terms, two different odd powers of a sparse root can be conjugate only up to an explicit degree.** Let $w$ be the weight, $g$ the exponent gcd and $L=\operatorname{lcm}(a,b)$ for distinct positive odd $a,b$. If $z^a$ is conjugate to $z^b$, the normalized degree $n/g$ is at most $L^{w-2}$. For conjugacy to $z^{-b}$ the bound is $(2L)^{w-2}$. [Proof](results.pdf#page=321) · [Lean proof of the order implications](GF2Sparse/PowerOrbitBounds.lean)

- **In every prime degree $n\ge13$, an irreducible binary polynomial with at most five terms has root order greater than $256n+1$.** The smallest order across these degrees is 8,191, attained by $X^{13}+X^5+X^2+X+1$. When $2^n-1=sP$ with $P$ prime and $s\le256n+1$, the full power of $P$ in the group order divides every such root order. [Proof and small-degree exceptions](results.pdf#page=319) · [Reproduce the sieve and factor counts](scripts/check_sparse_root_orders.py)

- **In odd degree above one, the cube of a sparse irreducible root can be conjugate to the root or its inverse in exactly one family.** The exceptions are $X^{3d}+X^d+1$ and their reciprocals for $d=7^a$, $a\ge0$. In each case the cube is conjugate to the inverse. This gives an arithmetic exclusion for subgroups of any size and rules out order 12,189,337 in degree 26,731. [Proof](results.pdf#page=320) · [Cubing verifier](scripts/check_cubing_chains.py)

- **If the exponents lie in two short arithmetic progressions of the same step, the root order has a quadratic lower bound in the degree.** For an irreducible $X^n+X^{n-a}+X^{2a}+X^a+1$ with $\gcd(a,n)=1$, the order is at least $5n^2/16$. In degrees 28,759 and 28,771 this already excludes the subgroup of order 226,160,777 and 104,726,441, respectively. [Proof for general progressions](results.pdf#page=318) · [Support verifier](scripts/check_exponent_spans.py) · [Lean proof for common exponent divisors](GF2Sparse/SparseOrderBounds.lean)

- **In every degree $n=7q^b$ with $q>7$ prime and $b\ge1$, three exponents among seven equally spaced positions force a full-degree prime power in the root order of an irreducible pentanomial.** This means that $h$ divides the root order and $n$ is the first positive integer with $2^n\equiv1\pmod h$. One can take $h$ prime unless $q=127$. When $\Phi_n(2)$ is prime, checking the two norms in degrees $n/7$ and $n/q$ settles primitivity. [Proof and sharp example](results.pdf#page=316) · [Finite verifier](scripts/check_seven_position_orders.py)

- **More than 35.756% of degrees admit no primitive trinomial.** Even irreducible trinomials are impossible in more than 34.101% of all degrees and 47.742% of prime degrees, measured by lower asymptotic density. A five-term witness is necessary wherever a primitive trinomial is impossible. For more than 30.219% of primes $p$, every degree $p,p^3,p^5,\ldots$ has no irreducible trinomial. [Density proof](results.pdf#page=311) · [All odd powers of one prime](results.pdf#page=315) · [Density verifier](scripts/check_trinomial_density.py) · [Lean proof for dilations](GF2Sparse/Dilation.lean)

- **In degrees 28,759 and 28,771, every irreducible polynomial with fewer than 14,105 terms has an explicit prime of more than 8,600 digits in its root order.** The prime is $(2^{28759}-1)/226160777$ or $(2^{28771}-1)/104726441$, respectively. In either degree a single further power test decides primitivity. The weight cutoff is sharp in both. [Proof](results.pdf#page=314) · [Weight distributions](data/cyclotomic-weight-spectra.json) · [Verifier](scripts/check_cyclotomic_weights.py)

- **A primitive pentanomial in degree 33,511 is $X^{33511}+X^{32291}+X^{2440}+X^{1220}+1$.** Its root has order $2^{33511}-1$. We verified all 27 prime-index powers and the primality of every factor, including a 9,124-digit prime. The two primitive trinomials up to reciprocity have taps 1,318 and 1,920. All integer certificates are stored in the repository. [Proof](results.pdf#page=310) · [Order factorization](data/mers-project-large-orders.json) · [Primality certificates](data/mers-project-primality)

- **The census gives the minimum primitive weight in all 83 selected degrees from 3,537 through 41,521.** Forty-two admit primitive trinomials and 41 require pentanomials. In degree 35,737 the pentanomial with interior exponents 6,883, 14,427 and 21,310 attains the minimum. In degree 32,531 the minimum is attained by $X^{32531}+X^{29001}+X^{7060}+X^{3530}+1$. In degree 28,759 the two primitive trinomial taps up to reciprocity are 8,526 and 13,192. A primitive pentanomial there has interior exponents 468, 936 and 28,291. Five terms are necessary in degree 28,381, where the pentanomial with interior exponents 5,690, 11,380 and 22,691 is primitive. In degree 41,263 the three primitive trinomial taps up to reciprocity are 3,505, 8,787 and 13,968. A primitive pentanomial there has interior exponents 3,313, 6,626 and 37,950. These include degrees 25,243, 25,933 and 28,771, with interior exponents $(1330,2660,23913)$, $(4453,8906,21480)$ and $(407,814,28364)$, respectively. In degree 35,339 a primitive pentanomial is $X^{35339}+X^{33821}+X^{3036}+X^{1518}+1$. In degree 17,683 a primitive pentanomial has interior exponents 2,170, 4,340 and 15,513. In degree 17,698 both $X^{17698}+X^{511}+1$ and the pentanomial with interior exponents 783, 1,566 and 16,915 are primitive. [First 63 witnesses](data/mers-project-sparse-orders.json) · [Twenty larger witnesses](data/mers-project-large-orders.json) · [Degree 32,531 proof](results.pdf#page=347) · [Census proof](results.pdf#page=307)

- **All 530,119 trinomial reciprocal classes in the 83 selected Mers Project degrees are classified.** Exactly 136 are irreducible. Of those, 128 are primitive and eight have smaller order. In degree 41,521 all four irreducible pairs are primitive, with taps 1,866, 2,034, 4,102 and 13,716. The pentanomial with interior exponents 6,931, 13,862 and 34,590 is also primitive. Degrees 32,531 and 35,737 admit no irreducible trinomial. [Census](data/mers-project-trinomial-census.csv) · [Degree 35,737 certificate](results.pdf#page=310) · [Census proof](results.pdf#page=341) · [Degree 41,521 certificate](results.pdf#page=348)

- **Eight irreducible trinomial pairs in the census have smaller order than the field group.** In degree 29,473 the five primitive trinomial taps up to reciprocity are 1,879, 1,953, 5,404, 7,459 and 14,563. A primitive pentanomial there has interior exponents 5,476, 10,952 and 23,997. Degree 26,903 has one primitive pair with tap 7,044. In degree 4,809 the only irreducible taps are 91 and 931. Their roots have order $7(2^{687}-1)$. A primitive pentanomial has interior exponents 746, 1,119 and 3,690. [Complete tap lists](data/mers-project-trinomial-census.csv) · [Six smaller-degree exceptions](results.pdf#page=308) · [Two degree-33,511 exceptions](results.pdf#page=313)

- **In degrees 1,331, 3,993 and 6,655, 21 pentanomial pairs have root index one or greater than 182,931,247,071,233.** Three examples have interior exponents $(1,2,289)$, $(1,2,83)$ and $(1,2,1719)$, respectively. The first two primitivity checks reduce to the same 250-digit composite order in degree 1,331. The third also has a 1,427-digit composite to resolve. All 665 trinomial pairs in degree 1,331 are reducible, so a witness there requires five terms. [Order bounds and remaining tests](results.pdf#page=306) · [Polynomials and factors](data/degree-1331-order-projections.json) · [Verifier](scripts/check_1331_order_projections.py)

- **For an irreducible trinomial $X^n+X^k+1$, the degree and tap determine exactly which pairs of subfields can supply its root.** For distinct primes $p,q\mid n$, a root is a product from the subfields of degrees $n/p,n/q$ exactly when $\gcd(k,pq,2^{n/(pq)}-1)>1$. The criterion for arbitrary pairs uses only divisors of $n$. Direct powering agrees on all 2,327 pairs tested through degree 384. [Proof](results.pdf#page=301) · [Lean](GF2Sparse/SubfieldProducts.lean) · [Verifier](scripts/check_trinomial_subfield_pairs.py)

- **In every degree $n=3q^b$ with prime $q>3$, a three-term arithmetic progression in an irreducible pentanomial forces a prime-power divisor of its root order with binary multiplicative degree $n$.** The conclusion also holds in every degree $n=5q^b$ with prime $q>5$ for any three of five equally spaced positions. Outside $(p,q)=(3,7),(5,31)$ the divisor can be taken prime. The quadratic-residue code bound rules out the remaining class $q^b\equiv11\pmod{12}$. [Proof](results.pdf#page=300) · [Exact coefficient verifier](scripts/check_relative_fourier_minors.py)

- **For every fixed odd prime power $m=p^a$, all sufficiently large powers $q^b$ admit an exact subfield test.** Let $q>p$ be prime and $2q^b+1>(6m-5)^9$. An irreducible pentanomial of degree $n=mq^b$ containing three of $p$ equally spaced positions has a root in the product of the maximal subfields exactly when its exponents have a common divisor greater than one and $q\mid 2^{m/p}-1$. Every other such root has a prime power of binary multiplicative degree $n$ in its order. [Classification and example](results.pdf#page=304) · [Determinant argument](results.pdf#page=298) · [Four unrestricted columns](results.pdf#page=303)

- **In degree 17,029, the least weight of an irreducible that can miss the 5,118-digit prime in the field order is exactly 8,279.** Exactly two of the 24,598 irreducibles in the exceptional subgroup attain this weight. The minimum primitive weight is five, with witness $X^{17029}+X^{560}+X^2+X+1$. [Complete distribution and proof](results.pdf#page=296) · [Weight spectra](data/cyclotomic-weight-spectra.json) · [Order certificate](data/cyclotomic-order-witnesses.json)

- **Five terms are necessary in degrees 3,837, 5,509 and 8,371. Three suffice in degrees 5,785, 7,673, 20,591, 23,479 and 32,551.** In degree 7,673 the unique primitive trinomial up to reciprocation is $X^{7673}+X^{120}+1$. The eight primitive trinomial taps in the three highest degrees are listed in the research note. Each degree also has an explicit primitive pentanomial. [Witnesses and complete order factorizations](data/cyclotomic-order-witnesses.json) · [First five degrees](results.pdf#page=292) · [Three higher degrees](results.pdf#page=297)

- **All eight irreducible trinomial pairs in degree 3,073 pass the five known prime-index tests.** Their powers give 23 distinct pentanomial pairs with the same respective orders. Each root index is one or exceeds ten billion. For tap 1,023 a rational parametrization yields 9,145,564 split norm circles at $q=1024$. The 791-digit cofactor is composite, and full primitivity remains open. [Proof and tap list](results.pdf#page=293) · [Order verifier](scripts/check_3073_trinomials.py) · [Circle census](scripts/count_3073_circles.cpp)

- **An explicit periodic test for the same subfield obstruction also works in degrees $p^a q^b$ for every fixed $a$.** For $a=1$, every positive multiple $b$ of $\mathrm{lcm}_{3\le r\le p,\ r\text{ prime}}(r-1)$ works for all $q>p$, regardless of the size of $q^b$. [Proof](results.pdf#page=290) · [Congruence verifier](scripts/check_relative_progressions.py) · [Lean](GF2Sparse/ScalarOrderBound.lean)

- **In degrees 4,167, 6,925, 9,583 and 12,231 every irreducible pentanomial containing a three-term progression has a certified large prime in its root order.** Primitivity then reduces to testing the two maximal-subfield norms. For the explicit examples at 6,925 and 12,231 the root orders have certified divisors of 1,840 and 2,936 digits. Each remaining index is one or exceeds ten billion. The data reduce the two remaining order tests to explicit fields of degrees 1,385 and 4,077. [Proof and polynomials](results.pdf#page=288) · [Cofactors](data/relative-progression-witnesses.json) · [Verifier](scripts/check_relative_progression_witnesses.py)

- **For odd degrees with two distinct prime factors through 20,000, progression pentanomials that split into maximal subfields are classified.** Write $n=p^a q^b$ with $p<q$. An irreducible pentanomial containing a three-term progression has a split root exactly when its exponents share a divisor and $q$ divides $2^{n/(pq)}-1$. Testing the progression step and the difference of the other two exponents settles 3,235 of the 4,090 nonsquarefree degrees of this form through 100,000 directly. For all 562 nonsquarefree degrees through 10,000 the rule extends to any three of $p$ equally spaced positions. [Proof](results.pdf#page=286) · [Short triples and the two-power test](results.pdf#page=289) · [Degree sieve and census](scripts/check_relative_progressions.py)

- **Nine more degrees have certified minimum primitive weights.** Five terms are necessary in degrees 4,205, 5,325, 10,192, 17,917 and 24,853. In those degrees, $X^n+X^t+X^2+X+1$ is primitive for $t=216,1169,3159,1961,5045$, respectively. Three terms suffice in degrees 4,167, 7,135, 13,489 and 24,263, where 8,430 is the unique primitive trinomial tap up to reciprocity. Every trinomial tap up to reciprocity was checked. [Witnesses and factorizations](data/composite-order-witnesses.json) · [Proof and trinomial taps](results.pdf#page=285) · [Verifier](scripts/check_composite_orders.py)

- **Three exponents in arithmetic progression rule out every coprime-degree subfield split unless the degree is 2 modulo 4.** Every exception is $H_T(X^{3^a})$, where $T$ is an irreducible trinomial of odd degree $m$, $H_T$ is its quadratic twist, and $\gcd(3^a,m)=1$. Its exact root order is $3^{a+1}$ times the source order. This excludes all progression cases in degree 2,458. The step is arbitrary. In odd degree the same holds for $t,t+d,t+2^k d$ when $k$ is coprime to the degree. Three consecutive exponents also force a full-degree order component in every degree $p^a q^b$ for distinct odd primes, even when the two maximal subfields intersect. Explicit primitive examples include $X^{3375}+X^{491}+X^2+X+1$ and $X^{1233}+X^{43}+X^2+X+1$. [Proof](results.pdf#page=281) · [Classification for arbitrary exponent gcd](results.pdf#page=284) · [Order checks](scripts/check_progression_scalar_orders.py)

- **Three exponents inside any seven equally spaced positions exclude a coprime-degree subfield split in every odd degree.** The window grows to 23 positions when the degree is coprime to 6. More generally, for normalized support and three scaled positions $0,m,W$ whose differences are coprime to $2^n-1$, a split requires $5n<12W^3$. In odd semiprime degree these exclusions force a full-degree prime-power component. One primitive example is $X^{3415}+X^{36}+X^{27}+X^{18}+1$. [Proof of the three-position bound](results.pdf#page=283) · [Witness and gap tests](results.pdf#page=280)

- **For every prime $7\le p\le 10{,}000$ and every prime $q>p$, a sparse irreducible of degree $pq$ has a prime-power divisor of its root order with binary multiplicative degree $pq$.** The larger prime has no cutoff. An obstruction would require an additive pair in a subgroup of prime order between $3p^2/4$ and $12p^2/5$. Of the 96 candidate orders for odd $p$ through 10,000, only $7$ and $31$ allow a pair, at $p=3$ and $5$. For every larger composite partner coprime to $p$, the corresponding two-subfield product is also excluded when the support has gcd one. The theorem covers every Mersenne prime exponent $p\ge7$. [Counting proof](results.pdf#page=271) · [Exact finite test](scripts/check_scalar_order_bound.py)

- **For every coprime pair $13\le i\le1000$ and $j>i$, no root of a sparse irreducible of degree $ij$ with support of gcd one belongs to the product of those two subfields.** Checking 12,780 possible scalar orders leaves eight smaller degrees through 1,000 where a split still needs investigation, namely 2, 3, 4, 5, 6, 8, 9 and 12. When the degree is coprime to 30, descent removes the support-gcd restriction. Every coprime partition is thereby excluded through degree one million for degrees coprime to 30. A separate exhaustive check excludes every coprime split in every odd degree through 2,048, covering 6,226,592,338 possible supports. [Per-case counts](data/odd-scalar-splits-2048.csv) · [Proof and exact subgroup counts](results.pdf#page=277) · [Reproduce the calculation](scripts/check_coprime_scalar_orders.py)

- **The quadratic bound on the smaller component also holds when either subfield degree is even.** For coprime degrees $i,j>1$ and support of gcd one, a split root forces $3i^2/4\le A<12i^2/5$ on its plane side and $9i\le4j$, with the sole exception to the degree ratio at $(i,j)=(2,3)$. The exceptional pentanomials have root order 21. The same proof identifies two dyadic lifts with exact orders, including $3(2^{2047}-1)$ in degree 4,094 and $15(2^{22327}-1)$ in degree 89,308. [Proof](results.pdf#page=276) · [Lean arithmetic and outer-polynomial obstruction](GF2Sparse/ScalarOrderBound.lean)

- **The unique degree-3,415 trinomial up to reciprocal is primitive, with tap 1,272.** Its third, fifth and seventh powers give three primitive pentanomials. Across degrees 3,415, 5,403, 7,617, 12,365 and 13,045, an exhaustive test excludes all 8,650,503,360 possible split supports. Every sparse irreducible in these degrees carries a certified prime of 821, 1,084, 1,528, 2,977 and 3,141 digits, respectively. In the last four degrees the displayed pentanomials pass every known prime-index test, with one unresolved subfield cofactor in each degree. [Proof and orders](results.pdf#page=274) · [Certificates and supports](data/scalar-pair-products.json) · [Verifier](scripts/check_scalar_product_orders.py)

- **Degree 2,458 has 40 certified field generators in one quaternary projective orbit.** The other 20 elements have index three. The lightest primitive polynomial in this orbit has 1,161 terms. The pentanomial with taps 910, 971 and 1,229 passes all eight known prime tests. Its remaining index equals that of its norm in degree 1,229. [Order proof](results.pdf#page=273) · [Reproduce the field checks](scripts/check_2458_projective_orders.py)

- **Degree 22,327 has a primitive trinomial with tap 2445 and a primitive pentanomial with taps 815, 1630 and 2445.** Exactly 53 of the first 22,327 powers of a trinomial root have sparse minimal polynomial. Their odd exponent parts are 1, 3, 5 and 7. Every sparse irreducible in this degree has a 6,616-digit prime in its root order. [Proof and four primitive pentanomials](results.pdf#page=270) · [Certificates](data/semiprime-scalar-norms.json)

- **In ten semiprime degrees, a certified large prime divides every sparse irreducible root order.** The minimum primitive weight is five in degrees 1,727, 1,781, 5,053, 11,581 and 14,971, and three in 2,353, 3,817, 8,033, 10,967 and 14,263. In degree 14,971 the only possible scalar order leads to 120,050 supports. The largest relevant polynomial gcd has degree 16, excluding a required degree-1,361 factor. [Eight degrees and tap lists](results.pdf#page=268) · [Degrees 5,053 and 14,263](results.pdf#page=266) · [Norm records and primality certificate sources](data/semiprime-scalar-norms.json) · [Pair census](scripts/check_scalar_pairs.cpp)

- **Four nearby exponents restrict root orders in every degree.** If the support has gcd one, four exponents span $T$, and $4T<3s^2$ for the smallest prime $s$ dividing the degree, a root cannot be a product from two coprime proper subfields whose degrees multiply to the full degree. In degree $pq$ this forces a full-degree prime power for arbitrarily separated primes. A separate norm-one argument in degree $2kd$ forces every support exponent to be divisible by $k$. [Proofs and hypotheses](results.pdf#page=267) · [Lean lemmas](GF2Sparse/SubfieldProducts.lean)

- **Every sparse irreducible of degree $pq$ has a full-degree prime-power factor in its root order whenever $4q\le9p$.** This holds for all odd primes $p<q$. In a hypothetical product of proper subfield elements, a class pattern of $3,1,1$ makes the polynomial vanish in a proper subfield. The remaining pattern forces the smaller component order to lie between $3p^2/4$ and $pq/3$. [Proof and norm criterion](results.pdf#page=264) · [Lean tensor argument](GF2Sparse/SubfieldProducts.lean)

- **Every sparse irreducible in degrees 1,637, 3,359 and 4,243 has a large certified prime in its root order.** The conclusion holds for all six binary fractional linear images of its root at weights below 733, 1,649 and 2,029, respectively. For the root itself the exact thresholds are 737, 1,683 and 2,029. The census multiplies all exceptional factors and their translates to verify both lists. [Proof](results.pdf#page=263) · [Weight distributions](data/cyclotomic-weight-spectra.json) · [Verifier](scripts/check_cyclotomic_weights.py)

- **Thirteen additional composite degrees have certified primitive pentanomials.** In degree $16{,}129=127^2$, the only primitive trinomial taps up to reciprocity are 79 and 7,575. The minimum weight is also three in degrees 3,481 and 4,913, and five in the other ten, including 15,856. In degree 3,481 a 1,031-digit prime divides the root order of every irreducible, so primitivity reduces to a norm test in degree 59. [Lean proof of the norm criterion](GF2Sparse/PartialOrder.lean) · [Witnesses and order factorizations](data/composite-order-witnesses.json) · [ECPP archive](data/composite-order-prime-certificates.json.gz) · [Degree-16,129 certificate](data/degree-16129-primality.cert.gz) · [Proof](results.pdf#page=260)

- **For $k=141$ and $191$, the prime $2^k+5$ divides the root order of the degree-$2^k+4$ pentanomial exactly once. The exact powers of three in those orders are 9 and 243.** The conductor-prime test uses binary quadratic forms and agrees with direct powering at all 125 eligible primes through 2,053. The powers of three follow unconditionally from two certified imaginary quadratic class numbers. [Conductor-prime proof](results.pdf#page=253) · [Powers of three](results.pdf#page=257) · [Class-number verifier](scripts/check_twisted_three_class.py)

- **A ray class group gives a full-order criterion for the twisted cyclotomic family.** For a prime $p\ge5$ with $-2$ primitive modulo $p$, choose $2^j\equiv\pm3\bmod p$. A root of $D_p$ is primitive exactly when $\gcd(2^{(p-1)/2}-1,2^j-3)=1$ and Frobenius minus two maps the ordinary ray class group modulo two of $\mathbb Q(\zeta_{3p})^+$ onto itself. Individual primes can be tested in smaller subfields. A cubic field detects the factor seven in the root-order index of the degree-2,052 pentanomial. Direct powering agrees in 325 root tests and 195 Gauss period tests across 253 ray groups. [Proof](results.pdf#page=247) · [Certified computations](scripts/check_twisted_ray.py)

- **The minimum weight in degree 3,927 is three.** Of the 1,963 reciprocal pairs of trinomials, ten are irreducible and five are primitive. The smallest tap giving full order is 367. Cubing the five primitive trinomial roots gives five pentanomial pairs, and $X^{3927}+X^{113}+X^{101}+X^{12}+1$ is another primitive pentanomial. The order tests use all 29 prime divisors of $2^{3927}-1$. [Proof and exact orders](results.pdf#page=245) · [Reproduce the certificates](scripts/check_3927_thirds.py)

- **Lean certifies five-term irreducibles in degrees $2^{141}+4$ and $2^{191}+4$.** For odd $k\ge3$, the polynomial $X^{2^k+4}+X^{2^k+1}+X^{2^k}+X^5+1$ is irreducible exactly when $2^k+5$ is prime and $-2$ has full order modulo that prime. At $k=191$ the base-two logarithm of its root order is at least $137227202865029797602485611882$ by counting products of conjugates in two subgroups. The full multiplicative orders of these two roots remain open. Across $20<n\le 2^{191}+4$, just five candidates up to reciprocity remain for a primitive polynomial of weight at most five with a nonidentity binary projective symmetry of its roots. [Irreducibility proof](results.pdf#page=241) · [Order bound](results.pdf#page=255) · [Lean certificates](GF2Sparse/TwistedCyclotomic.lean) · [Reproduce the order and factor checks](scripts/check_translation_lift_orders.py)

- **Two imaginary quadratic forms test whether a twisted cyclotomic root is a cube.** For $p\equiv5\pmod8$ with two primitive modulo $p$, let $h=h(-3p)$ and let $t$ be the order of the prime above two. Three divides the root-order index exactly when $3\mid h/t$ or the lifted form of discriminant $-27p$ becomes principal after raising it to $t$. The test agrees with the real quadratic class number at all 2,399 primes congruent to five modulo eight through 100,000. In the five-term family, every odd exponent strictly between 191 and 16,541 gives a reducible polynomial. [Imaginary quadratic test](results.pdf#page=261) · [Real quadratic criterion](results.pdf#page=244) · [Excluded exponents](results.pdf#page=246) · [Verifier](scripts/check_twisted_cubic.py)

- **The minimum weight is five in ten additional prime degrees and three in seven others.** One example is $X^{4507}+X^{4313}+X^{388}+X^{194}+1$. The search checked all 35,566 reciprocal classes of trinomials in the seventeen degrees from 3467 to 5087. Exactly fifteen classes are irreducible, and all fifteen are primitive. Each of the seventeen degrees also has a certified pentanomial. [Five-term witnesses](data/complementary-prime-degrees-3467-5087.csv) · [Trinomial census](data/prime-degree-trinomial-census.csv) · [Proof](results.pdf#page=236)
- **Quadratic rational maps of optimal normal basis generators give two further degrees, 23 and 30.** The same map $(T+1)/T^2$ produces primitive pentanomials in both. Across all 24 quadratic maps, the only target degrees above one admitting a primitive polynomial with at most five terms are 2, 3, 4, 5, 6, 9, 11, 23 and 30. For any fixed rational map the paper gives a finite procedure to decide which period indices meet a prescribed term bound. [Proof](results.pdf#page=239) · [Exhaustive verifier](scripts/check_quadratic_period_images.py) · [Lean witnesses](GF2Sparse/GaussPeriodWeights.lean)
- **Optimal normal bases yield primitive polynomials with at most five terms only in degrees 2, 3, 4, 5, 6, 9 and 11 among degrees above one.** This includes all six binary fractional linear changes of a basis generator. For any five-term irreducible of prime degree $n\ge13$, writing a projective image of its root as $z+z^{-1}$ requires $z$ to have order at least $6n+1$. The proof gives a sharp coefficient bound for the full sequence of reciprocal period polynomials. [Proof](results.pdf#page=237) · [Lean weight bound](GF2Sparse/GaussPeriodWeights.lean) · [Finite classification](scripts/check_gauss_period_weights.py)
- **The minimum weight in degree 216,091 is five.** The polynomial $X^{216091}+X^{68}+X^{26}+X^{13}+1$ is primitive. A second primitive pentanomial is $X^{216091}+X^{130}+X^{10}+X^3+1$. Lucas–Lehmer and full polynomial powering certify both orders. With the earlier results, the five-term bound now holds at all of the first 33 Mersenne prime exponents, through 859,433. The last two degrees use published primitive trinomial seeds. [Witnesses](data/mersenne-exponent-prefix.json) · [Verification](scripts/check_large_circle_orders.py) · [Proof](results.pdf#page=233)
- **Powers of the 32 almost primitive trinomials tabulated by Brent and Zimmermann give five-term images only in degrees 8 and 13.** This checks every power through the source factor degree and all six binary fractional linear transformations, including at degrees 216,091, 1,257,787 and 2,976,221. A general bound shows that for a trinomial with a cofactor of degree $\delta$, the degree-$n$ factor after taking an odd power $m$ still has at least $\lceil(n+\delta)/(m\delta)\rceil$ terms. [Proof](results.pdf#page=234) · [Source cases and counts](data/almost-trinomial-power-windows.csv) · [Verifier](scripts/check_almost_trinomial_powers.py)
- **There are 242 explicit primitive pentanomials in thirteen large degrees from 110,503 to 74,207,281.** They exhaust the five-term minimal polynomials obtained by raising primitive trinomial roots to powers through the degree in those thirteen cases. One example is $X^{74207281}+X^{9999621}+X^{9411408}+X^{588213}+1$. The seven positive trinomial seeds and all 121,268 other reciprocal pairs in degrees 110,503 and 132,049 were independently checked. The larger cases use published trinomial searches. [242 witnesses](data/large-mersenne-sampled-pentanomials.csv) · [Proof](results.pdf#page=232) · [Lean transfer](GF2Sparse/LargeTrinomialSamples.lean) · [Published seed certificates](https://maths-people.anu.edu.au/brent/trinom.html)
- **A second degree-4112 family gives 4,208,864 primitive elements, and every full-degree member has at least 97 terms in its binary minimal polynomial.** These are the translates of $y^j+y^{-j}$ by the 65,536 constants. A circle or line reduces each quadratic order calculation to known logarithms. Across all 4,080 constant orbits the leading 257 binary coefficients contain at least 96 ones. [Reduction and weight proof](results.pdf#page=231) · [Census and weight checker](scripts/check_4112_trace_translates.py)
- **In degree 4112, exact order tests certify 8,392,592 primitive elements among 16,777,216 binomials in the torsion coordinate.** Of the whole family, 16,711,168 generate the component of order equal to the remaining 539-digit cofactor. The 2,048 stored logarithms also determine this component for every product or quotient of the binomials. Their binary minimal polynomials have at least seven terms whenever they are primitive. [Logarithms](data/degree-4112-binomial-logs.csv.gz) · [Power verifier](scripts/check_4112_binomials.py) · [Reconstruction](scripts/solve_4112_binomials.py)
- **The degree-4112 five-term candidate now has an explicit logarithm descent.** Its root is encoded in the same field as the certified primitive polynomial. Multiplication by a subfield element leaves its unresolved order component unchanged and gives a polynomial of relative degree 129. Fifty-one verified identities reduce the remaining logarithms to 568 factors of relative degrees two through nine. The checker exports individual factors and verifies contributed logarithms by direct powering. [Field coordinates and factorizations](data/degree-4112-subfield-descent.json) · [Direct checker](scripts/check_4112_descent.py)
- **Degree 4112 has a certified eleven-term primitive polynomial and a five-term candidate with a 2,322-bit proven order divisor.** The eleven-term polynomial is $P(X^{257}+X)$ for $P(T)=T^{16}+T^6+T^4+T+1$. Its full order follows from 129 directly verified power identities and four small-prime tests. The pentanomial $X^{4112}+X^{23}+X^{12}+X+1$ passes all 23 known prime-index tests. One scalar modulo a 539-digit cofactor would finish its certificate. A general obstruction shows why projective Frobenius alone cannot produce the five-term witness in this degree. [Full-order proof](results.pdf#page=227) · [Pentanomial reduction and obstruction](results.pdf#page=228) · [129 exponents](data/degree-4112-projective-logs.csv.gz) · [Five-term target](data/degree-4112-pentanomial-target.json)
- **Twenty more degrees between 3464 and 4032 have certified primitive pentanomials.** For example, $X^{4032}+X^{2955}+X^{1077}+X^{92}+1$ has order $2^{4032}-1$ at each root. Together with the earlier certificates this covers at least 2,655 of the first 10,351 positive degrees. All five additions are multiples of eight, where Swan’s theorem rules out trinomials. The twenty certificates check 869 prime-index powers. [Witnesses](data/complementary-width-cyclotomic.csv) · [Complete order factors](data/mersenne-complementary-cyclotomic.json) · [Primality certificates](data/mersenne-cyclotomic-prime-certificates.json.gz)
- **Sixty-nine additional composite degrees have certified primitive pentanomials, up to degree 10,351.** The largest is $X^{10351}+X^{9810}+X^{1082}+X^{541}+1$. The table includes 9583, 9757 and 9985. Together with earlier witnesses it covers at least 2,635 of the first 10,351 positive degrees. [Witnesses](data/complementary-width-extra.csv) · [Complete factorizations](data/mersenne-complementary-width-extra.json) · [Primality certificates](data/mersenne-complementary-width-prime-certificates.json.gz) · [Verification](results.pdf#page=225)
- **Every fixed bound on the spacing of the three interior terms eventually fails, even after rescaling by any unit modulo the degree.** In infinitely many degrees, any primitive five-term witness needs a span of at least a constant times $\sqrt{\log n}$ under every such rescaling. Every multiple of 21,853,877,362,864,135,364,080,305 excludes all complementary shapes of normalized width at most 18. [Proof](results.pdf#page=226) · [Lean factor theorem](GF2Sparse/AffineTapSpan.lean) · [Compute the exact moduli](scripts/check_affine_tap_span.py)
- **A normalized tap bound of 18 suffices for primitive pentanomials in 1,756 degrees.** This covers every degree from 5 through 1228 and every even degree from 1230 through 2292. Exactly two degrees, 1320 and 1380, need 18. Exhausting every smaller tap pair leaves just 3 and 10 irreducibles respectively, all of proper order. [Proof](results.pdf#page=224) · [First witness table](data/complementary-width-5-1228.csv) · [Even-degree table](data/complementary-width-1230-2292.csv) · [Sharpness check](scripts/check_complementary_width.py)
- **In degree 9583 a 2,406-digit prime divides the root order of every irreducible polynomial with quotient bound $K<37$.** Primitivity for this class reduces to two norm tests in degrees 259 and 1369. In degree 3415, the same argument forces an 821-digit prime and reduces the tests to degrees 5 and 683. The proof applies to arbitrary degrees with two suitable prime divisors. [General theorem](results.pdf#page=223) · [Norm certificates](data/two-subfield-norms.json) · [Norm checker](scripts/check_two_subfield_norms.py)
- **A formula in every sufficiently large degree gives five terms, an increasing factor cutoff and a nearly quadratic period.** For any $B\ge2$, put $L=\mathrm{lcm}_{1\le i\le B}(2^i-1)$. In every degree $n\ge64(L+1)$ the formula gives a squarefree pentanomial with an odd number of irreducible factors, each of degree greater than $B$, and period $H\ge1+n(n-1)/(14L+2)$. Taking $B\to\infty$ with $B=o(\sqrt{\log n})$ gives $n^{1-o(1)}$ distinct choices of period at least $n^{2-o(1)}$. Six members have certified full order, including $X^{4224}+X^8+X^3+X^2+1$. [Proof](results.pdf#page=222) · [Construct a candidate and replay the six certificates](scripts/check_uniform_period.py)
- **In every sufficiently large even degree $n$, a five-term polynomial passes the degree-16 factor sieve and has period $H\ge 1+n(n-1)/39$.** It is squarefree, has coprime exponents and has an odd number of irreducible factors. The constant 39 is sharp for the normalized tap bound used in the proof. If the candidate is irreducible in degree $2^h p^e$ with prime $p>39$ and $p\nmid 2^{2^{h-1}}+1$, its root order contains a prime of full binary degree. [Uniform construction and sharpness](results.pdf#page=220) · [Order consequence](results.pdf#page=221) · [Finite sieve](scripts/check_complementary_taps.py) · [Lean factor certificates](GF2Sparse/ReciprocalSieve.lean)
- **Three more degrees have explicit primitive pentanomials with complementary taps.** The degrees are 19,937, 21,701 and 23,209. Separate witnesses in degrees 5,234, 21,002 and 24,782 generate the entire subgroup of order $2^{n/2}+1$ after raising a root to $2^{n/2}-1$. Their remaining full-group indices divide specified cofactors. The verifier replays Lucas–Lehmer, integer primality certificates, irreducibility and the relevant order tests. [Six witnesses and proofs](results.pdf#page=219) · [Full-order supports](data/large-mersenne-complementary-taps.json) · [Relative-order certificates](data/large-quadratic-circle-orders.json) · [Verifier](scripts/check_large_circle_orders.py)
- **A 3,161-digit prime divides the root order of every irreducible trinomial and pentanomial in degree 21,002.** The prime is $(2^{10501}+1)/3$. More generally, for every prime $p>7$, the proof identifies exactly which irreducible pentanomials in degrees $2p$ and $4p$ can miss all primes of full binary degree. Every irreducible pentanomial with two interior taps summing to its degree passes this test. [Classification](results.pdf#page=217) · [Order consequence](results.pdf#page=218) · [Independent field checks](scripts/check_circle_power_degrees.py) · [Primality of the order divisor](https://arxiv.org/html/2605.18555v1#S4.SS3)
- **Logarithmic spacing suffices to pass the parity and small-factor tests in every sufficiently large even degree.** Some $X^n+X^{n-b}+X^a+X^b+1$ with even $b=O(\log n)$ has coprime exponents, an odd number of factors and no factor of degree at most 16. Along an infinite sequence of degrees, even spacing of order $\log n$ is already necessary to pass these tests through degree four. For degrees divisible by eight, a positive fraction of the candidate pairs pass through degree 16. The proof leaves irreducibility and full order open. [Proof and finite calculation](results.pdf#page=215) · [Reproduce the 49,152 cases](scripts/check_complementary_taps.py) · [Lean divisibility lemmas](GF2Sparse/ReciprocalSieve.lean)
- **The factor-parity test has an exact solution for all even complementary taps.** In degree $n$ divisible by eight, the number of reciprocal pairs with coprime exponents that pass the test is asymptotic to $\varphi(n/2)\log(n/2)$. A formula lists them directly. Of the first 286 multiples of eight, exactly 268 have a primitive member with even spacing. The other 18 all have a certified example with odd spacing. [Discriminant proof](results.pdf#page=213) · [Candidate list and count](results.pdf#page=214) · [Witnesses](data/symmetric-witnesses-multiples-of-eight-through-2288.csv) · [Census checker](scripts/check_complementary_taps.py)
- **Thirteen tap spacings suffice in 1,756 degrees, and degree 2040 needs the thirteenth.** Every degree from 5 through 1228 and every even degree from 1230 through 2292 has a certified primitive $X^n+X^{n-b}+X^a+X^b+1$ with $b\le13$. In 1,113 of the archived witnesses $b=1$. In degree 2040, all eleven irreducibles with $b\le12$ and coprime exponents have proper order, while $X^{2040}+X^{2027}+X^{13}+X^8+1$ is primitive. [Degrees 5–1228](data/symmetric-witnesses-5-1228.csv) · [Even degrees 1230–2292](data/symmetric-witnesses-1230-2292.csv) · [Exhaustive check](scripts/check_complementary_taps.py)
- **Five additional degrees have certified primitive pentanomials with complementary taps.** The degrees are 7854, 8680, 8712, 8840 and 9576. In the largest, $X^{9576}+X^{9566}+X^{4555}+X^{10}+1$ has order $2^{9576}-1$ at each root. NTL found the examples and FLINT independently checked all five full orders. The repository now covers at least 2,564 of the first 9,576 degrees. [Five witnesses](data/symmetric-witnesses-above-7560.csv) · [Order factors](data/mersenne-symmetric-above-7560.json) · [Verification](results.pdf#page=212)
- **Four fixed exponents suffice to pass the factor-parity test in every even degree $n\ge6$.** For $X^n+X^{n-2}+X^a+X^2+1$ the proof specifies exactly which odd $a$ give an odd number of irreducible factors. When $8\mid n$, only $a=n/2\pm1$ pass. Among the 1,500 multiples of eight through 12,000, this family gives primitive reciprocal pairs in exactly three degrees, 8, 112 and 1968. [All-even formula](results.pdf#page=211) · [Order checks and census](scripts/check_progression_factor_parity.py)
- **In every degree $n\ge12$ congruent to four modulo eight, all $n/2$ odd choices of $a$ make $X^n+X^{n-4}+X^a+X^4+1$ squarefree with an odd number of irreducible factors.** The general construction allows other fixed exponents and can simultaneously exclude every factor of any prescribed bounded degree on an infinite progression. Two verified primitive members have degrees 5964 and 6300. In every positive multiple of 2520, a primitive five-term binary polynomial must have at least six terms in each factor over $\mathbb F_4$. The degree-7560 example has 2,831 in each. [Parity theorem](results.pdf#page=209) · [Multiples of 2520](results.pdf#page=210) · [Verify the examples](scripts/check_progression_factor_parity.py)
- **In even degrees above 16, exactly two families can give a primitive binary polynomial and a factor over $\mathbb F_4$ both having at most five terms.** This cuts the search in each degree to a linear number of candidates. In degree 2458 only one of the 2,558 reciprocal classes is irreducible. The norm of its root down to degree 1229 has a minimal polynomial with 631 terms, ruling out this construction for a degree-1229 pentanomial. [Classification](results.pdf#page=207) · [Degree-1229 consequence](results.pdf#page=208) · [Exact enumeration](scripts/check_quaternary_norm_shapes.py)
- **In degree 1229, over 99.9% of the four-test survivors with at most 319 terms are primitive when their interior terms lie in any chosen window of 680 positions.** The bound holds for the ordinary count in each window, which has more than $2^{627}$ survivors. At a cutoff of 325 terms the failure fraction is below one in 100,000. The five-term case remains open. In every sufficiently large degree, a family with at most $0.219245n$ terms contains at least $2^{0.5438n}$ irreducibles and has primitive fraction at least $\varphi(2^n-1)/(2^n-1)-1/n^2$ among them. [Proof](results.pdf#page=197) · [Exact density bounds](scripts/check_1229_weight_density.py) · [Lean arithmetic](GF2Sparse/SelbergWeight.lean)
- **The $0.219245n$ weight bound still holds when a primitive root and its inverse must both generate normal bases.** In every sufficiently large degree, at least $2^{0.5438n}$ polynomials satisfy that weight bound with all six binary fractional linear images of a root primitive. Three specified images are normal, and all six are normal in even degree. Degree 44 is the first even degree above two where a five-term polynomial meets all six conditions of each kind. [Counting proof](results.pdf#page=193) · [Finite examples and checker](scripts/check_endpoint_normality.py)
- **In every degree congruent to 29 modulo 40, five terms cannot give an irreducible polynomial whose root and inverse both generate normal bases.** In degree 1229, exactly 1,203 irreducible pentanomials have a normal root and each passes the four known prime-index tests. Seven terms are necessary and sufficient for irreducibility with both normality properties. The example is $X^{1229}+X^{1228}+X^{12}+X^{11}+X^8+X+1$. Its full order is open. [Proof](results.pdf#page=192) · [Lean exclusion](GF2Sparse/Trinomial1229.lean) · [Independent checker](scripts/check_endpoint_normality.py)
- **Four primitive trinomials and eight primitive pentanomials in degree 2047.** The roots of $X^{2047}+X^{511}+1$ have order $2^{2047}-1$. A trace power gives $X^{2047}+X^3+1$, reciprocation gives two more trinomials, and cubes and fifth powers give eight pentanomials, including $X^{2047}+X^3+X^2+X+1$. The certificate uses 67,087 distinct polynomial logarithms. A CPU can verify the full order while leaving a 549-digit cofactor unfactored. [Proof](results.pdf#page=172) · [Twelve witnesses](data/degree-2047-sparse-witnesses.csv) · [CPU verification](#verify-degree-2047) · [Rank certificates](data/degree-2047-ore-rank.json) · [Lean algebra and arithmetic](GF2Sparse/OreCircle2047.lean)
- **The root order of an explicit five-term polynomial in degree $n=2^{84}+2$ exceeds $2^{10{,}134{,}308{,}948{,}149}$.** The polynomial is $X^n+X^{n-2}+X^3+X+1$. At degree 262,146 the same construction gives an irreducible pentanomial with root order above $2^{1387}$. Its proof encodes distinct field elements as quotients of elliptic functions of bounded degree. Across this family, whenever $4^k+3$ is prime with primitive root 2, the logarithm base two of the root order is at least $(2.7819-o(1))\sqrt n$. The exact 3-part is nine. Full order in the two displayed degrees remains open. [Counting proof](results.pdf#page=349) · [Exact integer counts](scripts/check_elliptic_quotient_counts.py) · [Lean arithmetic](GF2Sparse/EllipticPentanomial.lean) · [Fu–Li–Zuo](https://arxiv.org/abs/2611.34282)
- **The degree-4098 elliptic pentanomial passes all fourteen known prime-order tests.** Its root projects onto the full group of order $2^{2049}+1$, and its norm to degree 683 is primitive. Full order is equivalent to one explicit cubic-field element having order $(2^{1366}+2^{683}+1)/7$, a 411-digit composite. The cubic needs only arithmetic over the supplied degree-683 field. [Cubic and proof](results.pdf#page=181) · [Field polynomials and factors](data/degree-4098-elliptic-norm.json) · [Run the order checks](scripts/check_4098_elliptic_norm.py)
- **Six auxiliary degrees give a factorization-free primitivity test in every degree $n\ge24$.** Choose $d$ least with $n\le2^{d+1}+2$. For each $k$ from $2d-5$ through $2d$, retain the binary minimal polynomials of any 99.95% of the elements of $\mathbb F_{2^k}$. At any degree-$n$ element $a$, the values $P(a)$ of those polynomials generate the entire multiplicative group. Showing they are powers of a sparse root proves it primitive. With complete coverage, five auxiliary degrees suffice in odd degree and three in prime degree. [Six-degree proof](results.pdf#page=191) · [Three- and five-degree bounds](results.pdf#page=176) · [Exact checker](scripts/check_factor_field_index.py) · [Lean inequalities](GF2Sparse/FactorFieldIndex.lean)
- **Two constant fields give a linear index bound in every degree $n\ge24$.** Let $d$ be least with $n\le2^{d+1}+2$ and put $q=2^{d-1}$. For any degree-$n$ element $a$, the values $P(a)$ for irreducibles of degrees dividing $2d-2$ or $2d$ generate a subgroup of index at most $83q$. If those values are powers of a candidate root, at most six prime-index tests suffice in prime degree. In degree 1229 the list contains only 36,871. [Proof](results.pdf#page=175) · [Exact checker](scripts/check_factor_field_index.py) · [Lean arithmetic and sieve](GF2Sparse/FactorFieldIndex.lean)
- **A uniform order bound for sparse Ore lifts.** If a primitive binary seed has degree $s\ge40$, every root of its lift of degree $n=2^s-1$ has order greater than $2^{5\sqrt{n+1}}$. A three- or five-term seed gives a lift with the same number of terms. [Proof](results.pdf#page=168) · [Integer certificate](scripts/check_ore_uniform_order.py)
- **Explicit logarithms at roots of irreducible Ore lifts.** Logarithms in the seed field determine products of binary irreducibles with prescribed Frobenius annihilator. For each of two degree-2047 trinomials, Lean and direct powering verify 47 identities through factor degree 31, including 38 individual irreducibles. Counting reduced fractions through degree 1023 gives an order bound above $2^{218}$ for every primitive degree-11 seed. [Proof](results.pdf#page=167) · [Lean certificate](GF2Sparse/OreClassLogs2047.lean) · [Reproduce the logarithms and bounds](scripts/check_ore_logarithms.py)
- **Midpoint powers of primitive trinomials have an exact weight formula.** If one of $0,a,n$ is the midpoint of the other two modulo the odd part $m>1$ of the power, then for $m\le n$ the weight is two plus the $m$th term of Stern's diatomic sequence. For $m>n>7$ there are exactly two sparse images up to reciprocation. The degree-11 trinomial with tap 2 gives a primitive pentanomial at power 13, and the degree-28 trinomial with tap 3 gives one at power 31. [Proof](results.pdf#page=164) · [Lean trace and weight identities](GF2Sparse/SternPowers.lean) · [Check the finite enumeration](scripts/check_trinomial_decimations.py)
- **All powers up to the degree of a primitive trinomial are classified.** For degree $n>7$, strip powers of two from the exponent to obtain $m\le n$. The image is a trinomial for $m=1$. It has five terms precisely when $m=2^k+1$ and two source exponents agree modulo $m$, or when $m=5,7$ and the three distinct residues have a midpoint. Every other image has at least seven terms. At degree 153 all 612 root powers of the four primitive trinomials give exactly sixteen distinct primitive pentanomials. [Proof and exact count](results.pdf#page=160) · [Lean multiplicity and injectivity lemmas](GF2Sparse/TrinomialPowers.lean) · [Independent matrix check with --all-powers](scripts/check_trinomial_decimations.py)
- **In degree 153, four primitive trinomials give sixteen distinct primitive pentanomials.** More generally, in odd degree $n>11$, each divisor of $n$ of the form $2^k+1$ with $k\ge3$ gives one more distinct pentanomial per primitive trinomial, in addition to the third- and fifth-power images. Choosing several such divisors gives an explicit progression of degrees for any prescribed multiplier. [Counting theorem](results.pdf#page=158) · [Lean construction](GF2Sparse/TrinomialPowers.lean) · [Verify or explore a degree](scripts/check_trinomial_decimations.py)
- **Ten additional verified primitive pentanomials bring the total to at least 2,559 of the first 7,560 degrees.** In degree 7560, $X^{7560}+X^{121}+X^{107}+X^{14}+1$ has full order. The ten certificates use 664 distinct primes and 999 prime-index tests. [Witnesses](data/product-witnesses-4224-7560-extra.csv) · [Complete factorizations](data/mersenne-4224-7560-extra.json) · [Proof](results.pdf#page=209)
- **Every degree congruent to four modulo eight through 4580 has a verified primitive polynomial with at most five terms.** The new table gives 122 primitive pentanomials from degree 4100 through 5964, bringing the project total to at least 2,549 of the first 5,964 degrees. One example is $X^{5964}+X^{127}+X^{80}+X^{47}+1$. [Proof](results.pdf#page=199) · [122 witnesses](data/product-witnesses-4097-5964.csv) · [Full order factorizations](data/mersenne-4097-5964.json)
- **At least 2,425 of the first 4,096 degrees have a verified primitive polynomial with at most five terms.** The latest 81 degrees include every degree congruent to four modulo eight from 3460 through 4092, and degree 4096. Seroussi's $X^{4096}+X^{27}+X^{15}+X+1$ has full order and is the only irreducible pentanomial in that degree with all interior exponents at most 27. A second primitive example is $X^{4096}+X^{153}+X^{135}+X^{18}+1$. [Proof](results.pdf#page=189) · [81 product witnesses](data/product-witnesses-3457-4096.csv) · [Order factorizations](data/mersenne-3457-4096.json) · [Degree-4096 tap verifier](scripts/check_4096_small_taps.py) · [Previous 58 witnesses](data/product-witnesses-3201-3456.csv)
- **There is one family of primitive pentanomials whose roots can still have sparse seventh powers above degree 25.** Up to translation the exponents must be $0,2u,3u,4u,t$ with $7\mid u+2t$. This reduces degree 1229 to 176 supports and two irreducible sources. Across all primitive sources, three successive sparse polynomials can occur under seventh powering only through degree 10. The sharp cutoff for fifth powering is degree 13. In degrees divisible by seven above 14, even a single sparse seventh-power step is impossible for a primitive sparse source. [Proof and examples](results.pdf#page=155) · [Classify seventh powers or list one degree](scripts/check_seventh_power_supports.py)
- **Exactly 72 primitive pentanomials have a root whose fifth power still has a minimal polynomial with at most five terms.** The largest degree is 25, where the two sources are reciprocals. In every larger degree, among primitive trinomials and pentanomials only trinomials give a sparse fifth power. Their twenty-fifth powers have more than five terms. [Proof](results.pdf#page=154) · [Complete enumeration](scripts/check_fifth_power_chains.py) · [Lean certificate for degree 25](GF2Sparse/FifthImage.lean)
- **Every odd degree above seven has at least twice as many primitive pentanomials as primitive trinomials.** Cubing and fifth powering give disjoint sets. Seventh powering can add a third set, with an exact count from the source exponents modulo seven. The six primitive trinomials in degree 17 produce sixteen distinct primitive pentanomials. [Proof](results.pdf#page=152) · [Lean power formulas and a nine-term exception](GF2Sparse/TrinomialPowers.lean) · [Check the disjointness and small degrees](scripts/check_trinomial_decimations.py)
- **Four degree-1229 pentanomials have exactly the same root order.** If $r$ is a root of the polynomial with interior exponents $(166,249,332)$, then $r^7$ is a root of the one with exponents $(332,726,1089)$. These two polynomials and their reciprocals are irreducible. One verified logarithm gives their common index, which is still unknown. It also splits into six factor logarithms of degrees 5, 7, 9, 11, 19, and 21 over $\mathbb F_{2^{20}}$. Among all 639,166 irreducible pentanomials only the first and its reciprocal have a five-term seventh-power image. The same construction gives a proved primitive pair in degree 16. [Proof](results.pdf#page=151) · [Lean theorem](GF2Sparse/SeventhImage.lean) · [Degree-1229 certificate](GF2Sparse/SparseRootModels.lean) · [Census and logarithm task](scripts/check_1229_power_images.py)
- **A fixed Frobenius bidegree can cover only logarithmically many degrees through $X$.** This holds for primitive binary polynomials of every weight when their original terms are rewritten in a root coordinate and its Frobenius conjugate. For each fixed $\varepsilon>0$, the degrees permitting both variables to have degree at most $n^{1/2-\varepsilon}$ have density zero. Writing each exponent in base $2^s$ gives a side length below $2\sqrt n$ for every degree. [Proof](results.pdf#page=150) · [Lean proof of the area bound](GF2Sparse/FrobeniusBoxes.lean)
- **Exactly one reciprocal pair in degree 1229 admits an elliptic model of degree at most 20 for a root and its Frobenius power.** Among the four tested field sizes, $q=1024,2048$ both work for $X^{1229}+X^{819}+X^{683}+X^{136}+1$ and its reciprocal. The two functions have degrees 9 and 13 for $q=2048$. The same curve gives an explicit family with a proved primitive first member, $X^{77}+X^{51}+X^{43}+X^8+1$. The degree-1229 pair passes all four known prime-order tests. Seven explicit logarithms determine its remaining index. [Seven-logarithm certificate](data/degree-1229-elliptic-split-seven.json) · [Proof and classification](results.pdf#page=180) · [Reproduce the census](scripts/check_1229_frobenius_curves.py) · [Lean formulas and primitive degree 77](GF2Sparse/EllipticFrobenius.lean) · [Degree-1229 order checks](GF2Sparse/SparseRootModels.lean)
- **The rational parametrization used in degree 2047 faces a genus obstruction in degree 1229.** For all 639,166 irreducible pentanomials and $q=256,512,1024,2048$, a sparse root $r$ and $r^q$ cannot both be rational functions of one parameter of degrees at most 20 over constants of degree coprime to 1229. Exactly 75 pairs of a reciprocal representative and $q$ admit any relation in the $20$-by-$20$ square. Every resulting curve has positive genus. [Proof](results.pdf#page=177) · [Curve equations and point counts](data/degree-1229-frobenius-curves.json) · [Verifier](scripts/check_1229_frobenius_curves.py)
- **Exactly 24 degree-1229 pentanomials can fit their five terms in degree 12 in both a root coordinate and its Frobenius conjugate.** This is the smallest possible square, allowing any generator of the sparse root's subgroup. The smallest sum of the two degrees is 18. Only the pentanomial with taps $(3,410,822)$ and its reciprocal attain it. For the former, setting $z^5=r$ and $y=z^{2048}$ gives $zy^3+z^{14}y^2+z^2y+z^{15}+1=0$. The full order of $r$ remains open. [Proof](results.pdf#page=148) · [List the twelve reciprocal pairs](scripts/check_1229_frobenius_boxes.py) · [Lean identities and partial orders](GF2Sparse/SparseRootModels.lean)
- **4,944 specified logarithms would certify the degree-1229 Seroussi pentanomial.** A new identity using $21+8\cdot151=1229$ and an exact character-sum bound reduce the previous 4,993 inputs in the sparse root’s own coordinate. The checker accepts partial submissions and verifies both ordinary and projected logarithms. [Proof](results.pdf#page=148) · [Download the target masks](data/degree-1229-seroussi-direct-targets.csv) · [Verify the criterion or a submission](scripts/check_1229_direct_moment.py) · [Lean identities](GF2Sparse/Seroussi1229.lean)
- **A degree-five Frobenius map cannot act directly on a degree-1229 pentanomial root.** Across all 639,166 irreducible pentanomials, the only rational functions of degree at most five taking a root to a Frobenius conjugate are $T,T^2,T^4$. This also holds over finite constant fields of degree coprime to 1229. For the Seroussi and product pentanomials the least degree of a nonidentity separable map is exactly 205. [Proof](results.pdf#page=147) · [Reproduce the search](scripts/check_1229_sparse_frobenius.py) · [Download the support list](data/degree-1229-irreducible-supports.csv.gz)
- **Cubing can preserve sparse minimal polynomials for at most three consecutive iterates in odd degree above 11.** For a primitive root $r$, the minimal polynomials of $r,r^3,r^9$ all have at most five terms exactly when the first is a trinomial with two exponents equal modulo nine. The degree-23 trinomial $X^{23}+X^9+1$ gives weights 3, 5, 5, 7. Only twelve primitive pentanomials in all odd degrees have sparse third and ninth powers, four each in degrees 5, 7 and 11. [Proof](results.pdf#page=145) · [Reproduce the complete list](scripts/check_cubing_chains.py)
- **In every degree $n>17$ congruent to 13 or 19 modulo 24, a primitive polynomial and the minimal polynomial of its cubed root cannot both have at most five terms.** In degree 1229, all 478 five-term supports with sparse cube images are reducible. The minimum cube weight among the 639,166 irreducible pentanomials is seven, attained by 18 of them. In degree 27 there is a primitive pentanomial pair related by cubing even though all trinomials are reducible. [Proof](results.pdf#page=144) · [Verify the examples and the obstruction](scripts/check_cubed_parity.py) · [Lean certificates for degrees 27 and 1229](GF2Sparse/CubedExamples.lean)
- **Four support patterns classify pentanomials whose cubed roots still have a polynomial of at most five terms and odd weight.** For supports with exponent gcd one, the complete list outside these patterns consists of 130 exceptions, all in degrees at most 17. In odd degree, cubing a root of an irreducible polynomial preserves its multiplicative order. [Proof and patterns](results.pdf#page=143) · [Lean proof of the cube formula and primitive-order criterion](GF2Sparse/CubicImage.lean) · [Reproduce the classification or list a degree](scripts/check_cubed_supports.py)
- **A power of any polynomial tail gives an exact primitivity test.** If $k\deg H<n$, then $X^n+H(X)^k$ is primitive exactly when $X^n+H(X^k)$ is primitive and $\gcd(k,2^n-1)=1$, for $k>0$. Lean also proves the irreducibility criterion and the exact order of $H(r)$ for a primitive root $r$. This gives same-degree primitive trinomials for all 55 archived product witnesses whose taps have a power-of-two ratio. At degree 1229, proper factors are available for every one of the 933 supports of this form. [Lean proof](GF2Sparse/BinomialTail.lean) · [933 proper factors](data/degree-1229-product-ratio-factors.csv) · [Witness and factor checker](scripts/check_binomial_tails.py)
- **A polynomial and its translate cannot both have at most five terms if the degree has five or more ones in binary.** Lean proves a sharp bound for every exponent in the support and characterizes equality. Among degrees below 65,536 with at least four binary ones, only 23 and 71 admit a translated pair of irreducible pentanomials. Both pairs are primitive. At degree 1229 the smallest translate of an irreducible pentanomial has 33 terms, attained by exactly five polynomials. [Proof and examples](results.pdf#page=138) · [Lean theorem](GF2Sparse/ShiftWeight.lean) · [838 proper factors](data/four-bit-translated-pairs.csv) · [Certificate checker](scripts/check_shift_weights.py) · [Degree-1229 census](scripts/census_1229_shift_weights.cpp)
- **Twenty-eight support patterns describe every translated pair of binary trinomials and pentanomials with value one at zero and one.** Across all exponents of either polynomial at most four binary digit positions occur. The checker lists every eligible support in any requested degree, including both orientations. [Classification](results.pdf#page=140) · [Print the patterns or select a degree](scripts/check_translated_supports.py)
- **Three families of affine lines determine 107 projected logarithms in the degree-1229 field.** Direct powering certifies that all 107 values are primitive. Eight also occur in the earlier quadratic catalogue. A fifth-root-of-unity identity gives an explicit logarithm for a cubic factor over $\mathbb F_{2^{20}}$ from 207 known factors. [Exponent table](data/degree-1229-direction-logs.csv) · [Derivation and order checks](scripts/check_1229_direction_logs.py)
- **A degree-1229 pentanomial root admits no short multiplicative relation with its translate.** Among all degree-1229 elements satisfying $r^u=(1+r)^v$ with $1\le u,v\le2457$, the minimum weight of the minimal polynomial is 551. Allowing signed relations of the same height gives exactly 3,234 distinct minimal polynomials. For $1+r^a=r^m$ with $0<a<m\le2457$, the minimum is 567. [Proof](results.pdf#page=137) · [All 539 trinomial factors with their weights](data/degree-1229-short-relations.csv) · [Exhaustive NTL census](scripts/census_1229_short_relations.cpp) · [Independent FLINT checker](scripts/check_1229_short_relations.py)
- **Two more sparse roots have exact identities for their low-degree factors.** For taps $(2,4,1101)$ the value $(1+r+r^2)/(1+r)^{64}$ has exactly the root's order. For taps $(310,609,919)$ the quotient $(1+r^{609})/(1+r^{919})$ equals $r^{620}$ and also has the root's order. Both pass the four known prime-index tests. The full orders remain open. [Derivation](results.pdf#page=137) · [Partition census and verifier](scripts/check_1229_translate_products.py) · [Lean certificates](GF2Sparse/SparseRootModels.lean)
- **Two degree-1229 pentanomial roots have the same order as a product of two linear values.** The candidates with interior exponents $(256,461,922)$ and $(29,58,400)$ each have an explicit coordinate $w$ in which a power of the sparse root equals $w^2(w+1)$. If $A,B$ are the projected logarithms of $w,w+1$ to the certified primitive base and $C$ is the 943-bit cofactor, the exact index of the sparse root is $\gcd(2A+B,C)$. The two exponents remain open in each coordinate. [Proof](results.pdf#page=136) · [Export or verify a logarithm task](scripts/check_1229_rational_cubics.py) · [Lean certificates](GF2Sparse/SparseRootModels.lean)
- **A primitive norm in the degree-1229 model over $\mathbb F_4$ has a 599-term binary minimal polynomial.** Adding its coordinate to the $q=1024$ circle equations gives rank 104,968 modulo the unfactored cofactor. This proves the norm has order $2^{1229}-1$. All 104,968 projected norms in the larger table have been checked by direct powering and have exact order equal to the 943-bit cofactor. The 29,144 projections in the smaller table have that same order. [104,968 exponents](data/degree-1229-q1024-quaternary-logs.csv.gz) · [Direct verification](results.pdf#page=185) · [Rank proof](results.pdf#page=162) · [Polynomial and verification digests](data/degree-1229-q1024-quaternary-rank.json) · [209,936 scalar moments](data/degree-1229-q1024-quaternary-moments.bin.gz) · [Matrix checker](scripts/check_1229_quaternary_pencils.py)
- **Exactly 104,964 of the 104,968 quaternary norms at $q=1024$ are primitive.** Four have index 36,871. The lightest primitive minimal polynomial has 543 terms and label `0xa7ad`. At $q=512$, exactly 29,143 of 29,144 norms are primitive. The remaining norm, labelled `0x87f`, has index 46,703. The smallest primitive weight in the $q=512$ table is 549, attained only at `0x3d02`. The table gives every projected exponent to a common primitive base. [$q=1024$ order and weight census](data/degree-1229-q1024-quaternary-orders.json) · [$q=512$ census](data/degree-1229-q512-quaternary-orders.json) · [29,144 exponents](data/degree-1229-q512-quaternary-logs.csv.gz) · [Logarithm derivation](results.pdf#page=134) · [Field and embedding certificates](data/degree-1229-quaternary-models.json)
- **262,144 specified norms generate the full multiplicative group in each of the five degree-1229 models.** Their labels are the conjugate pairs with no preimage under the rational map. The checker expresses all 524,800 linear norms as explicit products of these values. The pullbacks give 262,656 independent equations over the full group order, and the 1,023 zero-center circles add independent constraints. [Proof](results.pdf#page=133) · [Leaf list and reduction exporter](scripts/check_1229_height_two_pullback.py)
- **Five degree-1229 models attain the minimum possible rational degree, two.** With $q=1024$ each has $x=u/((x^q)^2+x^q+v)$. Both sparse roots and the previously certified primitive generator have explicit embeddings. A projective pencil containing a quadratic leaves a cofactor of degree at most one. Each model supplies 698,709 or 699,392 equations for 524,800 linear-norm logarithms, including 1,023 provably independent equations. The full rank is open. [Proof and models](results.pdf#page=131) · [Five field and embedding certificates](data/degree-1229-height-two-models.json.gz) · [Model verifier](scripts/check_1229_height_two.py) · [Equation census and export](scripts/check_1229_height_two_relations.py)
- **Linear Hermitian pencils give exactly 1,214,007 quadratic logarithms by isolating one binary mask.** For 1,187,645 masks the substituted polynomial has a single irreducible quadratic. A further 26,362 have two conjugate quadratics with the same binary norm. A uniqueness theorem and a census of all projective forms prove these lists exhaustive in the certified degree-1229 model. Direct powering verifies all 1,214,007 exponents. Exactly 1,213,940 of these values are primitive, and their minimum polynomial weight is 531. [Uniqueness theorem and census](results.pdf#page=129) · [Single factors](data/degree-1229-terminal-catalogue.bin.gz) · [Conjugate pairs](data/degree-1229-terminal-conjugates.bin.gz) · [Logarithm lookup](scripts/check_1229_terminal_census.py) · [Exact order census](data/degree-1229-terminal-order-census.json)
- **Both degree-1229 pentanomial orders now reduce to logarithms of relative degree at most four over $\mathbb F_{2^{20}}$.** For each candidate the two degree-32 factors give 2,058 degree-16 factors and 2,117,682 distinct degree-eight factors. Each of these has a certified reduction to quartics or smaller factors. One product branch reaches 1,058,819 distinct terminal masks, including 45 solved quadratics. [Derivation](results.pdf#page=126) · [All degree-eight pencils](data/degree-1229-dyadic-level3.bin.gz) · [Branch verifier](scripts/check_1229_dyadic.py)
- **One logarithm now determines the exact order of either degree-1229 pentanomial.** In the certified $q=1024$ model, the remaining irreducible factor has degree 57 over $\mathbb F_{2^{20}}$ for the Seroussi polynomial, and degree 58 for the product polynomial. Every other factor has a verified logarithm. The task files contain the subgroup base, field modulus, target, coefficient and known offset needed to check an answer. [Seroussi single-factor task](data/degree-1229-seroussi-known-offset-task.json) · [Product single-factor task](data/degree-1229-product-known-offset-task.json) · [Polynomial identities](data/degree-1229-known-offset-quotients.json)
- **All 126 product-cubic quadratics resist a completely split quadratic Hermitian pencil.** For every binary $q\ge4$, a separable quadratic pencil that splits on an entire projective $\mathbb F_q$-subline pulls it back to two sublines. At $q=1024$, every other target subline gives at least 481 nonsplit quadratic fibers. The same linear equations that rule out the linear pencils then rule out the completely split quadratic pencils for all 126 targets. [Proof](results.pdf#page=125) · [Exact count](scripts/check_1229_quadratic_pencils.py) · [Lean trace obstruction](GF2Sparse/HermitianDescent.lean)
- **Each degree-1229 pentanomial has a two-logarithm task attaining the minimum degree for a direct norm quotient.** Both unknowns have degree 31 over $\mathbb F_{2^{20}}$. Each candidate also has a single degree-62 task, a pair of degree-32 tasks, and a single degree-64 task. An exhaustive check of all 1,229 conjugates proves the minimum total degree is 62 in the certified $q=1024$ model. The four representations use the same base and compute the same sparse-root index. [Norm factors for both pentanomials](data/degree-1229-q1024-norm-quotients.json) · [Minimum-degree proof](results.pdf#page=124) · [Exhaustive checker](scripts/check_1229_norm_height.py)
- **All 20 cubic factors in the two degree-1229 tasks and the Seroussi degree-seven descent now reduce to quadratics.** In the product candidate, its cubic factor reduces to 126 unknown quadratic logarithms over $\mathbb F_{2^{20}}$. The Seroussi candidate's cubic factor reduces to 534. For its degree-seven factor, contributors can choose between 44 logarithms of degree at most three, 8,996 quadratics, or two logarithms of degrees 15 and 23. Three quadratic exponents on alternative branches are now known exactly. [Proof and counts](results.pdf#page=121) · [Pencils and three exponents](data/degree-1229-hermitian-descents.json) · [8,996 quadratic tasks, compressed JSON](data/degree-1229-seroussi-d3-quadratics.json.gz)
- **Each of two degree-1229 pentanomials now reduces to eleven projected logarithms.** For $X^{1229}+X^{15}+X^6+X^2+1$, the largest factor degree over $\mathbb F_{2^{20}}$ dropped from 33 to 18. For $X^{1229}+X^{77}+X^{50}+X^{27}+1$, it dropped from 29 to 21. The task files give each factor and its coefficient. The checker verifies partial submissions and computes the exact group index when a task is complete. [Seroussi task](data/degree-1229-seroussi-descent-task.json) · [Product task](data/degree-1229-product-descent-task.json) · [Descent checker](scripts/check_1229_log_descent.py)
- **A degree-five elliptic isogeny gives 37,751 more verified logarithms.** The rational map in the $q=1024$ model comes from Frobenius squared minus the identity on $w^2+w=z^3+z$, after inverting the input coordinate. The point count predicts the irreducible fibers. Two substitutions extend the original table from 52,488 to 90,239 distinct entries. NTL checks every new exponent directly in the degree-1229 field. [37,751 exponents](data/degree-1229-isogeny-logs.csv.gz) · [Derivation](results.pdf#page=118) · [Logarithm generator](scripts/check_1229_isogeny_logs.py) · [Lean coordinate and cycle identities](GF2Sparse/QuinticIsogeny.lean)
- **Circle and trace equations supply another 600 logarithms, bringing the verified total to 90,839.** One of these gives the exponent for $T^3+T+1$ in the descent for the product candidate. Its factor with mask `0x35d5` now has 91 open logarithms of relative degree at most eight. [600 exponents](data/degree-1229-partial-circle-logs.csv) · [Reconstruction](scripts/check_1229_partial_circles.py)
- **Exactly 90,835 of the 90,839 table elements are primitive in degree 1229.** One of the other four has index 36,871, and three have index 46,703. The least number of terms in any of their minimal polynomials is 545. Degree 1229 still needs a five-term witness. [Extended order and weight census](data/degree-1229-extended-order-census.json) · [Original factor base](results.pdf#page=116) · [Census checker](scripts/check_1229_factor_base_orders.py)
- **In prime degree $n\ge67$, fewer than $(\sqrt{136}/15)n+7$ elliptic subgroup targets and at most one prime-order test certify a proposed generator.** Fewer than $(\sqrt{10}/3)n+7$ targets need no preliminary tests. A parameterized bound applies in every degree $n\ge64$. In degree 1229, the 733 published elements generate the full multiplicative group. Exhibiting them as powers of any one sparse root would certify it primitive. The degree-53 example takes 30 targets after trial division or 38 using only the degree. [Uniform bound and degree-1229 proof](results.pdf#page=195) · [733 field elements](data/degree-1229-elliptic-unconditional-targets.csv.gz) · [Elliptic targets and checker](scripts/check_elliptic_ray.py) · [Original all-degree criterion](results.pdf#page=117) · [Lean inequalities](GF2Sparse/EllipticRay.lean)
- **Unconditional primitivity in degree 1229 without factoring $2^{1229}-1$, and a single-scalar pentanomial reduction.** For the $q=1024$ Frobenius model $I(X)\mid h_0(X^{1024})+Xh_1(X^{1024})$ ($h_0=T^5+T^2+1$, $h_1=T^3+T$), Hermitian circle norm-projection over $\mathbb F_{2^{20}}$ yields 93,656 exact multiplicative relations (92,910 canonically unique) of exact corank one across all 52,488 binary irreducibles of degree dividing 20. Solving the full $52{,}488\times 52{,}488$ system modulo the unfactored 284-digit cofactor $C$ via AVX2 Wiedemann and FLINT Half-GCD yields all 52,488 projected discrete logarithms $(x^K)^{e_P}\equiv P(x)^K\pmod{I(X)}$, every one directly verified in $\mathbb F_{2^{1229}}$ with $\gcd(e_P,C)=1$. The character-sum bound gives $Q=1294.90>1227$ using only one trial division ($C\bmod 2459\ne0\Rightarrow J\ge 9833$, and $Q=1366.00>1227$ with the sieved wheel), unconditionally proving $I(X)$ (weight 613) and all 111 degree-$\le10$ evaluations $P(x)$ primitive of exact order $2^{1229}-1$. Certifying any of the 639,144 eligible degree-1229 pentanomials now reduces from 3,380 targets to one single scalar $e_r$ with $(r^K)^{e_r}\equiv x^K$. [52,488 verified logs](data/degree-1229-q1024-projected-logs.csv.gz) · [Certificate metadata](data/degree-1229-q1024-certificate.json) · [Direct verifier](scripts/check_1229_q1024_logs.py) · [Single-scalar checker](scripts/check_1229_single_log.py) · [Relation generator & 943-bit solver](scripts/wiedemann_943.cpp)
- **Four exterior-power tests for 100% of six infinite shifted-dyadic trinomial families (including all Mersenne and Fermat degrees).** For any shifted dyadic trinomial $X^{2^s+d}+X^a+1$, any product-one triple or quartet of reciprocal roots satisfies $K(1)=1$ immediately, reducing the quartet dynamics to a 2-variable denominator-free polynomial map with resultants as small as degree 8. This gives 100% all-$s$ squarefree trinomial fourth-test covers for every Mersenne degree $2^s-1\ge7$ using two trinomials ($a\in\{1,3\}$, period 3), every Fermat number $2^{2^k}+1\ge5$ using two trinomials ($a\in\{2,5\}$), every $2^s+2\ge6$ using two trinomials ($a\in\{1,7\}$, period 12), and every $2^s-3\ge13$, $2^s+1\ge5$, $2^s+3\ge5$, and $2^s+5\ge7$ using three trinomials each (plus all odd pullbacks $T(X^m)$). [Certificates](data/shifted-dyadic-trinomial-4test-certificates.json) · [Exact algebraic prover](scripts/check_shifted_trinomial_quartets.py) · [C++ degree-261 checker](scripts/check_trinomial_4test.cpp)
- **At least $2^{0.5438n}$ primitive binary polynomials have at most $0.219245n$ terms in every sufficiently large degree.** More generally, every monic binary polynomial with constant one is within $0.219245n$ coefficient changes of at least this many primitive polynomials. For sufficiently large $n$, the agreement can include $\lfloor0.4226n\rfloor$ prescribed interior coefficients divided in any proportion between the two ends. In degree 1229, more than $2^{622}$ primitive polynomials have at most 313 terms using only the degree. In any 720 consecutive interior positions of degree 1229, more than $2^{616}$ primitive polynomials have all their interior terms there and at most 309 terms overall. The same count holds within 308 coefficient changes of any template, with all changes in the chosen interval. [Proof for every division between the two ends](results.pdf#page=187) · [Counting theorem](results.pdf#page=183) · [Fourier estimate](results.pdf#page=98) · [Squarefree-divisor sieve](results.pdf#page=184) · [Earlier finite bounds](results.pdf#page=166) · [Exact calculation](scripts/check_primitive_weight_bound.py) · [Lean kernel check of the 309-term bound](GF2Sparse/SelbergWeight.lean) · [Earlier Lean arithmetic](GF2Sparse/FourierWeightBounds.lean) · [Shparlinski's earlier bound](https://www.mathnet.ru/eng/ppi820)
- **Lower exponents at most 80 in every degree from seven.** There is a squarefree product pentanomial with exponent gcd one, odd factor count, no inverse pair and no factor of degree at most six. Thirty fixed tap pairs cover the odd degrees above 80, and 24 cover the even degrees above 150. A direct check handles the smaller degrees. At degree 1229 the list includes the irreducible $X^{1229}+X^{64}+X^{43}+X^{21}+1$, which passes every known order projection. [Odd-degree proof and tap list](results.pdf#page=91) · [Even-degree proof and tap list](results.pdf#page=93) · [Coverage checker](scripts/check_fixed_tap_cover.py)
- **Long intervals where every bounded choice of exponents factors.** Fix a distance from the two endpoints and any desired number of factors. In arbitrarily long intervals starting at a prime, every odd-weight polynomial with constant term one supported within that distance has at least that many distinct primitive factors of prime degree. The starts can lie in any prescribed reduced residue class. At a 269-digit prime and its successor, all ten choices from the two tap lists above have two certified primitive factors each, all of degrees greater than six. [Proof](results.pdf#page=94) · [Twenty factor certificates](data/fixed-tap-primitive-factors.csv) · [Checker](scripts/check_fixed_tap_block.py)
- **The first unresolved consecutive degree is 1229.** Lean proves that $X^{1229}+X^{77}+X^{50}+X^{27}+1$ is irreducible. If $K$ is the product of the four known prime factors of $2^{1229}-1$, its root order is $Kt$ with $t>1$ dividing the remaining 284-digit cofactor. Two independent product calculations exclude every cofactor prime through 1,183,886,414,924,742,657. The root orders of all 639,166 irreducible pentanomials exceed $2^{331}$, and those of the 639,144 passing the four known tests exceed $2^{346}$. The cofactor has at most 15 prime factors counted with multiplicity. Proving that $t$ equals the cofactor for either root would extend the consecutive range through 1230, since degree 1230 already has a witness. The next gap is 1231. [Product certificate](GF2Sparse/Degree1229.lean) · [Seroussi certificate](GF2Sparse/Seroussi1229.lean) · [Independent check](scripts/check_degree_1229.py) · [Sieved divisor check](scripts/check_1229_wheel.py) · [Factorization](https://factordb.com/index.php?query=2%5E1229-1)
- **Every degree-1229 sparse irreducible has root order above $2^{330}$.** Of the 639,166 irreducible pentanomials, 639,144 have root order above $2^{345}$ and pass all four known-prime tests. All 639,166 have a root order divisible by a prime of the remaining cofactor. The eleven exceptional reciprocal pairs each miss either 36,871 or 46,703. [Proof](results.pdf#page=68) · [Counts by smallest tap](data/degree-1229-pentanomial-census.csv) · [Exceptional supports](data/degree-1229-order-exceptions.csv) · [Independent audit](scripts/check_1229_pentanomial_census.py) · [All 319,583 reciprocal representatives with order-test flags](data/degree-1229-irreducible-supports.csv.gz)
- **An exact quadratic logarithm in degree 1229.** For a root $r$ of $X^{1229}+X^{1066}+X^{533}+X^{163}+1$, take $a=(1+r^{533})^{-1}$. Then $a^2+a+1=r^{163}$ and $(a+1)/a=r^{533}$. The quadratic value generates the same subgroup as $r$, of order greater than $2^{345}$. A second pentanomial gives a quadratic equation relating a fifth root to its 256th power. A binomial multiplier cannot reduce such a direct relation to degree one. The full order of both roots remains open. [Quadratic logarithm](results.pdf#page=101) · [Frobenius equation and proof of minimality](results.pdf#page=102) · [Lean certificates](GF2Sparse/SparseRootModels.lean) · [Reproduce both searches](scripts/check_sparse_root_models.py)
- **A trinomial logarithm in degree 1229 requires a quotient with at least 25 terms.** A relation $1+r^a=r^b$ for a pentanomial root makes its polynomial divide $1+X^a+X^b$. In any degree $n$, if a pentanomial has exponent gcd one and the quotient has $h$ terms, then $27n\le 2(h+2)^3$. For quotients of at most nine terms, the largest possible degree of a primitive pentanomial divisor is 17. Lean also proves that closure of the powers and zero under addition of one characterizes primitivity. [General bound and finite counts](results.pdf#page=103) · [Lean criterion](GF2Sparse/TrinomialMultiples.lean) · [Direct enumeration](scripts/check_trinomial_multiples.cpp)
- **Generators in every prime extension degree $n\ge17$.** For any element $x$ of degree $n$, the values $B(x)$ of binary irreducibles with degree dividing $m$ generate the multiplicative group whenever $2m<n$ and $2n^2\le3\cdot2^m$. In degree 1229, any 44,919 degree-20 irreducibles suffice in every coordinate. In the published $q=1024$ coordinate, the sparse root times $x^{6655}$ factors in auxiliary degrees 7, 13, 19, and 29. [Proof](results.pdf#page=106) · [Exact generation bounds and sparse-root factors](scripts/check_1229_factor_generation.py)
- **Logarithm descent for the six open degrees through 1280.** Explicit field equations meet the hypotheses of the Granger–Kleinjung–Zumbrägel algorithm in each degree. In degree 1229, the two selected sparse roots and all ten period targets of degree at most six are explicit quotients of norms of good degree-16 values. For these targets the least degree is 16 for a quotient and 32 for a single norm to the same field. With linear inputs, the smallest possible constant fields have binary degrees 3744 and 7410, respectively. Taking the norm down to the binary target field gives a further bound in all six degrees. Every nonzero element is the norm of a good degree-16 value and can also be written as a product of at most 15 norms of linear values. [Quotient certificates](data/degree-1229-norm-quotients.json) · [Optimality proof](results.pdf#page=112) · [Lean degree bound](GF2Sparse/NormQuotients.lean) · [Smallest constant fields for linear norms](results.pdf#page=114) · [Single norm factors](data/degree-1229-norm-factors.json) · [Field models](results.pdf#page=109) · [Binary target theorem](results.pdf#page=113) · [Lean numerical bounds](GF2Sparse/NormCoverBounds.lean) · [PARI/GP checker](scripts/check_1229_forward_descent.py)
- **A quadratic Frobenius model for the first open degree.** A four-term polynomial over $\mathbb F_{1024}$ has a factor of degree 1229. Its root satisfies $t=(y^2+vy+u)/(uy)$ with $y=t^{1024}$. Both sparse roots and their common Gauss period are given explicitly in this field. All 1,023 centered norm circles have split quadratic right-hand sides. Norms of the linear and irreducible quadratic values generate the binary target group. [Field data](data/degree-1229-quadratic-frobenius.json) · [Proof](results.pdf#page=107) · [PARI/GP checker](scripts/check_1229_quadratic_model.py)
- **A route around the unresolved factorization.** For any one of 639,144 degree-1229 candidates, 3,380 specified logarithms in a Gauss period coordinate would prove full order. Each logarithm can be computed in the subgroup of 943-bit order. The checker obtains 6,741 polynomial logarithms from those inputs. The new list is a subset of the 3,399-row list. All three published lists use the same coordinate and submission format. The requested exponents remain open. The character-sum and counting methods already certify examples in degrees 47, 61, and 89 without factoring their group orders. Lean checks their 213 logarithm identities. [3,380 targets](data/degree-1229-period-wheel.csv) · [Original target list](data/degree-1229-period-targets.csv) · [Relation checker](scripts/check_period_relations.py) · [Character-sum and counting proofs](results.pdf#page=44) · [Lean logarithm checks](GF2Sparse/FactorBaseExamples.lean)
- **The semiprime census covers 380,093 pairs and gives 61 exceptions to the prime conclusion.** For each pair with $q=2p+1\equiv7\pmod8$ through $q=10{,}000$, an explicit sparse irreducible has only primes of smaller degree in its root order. [Proof](results.pdf#page=67) · [Census checker](scripts/check_semiprime_gap.cpp) · [61 seeds](data/semiprime-gap-seeds.csv)
- **A forced prime in infinitely many semiprime degrees.** If $p<q$ are odd primes with $2q\le3p$, every irreducible binary trinomial or pentanomial of degree $n=pq$ has root order divisible by a prime $\ell$ with $\operatorname{ord}_\ell(2)=n$. This applies, for example, in degree 1,022,117. The proof uses a Lean-verified bound for a subgroup containing $x$ and $1+x$. [Proof](results.pdf#page=61) · [Lean subgroup bound](GF2Sparse/PlaneOrder.lean)
- **A full-degree order component in all 251 odd semiprime degrees through 1280.** For every degree $n=pq\le1280$ with distinct odd primes $p,q$, every irreducible binary polynomial of weight at most five has a root order divisible by a prime power $L$ with $\operatorname{ord}_L(2)=n$. A prime is forced in exactly 245 of those degrees. Explicit trinomials give the six exceptions. [Proof and exceptions](results.pdf#page=60) · [Reproduce the census](scripts/check_subfield_census.py)
- **Sparse roots cannot come from three independent subfields.** If $n$ is a product of three pairwise coprime degrees greater than one, a root of a degree-$n$ irreducible trinomial or pentanomial cannot be a product of elements from those three subfields. Two coprime proper subfields already give the exclusion for trinomials. [Proof](results.pdf#page=62)
- **A prime factor forced in degree 1243.** Every irreducible polynomial of weight at most five in this degree has a root order divisible by a prime $\ell$ with $\operatorname{ord}_\ell(2)=1243$. That prime belongs to the remaining cofactor of $2^{1243}-1$ and exceeds 262,340,983,306,321,921. The published candidate has root order above $2^{181}$. The support argument applies to all candidates and also forces 151 into every such order in degree 15. [Subfield calculation](scripts/check_subfield_products.py) · [Lean rank and arithmetic checks](GF2Sparse/SubfieldProducts.lean)
- **Quotients of roots give an order bound for pentanomials.** For every $n\ge4$, $X^n+X^{n-1}+X^2+X+1$ is squarefree and its quotient-ring period $h$ satisfies $3(h-1)\ge n(n-1)$. The proof bounds the number of root pairs with the same quotient for any support that splits as $X^mA(X^d)+B(X^d)$. A Frobenius orbit then restricts which subfields can contain a quotient. [Lean counting proof](GF2Sparse/TwoBlockOrder.lean) · [Independent check](scripts/check_two_block_orders.py)
- **An order bound for every irreducible pentanomial with exponent gcd one.** Its degree $n$ and root order $h$ satisfy $16h^3\ge5n^4$, strengthened to $16h^3\ge5n^4+10n^2+1$ in odd degree. The proof also gives a support-dependent test for a proposed period. It recovers the full order 63 of $X^6+X^4+X^3+X+1$ from two short intervals of exponents. [Proof](results.pdf#page=51) · [Check the bounds](scripts/check_exponent_spans.py)
- **Three-root test for odd-degree pentanomials with four exponents in arithmetic progression.** Among the irreducibles, the only exceptions are $X^{9d}+X^{6d}+X^{3d}+X^d+1$ and their reciprocals, with $d=73^j$. Their roots have exact order $73^{j+1}$. For odd-degree irreducibles of this shape with exponent gcd one, the root order is at least $n(n-1)+1$. [Proof](results.pdf#page=50) · [Lean sampling theorems](GF2Sparse/ProgressionTriples.lean) · [Independent check](scripts/check_trinomial_triples.py)
- **All exceptional irreducible trinomials for the three-root test.** Three roots multiply to one, with repetition allowed, precisely for $X^{bd}+X^d+1$ and their reciprocals with $(b,d)=(2,3^j),(3,7^j),(9,73^j)$, $j\ge0$. Lean checks the exclusion of every coprime tap above degree nine. Direct Frobenius-orbit checks reproduce all 13 exceptions through degree 192. [Classification and proof](results.pdf#page=49) · [Lean](GF2Sparse/TrinomialOrder.lean) · [Independent check](scripts/check_trinomial_triples.py)
- **A sharp trinomial order bound.** If $\gcd(n,a)=1$, the period of $X$ modulo $X^n+X^a+1$ is at least $n(n-1)+1$. For $a=1$ equality holds exactly when $n-1$ is a power of two. Every irreducible trinomial with $1<a<n-1$ and coprime exponents passes the first three root-product tests. [Proof](results.pdf#page=48) · [Lean quotient-ring bound and sharp family](GF2Sparse/TrinomialOrder.lean)
- **Subfield restrictions on trinomial orders.** For an irreducible trinomial with coprime exponents, every quotient of two distinct roots has the full degree $n$. If $n$ has at most two distinct prime divisors, the root order has a prime-power divisor $L$ with $\operatorname{ord}_L(2)=n$. In degree 15, every such root order is divisible by 151. [Proof and exterior-square factor degrees](results.pdf#page=52) · [Lean divisibility exclusion](GF2Sparse/TrinomialOrder.lean)
- **Primitive witnesses.** Lean proves the statement for every $1\le n\le672$. For every $5\le n\le672$ it verifies the shape $X^n+(X^u+1)(X^v+1)$, where $0<u<v$ and $u+v<n$. The degree-672 witness is $X^{672}+X^{11}+X^6+X^5+1$. The same exponent relation appears in the pentanomial entries of Table 4.8 of the *Handbook of Applied Cryptography*. Published minimum-weight tables cover degrees 2 through 640 with unrestricted interior exponents. [Lean degree coverage](GF2Sparse/Coverage.lean) · [Table 4.8 and its construction](https://cacr.uwaterloo.ca/hac/about/chap4.pdf#page=37) · [Minimum-weight tables](https://people.math.carleton.ca/~daniel/hff/)
- **Consecutive computational witnesses through degree 1228.** PARI/GP finds a primitive product pentanomial in every degree from 5 through 1228. FLINT independently verifies all 1,224 full orders and proves the 4,381 distinct integer factors prime. The final row gives $X^{1228}+X^{33}+X^{18}+X^{15}+1$. [Degrees 5–1206](data/product-witnesses-5-1206.csv) · [Degrees 1207–1228](data/product-witnesses-1207-1228.csv) · [Independent checker](scripts/check_product_range.py)
- **Every even degree through 2292.** For every even $6\le n\le2292$ the table gives a primitive $X^n+(1+X^u)(1+X^v)$ with $u+v\le299$. FLINT checks the 1,144 full orders using 6,794 distinct prime factors. The bound 299 is sharp in degree 2016. Of the 22,052 shorter supports in this family, 22,027 are reducible and the remaining 25 have proper root order. Degrees two and four are covered by the small Lean certificates. [All even-degree witnesses](data/even-least-span-6-2292.csv) · [Supplemental order factors](data/mersenne-even-2182-2292-extra.json) · [Sharpness check](scripts/check_even_span.py) · [Proof](results.pdf#page=55)
- **Six open degrees through 1280.** In the interval from 1230 through 1280, PARI/GP found 46 primitive product pentanomials. FLINT verified their exact orders and the 673 distinct prime factors used. Combining the intervals leaves 1229, 1231, 1237, 1243, 1249, and 1259 open in this project. In degree 1280 the interior exponents are 6, 49, and 55. [Witnesses](data/product-witnesses-1230-1280.csv) · [Complete order factorizations](data/mersenne-1230-1280-factors.json) · [Proof](results.pdf#page=54)
- **Primitive witnesses in at least 2,119 of the first 2,688 degrees.** The interval 2561–2688 adds 44 even degrees and six odd degrees. In degree 2574 the polynomial is $X^{2574}+X^5+X^4+X+1$. PARI/GP and FLINT checked all 50 orders, including 1,541 prime-index powers. [Witness table](data/product-witnesses-2561-2688.csv) · [Group factorizations](data/mersenne-2561-2688.json)
- **Primitive witnesses through degree 2560.** The interval 2417–2560 adds 57 even and seven odd degrees to the 2,005 previously covered. One example is $X^{2441}+X^{33}+X^{27}+X^6+1$. PARI/GP and FLINT independently checked all 64 orders using 1,440 distinct prime factors. Lean also proves the full order of $X^{2520}+X^{199}+X^{177}+X^{22}+1$. The three even gaps through 2416 are 2294, 2302 and 2416. [New witnesses](data/product-witnesses-2417-2560.csv) · [Degree-2520 Lean proof](GF2Sparse/Witness2520.lean) · [Their group orders](data/mersenne-2417-2560.json) · [Degrees 2293–2416](data/product-witnesses-2293-2416.csv) · [Earlier group orders](data/mersenne-2293-2416.json) · [Odd degrees through 1535](data/odd-product-witnesses-1281-1535.csv) · [Through 1791](data/odd-product-witnesses-1537-1791.csv) · [Through 2047](data/odd-product-witnesses-1793-2047.csv) · [Through 2291](data/odd-product-witnesses-2049-2291.csv) · [Checker](scripts/check_product_range.py)
- **Twelve primitive pentanomials in degree 4095.** One is $X^{4095}+X^{255}+X^3+X+1$. FLINT and PARI/GP independently check every sparse primitive degree-12 seed. Twelve lifts have full root order and the other six have exact index seven. The factor list and the elliptic-curve primality certificate for its 425-digit prime are included. Lean also verifies the six seventh-power obstructions. [Exact orders and seed list](results.pdf#page=37) · [FLINT check](scripts/check_ore_lifts.py) · [PARI/GP check](scripts/check_ore_4095.gp) · [Lean obstructions](GF2Sparse/OreNormObstructions.lean)
- **Larger primitive witnesses.** Lean certifies product pentanomials in degrees 1279, 2203, 2281, 3217, 4253, 4423, 9689 and 11213. The last is $X^{11213}+X^{153}+X^{83}+X^{70}+1$. It also certifies two published examples, Seroussi’s pentanomial $X^{9941}+X^{29}+X^{12}+X^{10}+1$ and the Kurita–Matsumoto trinomial $X^{44497}+X^{8575}+1$. The certificates check both Lucas–Lehmer primality and the polynomial power. [Packed squaring proof](GF2Sparse/PackedSquare.lean) · [Degree 11213](GF2Sparse/PackedMersenne11213.lean) · [Degree 44497](GF2Sparse/PackedMersenne44497.lean) · [Seroussi’s table](https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/98/HPL-98-135.pdf) · [Published trinomial table](https://maths-people.anu.edu.au/~brent/pd/rpb199.pdf)
- **Irreducible lifts of the same weight.** Replacing each exponent $i$ by $2^i-1$ takes a primitive degree-$s$ seed to an irreducible of degree $2^s-1$. Lean proves the converse and shows that every lifted polynomial passes all root-product tests of lengths below $s$. This supplies sparse irreducibles for every $1\le s\le672$, and the seed in degree 11213 gives an irreducible pentanomial of degree $2^{11213}-1$ passing 11212 tests. The degree-44497 seed gives a trinomial passing 44496 tests. For these irreducible lifts of degree $n=2^s-1$ with $s\ge5$, the logarithm base two of the root order exceeds $\sqrt{n+1}-\tfrac12\log_2(n+1)$. In the degree-$2^{2203}-1$ example the order exceeds $2^{2^{1102}-1101}$. [Lean order bound](GF2Sparse/OreOrder.lean) · [General equivalence](GF2Sparse/OreLift.lean) · [Certified examples](GF2Sparse/OreExamples.lean)
- **Prime divisors forced into lifted orders.** Every Ore root from a primitive degree-11 seed has order divisible by a prime $q$ with $\operatorname{ord}_q(2)=2047$. The analogous result holds for degree-15 seeds with $\operatorname{ord}_q(2)=32767$. The proof separates products of conjugates and works without factoring either lifted group order. The integer lower bound from mixed seed degrees also gives $\log_2\operatorname{ord}(r)\ge \tfrac32\log_2(3)\sqrt{n+1}-O(\log n)$ for all primitive seeds, where $n$ is the lifted degree. [Divisor theorem and proof](results.pdf#page=39) · [Lean proof of the integer bound](GF2Sparse/OreOrderCounts.lean) · [Arithmetic checker](scripts/check_ore_components.py)
- **Two nonprimitive lifts in degree 2047.** The primitive seeds with interior exponents $(2,3,7)$ and $(4,8,9)$ give lifts whose root orders omit 47. Lean checks explicit 47th roots of $X$ for both. The other 44 sparse primitive seeds pass all seven known prime-factor tests. A 549-digit cofactor remains in the order calculation. [Lean exclusions](GF2Sparse/OreIndexFortySeven.lean) · [Reproduce all 46 checks](scripts/check_ore_2047.py)
- **Full-order Ore lifts.** Lean verifies the primitive trinomials $X^{511}+X^{15}+1$ and $X^{1023}+X^7+1$. Of the 83 primitive binary trinomials and pentanomials in seed degrees 2 through 10, 81 have primitive lifts. The two exceptions give irreducible degree-63 pentanomials of exact root order $(2^{63}-1)/7$. [Primitive certificates](GF2Sparse/OrePrimitiveExamples.lean) · [Both exceptions in Lean](GF2Sparse/OreIndexSeven.lean) · [Reproduce the census](scripts/check_ore_lifts.py)
- **Exact degrees of Ore-root norms.** Take a primitive degree-$s$ seed, a lifted root $r$, and a divisor $b$ of $s$. Set $m=(2^s-1)/(2^b-1)$. The norm of $r$ to the degree-$m$ field has degree exactly $m$, and its conjugates span a binary space of dimension $(s/b)^b$. When $s=2b$, adding one to the norm gives a normal basis generator. [Proof in the research note](results.pdf#page=33) · [Lean proofs of the norm algorithm and the criterion for a given expansion](GF2Sparse/OreNorms.lean)
- **A normal basis from any primitive seed.** For every nonzero binary subspace of the additive Ore roots, take the product of its nonzero elements. Distinct subspaces give distinct elements of the root's multiplicative subgroup. Summing the products for the successive spans of $r,r^2,\ldots,r^{2^{s-1}}$ gives a normal basis generator of the entire lifted field of degree $2^s-1$. [Exterior-power proof](results.pdf#page=35) · [Independent finite-field checks](scripts/check_ore_bases.py)
- **Reciprocal primitive seeds have the same lifted root order.** In seed degree $s$, every root of the reciprocal lift is a product of exactly $2^{s-1}-1$ distinct roots of the original lift. The two root sets generate the same multiplicative group. This explains why the two degree-63 exceptions occur together and proves primitivity of two further trinomials, $X^{511}+X^{31}+1$ and $X^{1023}+X^{127}+1$. [Lean reciprocity proof](GF2Sparse/OreReciprocal.lean) · [Both trinomial proofs](GF2Sparse/OreReciprocalExamples.lean) · [Proof in the note](results.pdf#page=32)
- **Exact factor degrees from seed orders.** For any constant-one seed, the largest irreducible factor degree in its Ore lift equals the multiplicative order of $X$ modulo the seed. If the seed is irreducible, every factor has that degree. The two exceptional degree-63 examples each give a second pentanomial of degree $2^{63}-1$ with exactly seven distinct irreducible factors of degree 1,317,624,576,693,539,401. [General Lean proof](GF2Sparse/OreFactors.lean) · [Exact factor counts](GF2Sparse/OreFactorExamples.lean)
- **Three-root test for dyadic taps.** For a root of $X^n+X^{2^i}+1$, membership in a product-one triple is equivalent to $(1+x)^m=x^m+1$, where $m=n-2^i$. Every irreducible such trinomial above degree nine passes the first three tests. For $n=2^i+2^b(2^{2j}-2^j+1)$ with $j$ coprime to six, the trinomial passes for all $i,b$. [Lean criterion](GF2Sparse/DyadicTap.lean) · [Lean family and degree bound](GF2Sparse/KasamiTriples.lean) · [Complete counts and proof](results.pdf#page=41)
- **Translating whole intervals of witnesses.** For arbitrarily large common shifts $T$, changing just the leading term in each checked pentanomial of degree $5\le j\le672$ gives 668 consecutive squarefree, exponent-gcd-one pentanomials. At degree $T+j$, the shortest selection of roots with product 1 has length exactly $j$. Each enlarged polynomial contains its original seed as a factor. The same theorem transfers the degree-2203 witness to arbitrarily high degrees with first failure exactly 2203. [Lean proof for all 668 tails](GF2Sparse/TranslatedInterval.lean) · [General transfer theorem](GF2Sparse/ShiftedPeriods.lean) · [Proof for simultaneous translations](results.pdf#page=30)
- **Three tests for every degree with at most three ones in binary.** For every such $n\ge4$, a squarefree binary polynomial with at most five terms has no product of one, two or three roots equal to 1. For odd $n>7$ one of the four trinomials $X^n+X^a+1$ with $a=3,4,5,7$ works. For $n\equiv2\pmod4$ above 11 the choices are $3,7,11$. Two commuting Frobenius powers reduce the infinitely many degrees to 2,628 and 171 unordered residue pairs. [Proof in the note](results.pdf#page=24) · [Reproduce the finite calculation](scripts/check_binary_degree_triples.py)
- **Three tests for signed binary degrees.** Every $n\ge4$ expressible as a sum of at most three signed powers of two has a squarefree polynomial of weight at most five passing the first three root-product tests. At every odd such degree there is a trinomial with coprime exponents. For $n=2^s-2^t-1$ with $1\le t\le s-2$, two integer gcds determine exactly which powers of two work as the inner exponent, and at least one always works. [Proof and choice of exponent](results.pdf#page=27) · [Lean choice for every $s,t$](GF2Sparse/SignedDegreeChoices.lean) · [Lean 999-one example](GF2Sparse/SignedTriples.lean) · [Reproduce the finite cases](scripts/check_binary_degree_triples.py)
- **Thirty-two consecutive degrees after every sum of two powers of two.** For $s,t\ge1$ and $1\le e\le32$, write $n=2^s+2^t+e$. Except in degree 8, some trinomial $X^n+X^a+1$ with $a\le21$ and $\gcd(n,a)=1$ passes all three root-product tests. Degree 8 has a primitive pentanomial. The finite calculation checks every residue pair for all 32 offsets. [Proof and examples](results.pdf#page=25) · [Calculation](scripts/check_binary_degree_triples.py)
- **A limit on fixed trinomial searches.** For every bound $A$, there are arbitrarily large prime degrees $n$ where *every* $X^n+X^a+1$ with $1\le a\le A$ has three distinct roots with product 1. This holds in any prescribed reduced arithmetic progression. The note extends the obstruction to any finite list of rational affine rules for $a$ and to their cubic-sampled pentanomials. [Lean proof for bounded exponents](GF2Sparse/TripleObstruction.lean) · [Proof for affine rules](results.pdf#page=26)
- **Restrictions on every primitive support in prime degrees.** Fix finitely many rational slopes and a width around each slope times the degree. In every reduced arithmetic progression there are arbitrarily large prime degrees where every polynomial supported in those bands has a proper factor. For example, in prime degree 1307 the bands within two of $0,1307/2,1307$ force a factor of degree at most five. The note also proves a growing-width bound for rational slopes and a fixed-width result for arbitrary real slopes. [Lean proof and degree-1307 example](GF2Sparse/PrimeGrid.lean) · [Proofs in the note](results.pdf#page=26)
- **Arbitrarily many tests on one sequence.** For $s=1+j!$, $n=2^s-1$ and $u=(n-1)/3$, the squarefree pentanomial $X^n+(X^u+1)^3$ has exponent gcd 1. Lean proves that for every fixed $k$, all sufficiently large members have no product-one selection of one through $k$ roots, even with repetitions. These members pass the first $k$ exterior-power tests. The proof bounds the field degrees of roots in any short product relation and then excludes those field degrees by the choice of $s$. [Lean proof for the factorial sequence](GF2Sparse/ShortProducts.lean) · [Explicit degree bound](results.pdf#page=19) · [Lean interpolation bound](GF2Sparse/FibreBound.lean)
- **Arbitrarily many tests in power-of-two degrees.** For every fixed $k$, infinitely many powers of two have squarefree, exponent-gcd-one pentanomials passing all $k$ tests. For any fixed $u<v$, a bound on the degrees of roots in a short product relation makes those relations periodic in $s$ for $X^{2^s}+(X^u+1)(X^v+1)$. Choosing $u=1$ and $v=2^t-1$ transfers the trinomial construction to five terms. [Period bound and dyadic construction](results.pdf#page=20)
- **A primitive degree-1024 witness and an exact first failure.** Lean certifies $X^{1024}+X^{85}+X^{51}+X^{34}+1$. For infinitely many $s>10$, the same four lower terms give a squarefree pentanomial of degree $2^s$ that passes ranks 1 through 1023 and fails at rank 1024. [Full-order certificate](GF2Sparse/DyadicExample1024.lean) · [Proof of the first failure](results.pdf#page=21)
- **An irreducible pentanomial of degree $2^{127}-1$ passing 126 tests.** Let $n=2^{127}-1$ and $u=(n-1)/3$. Lean checks Ore's construction for $X^n+X+1$ and proves that cubing its roots gives the irreducible pentanomial $1+X(X^u+1)^3$. The trinomial roots and zero form a 127-dimensional binary vector space. Summing products of linear functions over this space rules out every product-one selection of fewer than 127 roots, even with repetitions. Coprime polynomials evaluated at one root give a multiplicative order greater than $2^{2^{61}}$. Applying the same root-space argument to a published primitive trinomial of Brent and Zimmermann gives an explicit irreducible pentanomial of degree $2^{74,207,281}-1$ passing the first 74,207,280 tests. [Root-product and order bounds](results.pdf#page=21) · [Brent and Zimmermann, Table 1](https://maths-people.anu.edu.au/~brent/pd/rpb266.pdf) · [Lean proof of all 126 tests](GF2Sparse/AdditiveOrbit.lean) · [Lean irreducibility proofs](GF2Sparse/Linearized.lean) · [Ore's construction in Brent, Larvala and Zimmermann](https://maths-people.anu.edu.au/~brent/pd/rpb199.pdf#page=8)
- **Splitting the small-factor tests between two exponents.** For every $n\ge168$, $X^n+X^{167}+X^{105}+X^{62}+1$ is squarefree, has no factor of degree at most five, and has quotient-ring order at least $n^2/334$. For a growing cutoff $B$, the two exponents can cover all fields through degree $B$ at a largest exponent of $L_B^{1/2+o(1)}$, where $L_B=\operatorname{lcm}_{d\le B}(2^d-1)$. This exponent bound is sharp for whole-field covers. Requiring exponent gcd one forces a larger exponent for an explicit sequence of degrees. [Proofs](results.pdf#page=63) · [Lean sieve](GF2Sparse/BalancedSieve.lean) · [Compute exponents](scripts/balance_factor_sieve.py)
- **An all-degree sieve.** Fix $B$ and put $L=\operatorname{lcm}_{1\le d\le B}(2^d-1)$. For every $n>L+2$, the explicit polynomial $X^n+(X^L+1)(X^2+1)$ is squarefree and has no irreducible divisor of degree at most $B$. Allowing all three interior exponents to vary gives at least $LM^3$ distinct squarefree pentanomials with this property whenever $n>6LM$. [Explicit construction](GF2Sparse/LocalFactors.lean) · [Counting proof](GF2Sparse/Many.lean)
- **Odd factor count in every sufficiently large degree.** For each fixed cutoff $B$, at least $c_B n^2\varphi(n)$ degree-$n$ pentanomials are squarefree, avoid every factor of degree at most $B$, and have an odd number of irreducible factors. This is at least a constant times $n^3/\log\log(3n)$ in every degree covered. A positive fraction of all pentanomials pass in prime degrees and in degrees congruent to 1, 2, 4, 6 or 7 modulo eight. Their exponents have gcd one and all fifteen unordered pair sums are distinct. A reducible candidate must have a factor of degree between $B+1$ and $\lfloor n/3\rfloor$. An explicit bound $n^2/(6144L^2)$ already applies for $n>128L$, where $L$ is the least common multiple of $2^d-1$ for $1\le d\le B$. [Totient bound](results.pdf#page=75) · [Prime half-gap construction](results.pdf#page=73) · [Lean projection bound](GF2Sparse/CyclicWeight.lean) · [Constructions and factor checks](scripts/check_parity_families.py) · [Explicit bound](results.pdf#page=3) · [Primitive examples in Lean](GF2Sparse/ParityExamples.lean)
- **Four exponents in arithmetic progression.** In odd degrees $n\ge5$, cubing roots gives a bijection between primitive trinomials and primitive pentanomials containing a four-term arithmetic progression. In even degrees there are no such primitive pentanomials. The forward sampling construction goes back to Kashiwagi and Uchimura. [Lean bijection](GF2Sparse/Progressions.lean) · [Original construction](https://doi.org/10.9746/sicetr1965.18.747)
- **An exact order test by substitution.** Write $N=2^n-1$. A binary polynomial $f$ of positive degree $n$ with $f(0)=1$ is primitive exactly when $f(X^N)$ is irreducible. If $f$ is irreducible and its roots have order $h$, then $f(X^N)$ has exactly $N/h$ distinct irreducible factors, all of degree $nh$. Substitution preserves the number of terms and raises the degree to $nN$. [Lean proof](GF2Sparse/Dilation.lean) · [Butler on substitution](https://doi.org/10.1112/jlms/s1-30.4.480)
- **A norm test for five-term compositions.** Suppose $f=h^4+h+1$ with $h(0)=0$ and $\deg h=m>0$. If every prime divisor of $m$ is 3 or 5, then $f$ is irreducible exactly when $X^{(2^{4m}-1)/15}\equiv h\pmod f$. For every $m$, this congruence supplies the full 3-part and 5-part of the required order. The degree-20 pentanomial $X^{20}+X^{16}+X^5+X+1$ is primitive. In degree 184, $X^{184}+X^{46}+X^4+X+1$ passes the congruence and splits into two degree-92 factors. [Proof for any primitive outer polynomial](results.pdf#page=7) · [Lean proofs of both criteria](GF2Sparse/CompositionNorm.lean) · [Which exponent pairs give five terms](GF2Sparse/FrobeniusPairs.lean) · [Checked examples](GF2Sparse/NormExamples.lean)
- **Order bounds.** In the quotient by $X^n+(X^u+1)(X^v+1)$, the order of $X$ is at least $n^2/(2(u+v))$ for distinct positive $u,v$ with $u+v<n$. When $n$ is a power of two and $d=u+v$, the stronger bound $d^{s(s+1)/2}$ holds modulo every divisor of degree at least $s d^s$, for each positive $s$. At fixed $d$ the bound for the full quotient grows faster than every fixed power of $n$. [Quadratic bound](GF2Sparse/OrderBound.lean) · [Iterate bound](GF2Sparse/IterateOrder.lean)
- **Restrictions on the exponents.** In infinitely many degrees divisible by eight, the three interior exponents of any irreducible pentanomial must have arbitrarily large spread. Lean also proves an obstruction for exponents near a fixed rational grid. The note extends it to finite sets of real slopes and gives a quantitative bound within any prescribed residue class. [Local factors](GF2Sparse/LocalFactors.lean) · [Rational grids](GF2Sparse/Grid.lean)
- **Quadratic lifts.** If an irreducible binary polynomial of weight at most five satisfies $f(X+1)=f(X)$, its degree is 2, 4, 6, 8, or $2^u+4$ for $u\ge3$. In each of the latter degrees only two explicit families, together containing at most $2u$ candidates, survive the support and trace conditions. Primitive examples occur in degrees 2, 4, 6, 8, 12 and 20. For an irreducible outer polynomial $H$ of degree $m$ and $q=2^m$, Lean proves the exact test for $H(X^2+X)$ to be primitive. It requires $H$ to be primitive, its next-to-leading coefficient to equal 1, and $x^{q-1}$ to have order $q+1$ for a root $x$ of the lift. The last condition follows from the first two whenever $q+1$ is prime. [Support classification](results.pdf#page=9) · [Lean trace and order proof](GF2Sparse/QuadraticLift.lean)
- **A determinant test for primitivity.** For a monic degree-$n$ binary polynomial with constant term 1 and companion matrix $C$, primitivity is equivalent to $\det(I+\bigwedge^k C)=1$ for $1\le k\le\lfloor n/2\rfloor$. Each column of $\bigwedge^k C$ has at most four entries for a pentanomial. In every even degree $2m\ge4$, some irreducible polynomial passes all tests below $m$ and fails at $m$. A consequence for sparse primitive polynomials of degree greater than 8 is that a nonidentity binary Möbius symmetry of the roots forces degree $2^u+4$ and one of the quadratic-lift supports or its reciprocal. [Paper proof and matrices](results.pdf#page=11) · [Lean proof of the conjugate-product test](GF2Sparse/ConjugateProducts.lean) · [Independent finite check](scripts/check_exterior.py)
- **Factor parity and reciprocal roots together.** Fix a factor-degree cutoff $B$. In every sufficiently large degree $n$, at least $c_B\varphi(n)$ product pentanomials are squarefree, have an odd number of factors, avoid all factors through degree $B$, and have no mutually inverse roots. Their exponents have gcd one. The bound improves to $c_B n\varphi(n)$ when $n$ is 1, 2, 4, 6 or 7 modulo eight. Dropping the factor-parity condition gives the larger bound in every degree. The construction includes three irreducibles at degree 1229, with smaller taps 255, 295 and 363. [All-degree proof](results.pdf#page=77) · [Larger bound](results.pdf#page=76) · [Lean root criteria](GF2Sparse/ReciprocalSieve.lean) · [Check the discriminants and factorizations](scripts/check_joint_product_sieve.py)
- **An exact test for triples of trinomial roots.** For $T=X^n+X^a+1$ with $\gcd(n,a)=1$, let $D=n^2-na+a^2$. The roots in product-one triples form disjoint three-cycles among the roots of $\gcd(T,X^D-1)$. The only exceptions in this gcd are the two nontrivial cube roots of unity, if present. Thus one polynomial gcd detects both inverse pairs and triples. For every $Q=2^s$, the trinomial $X^{Q+3}+X^Q+1$ and its reciprocal pass all three tests. [Proof and counts](results.pdf#page=13) · [Lean root-order bound](GF2Sparse/TripleRoots.lean) · [Independent exterior-power check](scripts/check_trinomial_triples.py)
- **Five terms passing the first three tests.** For every $Q=2^s$ with $s\ge3$, the squarefree pentanomial $F_Q=X^Q+X^5+X^3+X^2+1$ has no three roots with product 1, even with repetition. Odd substitutions $F_Q(X^m)$ retain this property and give every degree divisible by eight. The examples in degrees 8 and 16 are primitive. [Proof in the note](results.pdf#page=14) · [Lean proof in every multiple of eight](GF2Sparse/DyadicTriples.lean) · [Reproduce the polynomial certificate](scripts/check_dyadic_triples.py)
- **Five terms in degrees near powers of two.** The same lower terms $X^5+X^3+X^2+1$ pass the first three tests in every degree $2^s+7$ and $2^s+9$. For eleven offsets $d$ in total, the exact criterion in degree $n=2^s+d>5$ is $n\not\equiv0,5\pmod7$. Lean verifies the full primitive order in degree $265=2^8+9$. [Proof and offsets](results.pdf#page=15) · [Degree-265 primitive witness](GF2Sparse/ShiftedExample.lean) · [Reproduce the classification](scripts/check_shifted_triples.py)
- **Four exterior powers with one gcd.** Let $D$ be the squarefree polynomial whose roots are all pair products, including squares. The first four tests pass exactly when $D$ is coprime to its reciprocal. The algorithm only needs powers of $X$ modulo the original polynomial. The dyadic five-term construction passes rank four in degrees $8,16,32,64,128,256,512,1024$. Its first failure in degrees 32, 64, 128 and 1024 is rank five. [Proof and algorithm](results.pdf#page=16) · [Lean lemma on products with repetition](GF2Sparse/RootProducts.lean) · [Lean quintic factor criterion](GF2Sparse/DyadicFactors.lean) · [Reproduce the fourth test](scripts/check_pair_products.py)
- **The fourth test is periodic in the dyadic exponent.** Every root in a product-one quartet of $F_{2^s}$ has degree at most 62,500. Consequently the fourth test depends only on $s$ modulo $\operatorname{lcm}(1,\ldots,62500)$. This gives infinite progressions of exponent-gcd-one pentanomials passing the first four tests and an infinite progression whose first failure is rank five. [Proof of periodicity](results.pdf#page=17) · [Exact finite-field calculation](scripts/check_quartic_period.py)
- **Four tests in every multiple of eight.** No four roots of $F_{2^s}=X^{2^s}+X^5+X^3+X^2+1$ have product 1, even allowing repetitions. For $s\ge3$ and odd $m$, every $F_{2^s}(X^m)$ passes the first four tests. The first failure is exactly rank five when $s\equiv0,1,2\pmod5$. Three binary resultants leave just four quartics to rule out. [Proof in the note](results.pdf#page=18) · [Exact resultant calculation](scripts/check_dyadic_quartets.py)

The Lean target for an all-degree proof is `GF2Sparse.Conjecture`. The gap is to force exact order $2^n-1$ for at least one candidate in each degree. That order implies irreducibility by exhausting all nonzero residues of the quotient. [Formal statement and order criterion](GF2Sparse/Basic.lean)

The equivalent Ore target asks for a constant-one irreducible of degree $2^s-1$ for every $s>0$, using at most five exponents of the form $2^i-1$. The Lean theorem `conjecture_iff_sparseOreIrreducible` converts a proof of this target directly into the original conjecture. [Formal equivalence](GF2Sparse/OreConjecture.lean)

## Contributing

The 20 pentanomials in the large-degree table, through degree 41,521, all have offline proofs of primitivity. NTL and FLINT independently verified all 108 factor-index powers. In degree 35,737 the two archived PRIMO chains prove the 702-digit and 9,927-digit primes. The degree-22,327 row uses the 6,616-digit prime already verified in the subfield calculation. [Large-degree table](data/mers-project-large-orders.json) · [Verifier](scripts/check_mers_project_orders.py)

Choose a degree and run the command below for the full check. It verifies the integer certificates with PARI/GP and the polynomial powers with FLINT, then reports the root order. The cache retains each downloaded chain after it passes verification. Add `--defer-largest` to reproduce the polynomial checks and all smaller prime proofs offline. Use `--powers-only` for just the factor product and polynomial powers.

```bash
uv run --no-project --with python-flint==0.9.0 python scripts/check_mers_project_orders.py \
  --table data/mers-project-large-orders.json --degree 35737
```

In degrees 25,243, 25,933, 28,381, 28,771, 32,531 and 35,339, every trinomial is reducible. A primitive witness of weight at most five in any of these degrees must therefore have five terms. The proof uses Swan's theorem and explicit divisors of degree at most eight before substitution. [Proof](results.pdf#page=310)

In degree 41,681, all seven irreducible trinomials up to reciprocation and the pentanomial with taps $(5535,11070,36146)$ are primitive. The 1,398-record certificate proves the 12,495-digit fourth factor prime, completing the order proof and giving minimum weight three. In degree 53,381, every trinomial is reducible, and the pentanomial with interior taps $(11562,23124,41819)$ passes all four factor-index tests. The three smaller factors are proven primes. The archived 16,008-digit cofactor certificate is the remaining integer proof for minimum weight five. [Supports and order factors](data/mers-project-extension-orders.json) · [Proof and trinomial lists](results.pdf#page=363) · [Degree 41,681 certificate](https://factordb.com/cert/1100000000776586446) · [Degree 53,381 certificate](https://factordb.com/cert/1100000000888500230)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_mers_project_orders.py \
  --table data/mers-project-extension-orders.json --degree 41681 --degree 53381
~~~

The degree-1229 elliptic pentanomial with interior taps $(136,683,819)$ and its reciprocal share one order. Seven projected logarithms of relative degrees $2,6,13,15,15,16,17$ determine it. The smallest input is the degree-eight binary mask `0x15f`. The other six can be expanded into smaller factors. The combined task then has 4,404 logarithms, all of relative degree at most 15. The checker exports the targets and coefficients. Add `--logs answers.csv` with columns `mask,exponent` to verify any subset. A complete set gives the exact index, and index one proves both pentanomials primitive. [Seven inputs](data/degree-1229-elliptic-split-seven.json) · [Proof](results.pdf#page=187)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_power_images.py --split elliptic-seven
~~~

Four equations give alternatives for the degree-eight input `0x15f`. One uses five other degree-eight logarithms. A second uses one degree-eight, one degree-12 and 66 degree-16 logarithms. Two further equations each need only two logarithms, of binary degrees 84 and 473 or 117 and 377. The four lists of unknowns are disjoint. Each command exports the exact coefficients and accepts the same answer CSV. [Five- and 68-input equations](results.pdf#page=190) · [Two-input equations](results.pdf#page=205)

There is a limit to the original degree-five substitution. Even given the other six inputs for the pentanomial, the reference tables, every iteration of the substitution and all linear Hermitian equations at $q=1024$ allow every possible value for this one logarithm. The two-input equations each supply an independent constraint on that system. The logarithm itself is still open. [Proof](results.pdf#page=205) · [Reproduce the branch and rank checks](scripts/check_1229_octic_obstruction.py) · [Lean algebra](GF2Sparse/QuinticIsogeny.lean)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --octic isogeny --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --octic frobenius --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --octic binary-32 --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --octic binary-128 --json
~~~

An alternative quotient uses eight logarithms of relative degrees $3,3,6,7,9,11,18,19$. Its two cubic inputs reduce to 299 quadratic logarithms. Lowering all eight gives 5,391 inputs of binary degree at most 190, each with smaller relative degree or the same relative degree and smaller binary degree than its parent. [Eight inputs](data/degree-1229-elliptic-split-eight.json) · [Pencil certificates](data/degree-1229-elliptic-pencils.json)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_power_images.py --split elliptic-eight
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --eight
~~~

An independent quotient uses ten logarithms of relative degrees $7,9,11,12,13,14,17,19,19,20$. Export it with `--split elliptic`. [Ten inputs](data/degree-1229-elliptic-split.json)

The ten inputs also have a decomposition into 5,064 smaller logarithms. Every remaining factor has relative degree at most 13. To work on one of the original factors, use `--target 0x7d397`, for example. Add `--json` to export the masks and coefficients, or `--logs answers.csv` to check partial answers. [Pencil certificates](data/degree-1229-elliptic-pencils.json) · [Descent checker](scripts/check_1229_elliptic_descent.py)

~~~sh
g++ -O3 -std=c++17 scripts/degree_1229_dyadic.cpp -lntl -lgmp -o /tmp/gf2-elliptic-dyadic
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --lower-seven --backend /tmp/gf2-elliptic-dyadic
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --lower-eight --backend /tmp/gf2-elliptic-dyadic
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --backend /tmp/gf2-elliptic-dyadic
~~~

All 3,087 degree-130 and degree-150 factors in the seven-input expansion have a further reduction. Their new bounds over $\mathbb F_{2^{20}}$ are 12 and 14 respectively. The other factors in the expansion have relative degree at most nine. These commands check coverage and all 3,087 certificates, then export one explicit logarithm equation. [Pencil coefficients](data/degree-1229-elliptic-real-pencils.json.gz) · [Verification](scripts/check_1229_elliptic_real_pencils.py) · [Determinant search](scripts/find_1229_real_pencil.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --lower-seven --backend /tmp/gf2-elliptic-dyadic --json > /tmp/gf2-elliptic-seven.json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_real_pencils.py --frontier /tmp/gf2-elliptic-seven.json --jobs 4
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_real_pencils.py --expand 0x400412f00f4ddc3dfcdb785dea7b13943256ed
~~~

The ten-input route reaches relative degree 12 and binary degree 240. The first command reconstructs the original expansion. The second checks its 23 degree-260 halvings and all 23,667 subsequent real pencils. Use `--ten --expand MASK` to export one equation and `--logs answers.csv` to check any known exponents for it. [Complete certificate](data/degree-1229-elliptic-ten-real-pencils.json.gz)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_descent.py --backend /tmp/gf2-elliptic-dyadic --json > /tmp/gf2-elliptic-ten.json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_elliptic_real_pencils.py --ten --frontier /tmp/gf2-elliptic-ten.json --backend /tmp/gf2-elliptic-dyadic --jobs 4
~~~

Four degree-1229 candidates share one discrete logarithm task. The JSON gives the binary field modulus, a base of order $C$, and the target as hexadecimal polynomial masks with bit $i$ as the coefficient of $X^i$. Find an integer $0\le e<C$ with $\mathrm{base}^e=\mathrm{target}$ in that field. Replace `--task` with `--log E` to check an answer. The checker computes the exact index of all four roots, and an index of one proves all four primitive. [Download the task](data/degree-1229-seventh-power-task.json)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_power_images.py --task
~~~

Every irreducible degree-1229 pentanomial has also had its roots compared with 1,304,685 elements of known order. Across all signed powers with absolute exponent below 36,871, none gives a Frobenius conjugate of a reference element. Among the pentanomials themselves, the seventh-power pair above and its reciprocal are the only transfers by an odd positive power greater than one in that range. Both native and portable builds reproduce the 11,783,025,210 oriented power checks. [Proof](results.pdf#page=200) · [Trace sieve and exact checks](scripts/census_1229_power_transfers.cpp) · [Census driver](scripts/check_1229_power_transfers.py)

Allowing powers on both sides, $r^u=s^v$ for $0<|u|,|v|\le1229$, still gives only the seventh-power pair after squaring, inversion and cancellation. The union of these powers and their conjugates across the 639,144 surviving pentanomials has exactly 483,087,188,936 elements. If 1229 is a counterexample, at least 32,205,913,046 of these elements must lie in one proper subgroup. [Rational-power census](results.pdf#page=205)

~~~sh
g++ -O3 -std=c++17 -march=native -fopenmp scripts/census_1229_power_transfers.cpp -lntl -o /tmp/gf2-power-transfers
uv run --no-project --with numpy --with python-flint==0.9.0 python scripts/check_1229_power_transfers.py /tmp/gf2-power-transfers
uv run --no-project --with numpy --with python-flint==0.9.0 python scripts/check_1229_power_transfers.py /tmp/gf2-power-transfers --sparse-ratios
~~~

A verified split uses six factor logarithms, of degrees 5, 7, 9, 11, 19, and 21 over $\mathbb F_{2^{20}}$. The task file includes the base, each binary polynomial mask and its signed coefficient, the known offset, and an irreducible relative factor for each mask. Add `--logs answers.csv` to check any subset, using a CSV with columns `mask,exponent`. A complete submission gives the common index. A second six-factor split has relative degrees 9, 11, 11, 13, 20, and 20. Select it with `--split degree-20`. The earlier nine-factor certificate is available with `--split 9`. [Six tasks including a quintic](data/degree-1229-seventh-power-split-six.json) · [Six tasks through degree 20](data/degree-1229-seventh-power-degree20.json) · [Nine-factor alternative](data/degree-1229-seventh-power-split.json) · [Field identities](results.pdf#page=158)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_power_images.py --split 6
~~~

The degree-20 split also gives a task for the common root order with **2,144 logarithms of relative degree at most eleven**. Its 2,058 degree-ten factors each have a verified split into factors of relative degree at most five. The quintic in the other six-factor split gives a choice of 275 quadratics and 149 cubics, or 76,921 quadratics. Add `--json` to export a task and `--logs answers.csv` to verify partial answers. Select a cubic by passing its binary mask to `--task`. [Factor identities](results.pdf#page=161) · [Cubic pencils](data/degree-1229-seventh-power-cubic-pencils.json) · [Degree-halving indices](data/degree-1229-seventh-power-halvings.json.gz)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py --task quintic
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py --task quintic --quadratics
~~~

Build the NTL checker to replay the 2,058 indices. To expand a single degree-ten factor, supply the same backend and pass its binary mask to `--task`.

~~~sh
g++ -O3 -std=c++17 scripts/degree_1229_dyadic.cpp -lntl -o /tmp/gf2-dyadic
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py --audit-branches --backend /tmp/gf2-dyadic
~~~

The interpolated root task has 4,278 factors. Of these, 2,438 have individual certificates reducing them to relative degree at most five. The remaining larger inputs consist of 147 of degree seven, 49 of degree nine and one of degree eleven. The command below lists all 197 with their binary masks and degrees. Add `--real-pencils` to the branch audit above to replay all 2,438 certificates. [Interpolation proof](results.pdf#page=163) · [Three interpolants and the additional indices](data/degree-1229-seventh-power-real-pencils.json) · [Reproduce the odd-degree interpolants by index](scripts/find_1229_hermitian_descent.py)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py --real-pencils --json |
  jq -r '.remaining[] | select(.relative_degree > 5 and .halving_index == null) | [.mask_hex, .relative_degree] | @tsv'
~~~

A degree-ten pencil over $\mathbb F_{2^{20}}$ eliminates the last degree-eleven input. The resulting root task has 6,278 logarithms. Applying its 2,840 indexed halvings leaves 296 logarithms of degree seven and 169 of degree nine above degree five. A contributor can export this task, verify one factor by its mask, or reconstruct the degree-ten pencil at search plane 1,864. [Proof](results.pdf#page=165) · [Pencil and halving indices](data/degree-1229-seventh-power-decic.json) · [Finder](scripts/find_1229_trace_pencil.py)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py --decic-pencil --json
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_seventh_descent.py --decic-pencil --audit-branches --backend /tmp/gf2-dyadic
uv run --no-project --with numpy --with python-flint==0.9.0 python scripts/find_1229_trace_pencil.py 0x151b5b924e9b7af9a64c4bc701f2cd3b7fad0fa96c74a542124af1f9 --start 1864
~~~

To reproduce the six-factor discovery, build the NTL finder and search index 6618. The three arguments after `--smooth` specify the maximum relative factor degree, the starting index, and the number of indices. Different computers can search disjoint intervals. Each output line is a quotient that the Python checker can certify on its own. [Finder](scripts/find_1229_known_offset.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/find_1229_known_offset.cpp -lntl -o /tmp/gf2-offset
uv run --no-project --with python-flint==0.9.0 python scripts/prepare_1229_single_log.py --taps 166 249 332 |
  jq -r '.model_modulus_hex, .sparse_root_in_model_hex' |
  /tmp/gf2-offset --smooth 21 6618 1 > /tmp/gf2-split-six.json
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_power_images.py --check-split /tmp/gf2-split-six.json
~~~

To work directly on either cubic value, choose `--v 256` or `--v 400`. The command exports the field modulus, the projected primitive base, the projected cubic and its two linear components. Submit either a single exponent with `--cubic-log` or both exponents with `--linear-logs` to verify the sparse root's exact index. [Rational coordinate checker](scripts/check_1229_rational_cubics.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_rational_cubics.py --v 400
~~~

To verify either quaternary logarithm table by direct powering, compile the NTL backend and select `--q 512` or `--q 1024`. Add `--orders` to reproduce the selected table’s full order and weight census. The last command exports the task for the four seventh-power candidates using the table's primitive normalization. For the original two candidates use `--task product` or `--task seroussi`. Supply `--log E` to verify a submitted exponent and obtain the sparse root's exact index. [Model checker](scripts/check_1229_quaternary_models.py) · [Independent binary-field verification](scripts/degree_1229_quaternary_logs.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/degree_1229_quaternary_logs.cpp -lntl -o /tmp/gf2-quaternary-logs
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_models.py --verify-logs /tmp/gf2-quaternary-logs
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_models.py --q 1024 --verify-logs /tmp/gf2-quaternary-logs
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_models.py --model 21149 --task product
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_models.py --task seventh-power --norm-base
~~~

To verify the larger system's full-rank recurrence from the archived moments, run the first command below. To verify that those moments come from the published circle equations, use the next three commands to rebuild the matrix and its sequence. The checker verifies the matrix digest. The uncompressed sequence has SHA-256 `a4def8fc75eaf20affd87f693bd5e14b6d29b2373169178b3a481dec342cd57a`. [Circle parameters](data/degree-1229-q1024-quaternary-pencils.bin.gz) · [Verification digests](data/degree-1229-q1024-quaternary-rank.json)

~~~sh
uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_pencils.py --q 1024 --rank
uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_pencils.py --q 1024 --rebuild --matrix /tmp/gf2-q1024-quaternary.bin
g++ -O3 -march=native -fopenmp scripts/wiedemann_943.cpp -o /tmp/gf2-wiedemann
/tmp/gf2-wiedemann --phase1 /tmp/gf2-q1024-quaternary.bin /tmp/gf2-q1024-quaternary.seq 12
sha256sum /tmp/gf2-q1024-quaternary.seq
~~~

To reproduce the linear system, rebuild its circle census and coefficient matrix. The solver computes the normalized exponents and checks the rank modulo the unfactored cofactor. The last command compares its output with the published table and checks every circle equation. [Pencil census and matrix builder](scripts/check_1229_quaternary_pencils.py) · [Wiedemann solver](scripts/wiedemann_943.cpp)

~~~sh
uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_pencils.py --rebuild --matrix /tmp/gf2-q512.bin
g++ -O3 -march=native -fopenmp scripts/wiedemann_943.cpp -o /tmp/gf2-wiedemann
/tmp/gf2-wiedemann --phase1 /tmp/gf2-q512.bin /tmp/gf2-q512.seq 12
uv run --no-project --with python-flint==0.9.0 python scripts/phase2_minpoly.py --seq /tmp/gf2-q512.seq --out /tmp/gf2-q512.poly --certify-rank
/tmp/gf2-wiedemann --phase3 /tmp/gf2-q512.bin /tmp/gf2-q512.poly /tmp/gf2-q512.sol 12
uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_pencils.py --solution /tmp/gf2-q512.sol --check-logs
~~~

To work in a model with a linear cofactor, export a sparse-root task over $\mathbb F_{1024}$. The task packs polynomial coefficients into ten-bit groups, starting with the constant coefficient. Find $e$ with $\mathtt{base}^e=\mathtt{target}$ modulo the relative modulus. This is the same forward exponent as in the certified binary model. The final command checks a submitted value and computes the sparse root's exact index. [Model verifier](scripts/check_1229_height_two.py) · [Model search](scripts/find_1229_height_two.cpp)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two.py --jobs 4
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two.py --model 3 1019 --task product
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/prepare_1229_single_log.py --candidate product --forward-log DECIMAL
~~~

For the linear-norm system, list the split pencils in one model and export a signed equation by its ten-bit parameters. The equation's labels are twenty-bit masks for constants in $\mathbb F_{2^{20}}$, using the smaller of the two conjugate masks. Pass any label to `--linear` to export its projected field element, subgroup base and modulus. The first command independently checks the counts in all five models. [Relation checker](scripts/check_1229_height_two_relations.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two_relations.py --audit
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two_relations.py --model 3 1019 --parameters > split-pencils.csv
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two_relations.py --model 3 1019 --pencil 0 1
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two.py --model 3 1019 --linear 0x2
~~~

To reduce an individual linear norm to generators, use its twenty-bit label. The coefficients in the output are full exponents modulo $2^{1229}-1$. They also apply to the projected logarithms. The example checks the identity $N(x)=N(x+\mathtt{0xc2efe})^{-2048}$ in the specified field. Use `--leaves` to list every generator. [Pullback checker](scripts/check_1229_height_two_pullback.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_height_two_pullback.py --model 6 246 --reduce 0 --field-check
~~~

To check whether the linear pencil method solves a quadratic, look up its binary mask. Add the NTL backend to obtain a directly verified `mask,exponent` CSV row. Use `--task task.json` to check a contributor task or `--rebuild` to repeat the complete census. [Census checker](scripts/check_1229_terminal_census.py) · [Finite-field arithmetic and factorization](scripts/degree_1229_terminal_census.cpp)

~~~sh
g++ -O3 -std=c++17 scripts/degree_1229_terminal_census.cpp -lntl -o /tmp/gf2-terminal
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_terminal_census.py --backend /tmp/gf2-terminal --mask 0x1025e3100bf
~~~

Use `--export-all logs.csv` with the same backend to reconstruct all 1,214,007 exponents. The following commands also check every exponent, exact order and minimal-polynomial weight in the original binary field. The `--fibers` audit counts the solved quadratic fibers available to a second pencil.

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/census_1229_factor_base.cpp -lntl -o /tmp/gf2-orders
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_terminal_census.py --backend /tmp/gf2-terminal --power-backend /tmp/gf2-orders --orders
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_terminal_census.py --backend /tmp/gf2-terminal --fibers
~~~

To work on a single branch of the degree-1229 problem, export a degree-16 task with `--halve --json`, then pass any of its remaining masks to the NTL checker. It produces a smaller task with the same `mask,exponent` CSV submission format. The product branch in the example below already extends to quadratics. Adding `--census` to the sample command enumerates the linear Hermitian pencils for all 1,058,817 quadratic masks. [Degree-halving checker](scripts/check_1229_dyadic.py) · [NTL backend](scripts/degree_1229_dyadic.cpp) · [Sample branch certificates](data/degree-1229-dyadic-sample.json.gz)

~~~sh
g++ -O3 -std=c++17 scripts/degree_1229_dyadic.cpp -lntl -o /tmp/gf2-dyadic
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task product --halve --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_dyadic.py --backend /tmp/gf2-dyadic --candidate product
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_dyadic.py --backend /tmp/gf2-dyadic --parent 0x10012a066403a92ecc429020b41280eced2ba647f --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_dyadic.py --backend /tmp/gf2-dyadic --sample
~~~

Each degree-16 parent also has a compact index for every degree-eight child. Use `--candidate product --depth 3` or `--candidate seroussi --depth 3` to replay an entire candidate. The first command below checks all 1,029 degree-eight pencils under a single parent. The second reconstructs the selected pencil, multiplies out its unprojected identity in the original binary field, and exports its quartic logarithms. [All 4,235,364 indices](data/degree-1229-dyadic-level3.bin.gz)

~~~sh
parent=0x100025fa5082778e43947101d9faeb698dae872213daf86a5f4905d7971915636b233741c429cfdf7
child=0x10012a066403a92ecc429020b41280eced2ba647f
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_dyadic.py --backend /tmp/gf2-dyadic --parent "$parent" --depth 3
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_dyadic.py --backend /tmp/gf2-dyadic --parent "$parent" --child "$child" --json
~~~

To certify the Seroussi pentanomial using one logarithm, solve the single row in the degree-57 task. The product candidate has a degree-58 task in the same field. Use the binary polynomial marked `mask_hex` in `remaining` and find $e$ satisfying $(x^K)^e=P(x)^K$. The checker accepts a CSV with header `mask,exponent`, verifies the exponent by powering in the field, and computes the original sparse root's exact index. Index one certifies primitivity. [Seroussi task](data/degree-1229-seroussi-known-offset-task.json) · [Product task](data/degree-1229-product-known-offset-task.json)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi --norm-form known-offset --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi --norm-form known-offset --logs my-logs.csv
~~~

To search for a smaller single-factor task, build the NTL finder. Its five arguments give the maximum binary numerator degree, maximum denominator degree, maximum relative degree of the remaining factor, starting index and number of indices. Disjoint index intervals can run on different computers. The example reproduces the Seroussi witness at index 811. For the product witness use the product input and index 77922. The final command verifies a discovery and exports it as a contributor task. [Finder](scripts/find_1229_known_offset.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/find_1229_known_offset.cpp -lntl -o /tmp/gf2-offset
jq -r '.model_modulus_hex, .sparse_root_in_model_hex' data/degree-1229-single-log-seroussi.json | /tmp/gf2-offset 1200 40 58 811 1 > /tmp/gf2-offset.json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi --offset-certificate /tmp/gf2-offset.json --json
~~~

For a two-person split of the degree-1229 problem, each contributor can take one irreducible from `--norm-form pair31`. Use `pair32` for two power-of-two degrees, or `single62` or `single64` for one factor. The coefficients in each JSON export convert the submitted exponents directly to the logarithm of the original pentanomial root. Completing any one form gives its exact group index. Both candidate names, `product` and `seroussi`, work in all four forms. [Irreducible factors over the constant field](data/degree-1229-q1024-norm-quotients.json) · [Proof and scope of the minimum](results.pdf#page=124)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task product --norm-form pair31 --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task product --norm-form pair31 --logs my-logs.csv
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_norm_height.py
~~~

To work on one factor of a degree-1229 pentanomial, pick a row from either eleven-factor task. For its binary polynomial $P$, find $e$ with $(x^K)^e=P(x)^K$ modulo the supplied field polynomial. Each file gives $x^K$, $K$, $C$, and every remaining coefficient. The checker takes a CSV with header `mask,exponent` and any subset of the rows. The mask can be hexadecimal or decimal. It verifies each exponent, then removes that row and updates the known part of the target logarithm. [Seroussi rows](data/degree-1229-seroussi-descent-task.json) · [Product rows](data/degree-1229-product-descent-task.json)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi --logs my-logs.csv
~~~

For a smaller starting problem, the Seroussi factor with mask `0xd3` has a further decomposition into 44 logarithms of relative degree at most three. Run the same command with `--task seroussi-0xd3 --json` to get those rows. The product factors `0xbf` and `0x35d5` have analogous tasks called `product-0xbf` and `product-0x35d5`. Running the checker without arguments verifies all decompositions. [Norm identities](results.pdf#page=120)

To work entirely with quadratics, start with one of the 126 rows for the product factor `0x93f1`. Each row can be submitted independently with `--logs my-logs.csv` on the same task. The degree-seven Seroussi task also has a two-row version for contributors working on higher degrees. The last command below reconstructs one of the three solved exponents from known linear logarithms. [126 product rows, compressed JSON](data/degree-1229-product-93f1-quadratics.json.gz) · [534 Seroussi rows, compressed JSON](data/degree-1229-seroussi-144f-quadratics.json.gz) · [Hermitian pencil certificates](data/degree-1229-hermitian-descents.json) · [Pencil search](scripts/find_1229_hermitian_descent.py) · [Derivation](results.pdf#page=121)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task cubic-0x93f1 --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi-0xd3 --expand-cubics --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task seroussi-0xd3-binomial --json
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_log_descent.py --task quadratic-0x17fa03989a9 --terminal-orders
~~~

The search below enumerates the determinant cubic for the product target. It finds 1,080 projective rank-two matrices, 113 of which leave only factors of degree at most two on the substitution side. Replacing the mask with `0x144f` checks the Seroussi cubic. For a quadratic mask, the same command solves the linear equations for a direct reduction to the original factor base. All 126 product rows give four independent equations, which rules out a single Hermitian circle for every one of them. Among the Seroussi rows, five verified relations give exact sums of two quadratic logarithms. For example, the task `quadratic-0x13f` expresses the octic mask `0x13f` using the single octic mask `0x1c3` and a known offset.

~~~sh
uv run --no-project --with sympy --with numpy --with python-flint==0.9.0 python scripts/find_1229_hermitian_descent.py 0x93f1
uv run --no-project --with sympy --with numpy --with python-flint==0.9.0 python scripts/find_1229_hermitian_descent.py --audit-quadratics data/degree-1229-product-93f1-quadratics.json.gz
uv run --no-project --with sympy --with numpy --with python-flint==0.9.0 python scripts/find_1229_hermitian_descent.py --audit-cubics
~~~

Two degree-1229 logarithm problems are ready to download. The product candidate has interior taps $27,50,77$, and the Seroussi candidate has $2,6,15$. Each file gives a base $b$ and target $t$ in the same certified $q=1024$ field. A solution to $b^d=t$ gives the exact index $\gcd(d,C)$ of that sparse root, where $C$ is the supplied cofactor. An index of one certifies the pentanomial. [Product candidate input](data/degree-1229-single-log-product.json) · [Seroussi candidate input](data/degree-1229-single-log-seroussi.json)

To reconstruct the product candidate input, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/prepare_1229_single_log.py --candidate product
~~~

Append `--forward-log DECIMAL` to check a computed $d$. Use `--reverse-log DECIMAL` for an exponent satisfying $t^e=b$. The same command accepts `--candidate seroussi` or `--taps A B C` for three increasing interior exponents. It checks irreducibility and all four known-prime order tests before printing a task.

For every sufficiently large odd $n$ and fixed cutoff $B$, there are at least $c_B n\varphi(n)$ two-odd-tap supports that pass the squarefreeness, inverse-pair and small-factor tests in both degrees $n$ and $n+2(u+v)$. Exactly one of those degrees has an odd factor count for that support. As a consequence, a positive proportion of odd degrees have at least $c_B n^2$ supports passing all four tests together. Lean verifies the cyclic coprimality test for squarefreeness. [Proof](results.pdf#page=90) · [Lean criterion](GF2Sparse/ReciprocalSieve.lean) · [Paired-degree checker](scripts/check_odd_tap_parity.py)

In odd degree $n$, a single inverse modulo $Y^{(u+v)/2}+1$ determines whether $X^n+(1+X^u)(1+X^v)$ is squarefree and, if so, the parity of its factor count when both taps are odd. If $(u+v)/2$ is odd, raising the degree by $2(u+v)$ reverses that parity. Together with the even-tap formulas, this covers every product support in odd degree. The checker agrees with direct factorization on all 21,327 two-odd-tap supports through degree 128. [Proof](results.pdf#page=88) · [Cyclic inverse checker](scripts/check_odd_tap_parity.py)

At degree 1229, 51,671 of the 376,382 product pentanomials are squarefree with an odd factor count. Of these, 25,406 also avoid inverse pairs and factors through degree five. The two-odd-tap family supplies 44,187 and 21,961 of these counts, respectively, and contains 393 of the 449 irreducibles. Independent full factorizations agree with the parity predictions on every support. [Six-degree counts](results.pdf#page=90) · [Irreducible supports](data/open-product-irreducibles.csv)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_odd_tap_parity.py --degree 1229 --factor --joint --jobs 8
~~~

The divisor enumerator lists every odd-factor product pentanomial with an even tap in degrees congruent to 3 or 5 modulo eight. Its running time is $n^{1+o(1)}$. At degree 100,003 it finds 1,341,358 candidates among 1,875,025,000 supports. The exhaustive C++ scan produces the same sorted CSV. [Enumeration proof](results.pdf#page=87) · [Divisor enumerator](scripts/enumerate_even_tap_parity.py) · [Exhaustive comparison](scripts/check_even_tap_enumeration.cpp)

~~~sh
python3 scripts/enumerate_even_tap_parity.py 100003 --list > /tmp/gf2-divisors-100003.csv
g++ -O3 -std=c++17 -fopenmp scripts/check_even_tap_enumeration.cpp -o /tmp/gf2-even-tap-check
OMP_NUM_THREADS=8 /tmp/gf2-even-tap-check 100003 > /tmp/gf2-direct-100003.csv
cmp /tmp/gf2-divisors-100003.csv /tmp/gf2-direct-100003.csv
~~~

In odd degrees congruent to 3 or 5 modulo eight, among the $\Theta(n^2)$ product pentanomials with at least one even tap, only $n^{1+o(1)}$ have an odd number of factors. At degree 1229, parity rules exclude 274,649 of the 282,133 such supports. The remaining 7,484 contain 56 irreducibles, all of which pass the known order tests. Of the 449 irreducibles in the full product census, 393 have two odd taps. For prime degrees in these two classes, at least $c_B n\log n$ supports with an odd smaller tap pass the simultaneous sieve at each fixed cutoff $B$. [All even-tap formulas and six-degree counts](results.pdf#page=85) · [Odd smaller tap](results.pdf#page=83) · [Counting proof](results.pdf#page=82) · [Independent factorization checker](scripts/check_product_parity_sector.py)

FLINT independently factored all 282,133 degree-1229 supports in that calculation and agreed on every parity and every irreducible. The four disjoint sector values for distributing the replay across computers are `four`, `two-smaller`, `two-larger` and `both-even`. The combined replay is

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_parity_sector.py --degree 1229 --sector even-tap --factor --jobs 16
~~~

The simultaneous sieve also works with a cutoff that grows with the degree. For every fixed $0<\epsilon<1$, at least $n^{1-o(1)}$ candidates in each sufficiently large degree avoid every factor through $(1-\epsilon)\log\log n$, have odd factor count, and pass the inverse-root test. When $8\nmid n$, the cutoff can reach $\frac1{32}\sqrt{\log n/\log\log n}$. The proof uses natural logarithms. [Proof and parameters](results.pdf#page=80) · [Verify the seven classes with --gap-slices](scripts/check_joint_product_sieve.py)

For degrees divisible by eight, the simultaneous sieve has an exact factor-parity table. For $q=8$, its 63 exponent classes split into 21 with odd factor count, 21 with even count and 21 with repeated roots. Negating a squarefree class reverses its parity for every power of two $q\ge8$. The checker compares all 318 classes at $q=8,16$ with full factorizations. Lean proves the constructed examples in degrees 56 and 152 are primitive. [Parity formula](results.pdf#page=79) · [Lean certificates](GF2Sparse/ReciprocalSieve.lean) · [Reproduce with the --residues option](scripts/check_joint_product_sieve.py)

The cyclic inverse construction gives 21 certified primitive pentanomials, including $X^{2203}+X^{2117}+X^{656}+X^{168}+1$. Lean checks that example. The Python checker verifies all 21 full powers and 375 prime-index powers with `--primitive-examples`. [Witnesses](data/cyclic-parity-primitive.csv) · [Lean certificate](GF2Sparse/ParityExamples.lean) · [Verification code](scripts/check_cyclic_trinomial_parity.py)

For pentanomials with two odd exponents and all even exponents divisible by eight, a single coefficient of a cyclic polynomial inverse gives the factor parity whenever the half-gap between the odd exponents is odd. At degree 1229 this identifies 638,918 squarefree candidates with odd factor count among 1,290,708 supports with prime half-gap. The complete census finds 3,899 irreducibles in this family. All pass the five order tests, including the example with taps 88, 376 and 1155. [Discriminant proof](results.pdf#page=72) · [Parity and census checker](scripts/check_cyclic_trinomial_parity.py)

An exponent test rules out 38,390,964 pentanomials at degree 1229. If the three interior exponents are all 0 or 1 modulo four, the polynomial is reducible. More generally, a binary polynomial with constant term one supported in classes $\{0,s\}$ modulo four, with $s$ odd, is reducible in every degree congruent to 0, 3 or 5 modulo eight. [Proof](results.pdf#page=69) · [Discriminant and factorization check](scripts/check_two_residue_parity.py)

In degree 1229, every primitive witness of weight at most five must have exactly five terms. Proper factors exclude all 1,228 trinomials and, by power sampling, 1,866 pentanomial supports including every four-term arithmetic progression. The `--trinomials` option of the degree-1229 checker replays the complete exclusion. [Factor table](data/degree-1229-trinomial-factors.csv) · [Lean exclusion](GF2Sparse/Trinomial1229.lean) · [Proof](results.pdf#page=53)

Finding 16 degree-1229 survivors whose pairwise quotients each have full order after projection to the cofactor group would certify at least one primitive pentanomial. [Counting argument](results.pdf#page=197) · [Lean subgroup-cover proof](GF2Sparse/SubgroupCover.lean)

The following commands reproduce the degree-10 quadratic example and the 8,193 positions on each of the three degree-1229 sequences. The checker verifies the seed embeddings, the four known tests and the minimal-polynomial weights.

~~~sh
g++ -O3 -std=c++17 scripts/census_1229_parameter_weights.cpp -lntl -lgmp -o /tmp/gf2-parameter-weights
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_sparse_parameter_codes.py /tmp/gf2-parameter-weights
~~~

Every degree-1229 irreducible of weight below 521 has a root order divisible by a prime greater than 818,085,338,814,611,457. In the subgroup generated by the two primes below that bound, the minimum weights at orders 36,871, 46,703 and 1,721,986,313 are 605, 579 and 521. An independent check using field traces rules out weight five in all 1,401,128 conjugacy classes. [Counts and minimum witnesses](data/degree-1229-small-subgroup-weights.csv) · [Proof](results.pdf#page=65)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/check_1229_subgroup_weights.cpp -lntl -lgmp -o /tmp/gf2-1229-weights
OMP_NUM_THREADS=16 /tmp/gf2-1229-weights
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_subgroup_traces.py
~~~

To verify the 75 Frobenius curves and repeat the scan of every degree-1229 pentanomial, run

~~~sh
c++ -O3 -std=c++17 -fopenmp scripts/census_1229_frobenius_curves.cpp -lntl -lgmp -o /tmp/gf2-frobenius-curves
uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_frobenius_curves.py --census /tmp/gf2-frobenius-curves --jobs 6
~~~

The degree-1229 search checked 153,940,238 reciprocal pairs in 614 ranges by smallest tap. NTL tested all 31,863,827 sieve survivors directly and found zero divisors of $X^K+1$. Builds using hardware carryless multiplication and portable bit spreading agreed on every census row and every exception. Each program accepts an inclusive range or defaults to the full search. For complete output files, the Python checker's `--full-runs` option compares every row and requires all 614 ranges in each file. The commands below replay the last 15 ranges. With `--list`, the census emits every irreducible support in the range. A zero missing mask selects a candidate that passes all five order tests. [NTL power search](scripts/check_1229_known_subgroup.cpp) · [Irreducibility and order census](scripts/census_1229_pentanomials.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/check_1229_known_subgroup.cpp -lntl -lgmp -o /tmp/gf2-known-subgroup
g++ -O3 -std=c++17 -march=native -fopenmp scripts/census_1229_pentanomials.cpp -lntl -lgmp -o /tmp/gf2-1229-census
/tmp/gf2-known-subgroup 600 614
/tmp/gf2-1229-census 600 614
/tmp/gf2-1229-census --list 600 614
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_pentanomial_census.py
~~~

The five other gaps through 1280 each have an irreducible product pentanomial with a partially certified order. The public JSON records its taps, the known prime factors, the exact remaining cofactor, and a divisor-search residue. For each candidate the checker proves that the root order includes the full known part and at least one cofactor prime above $10^{13}$. The five degrees can be investigated independently. [Open-degree candidates and cofactors](data/open-degrees-1231-1259.json) · [Checker](scripts/check_open_degrees.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_open_degrees.py
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_subfield_products.py --bound-1243 --threads 4
~~~

The complete product-pentanomial search in these six degrees covers 2,304,082 supports. All 7,126 irreducibles have a root order divisible by a prime of the unresolved cofactor. Of these, 7,100 also contain every known prime power, including 449 in degree 1229. The support list gives $u,v$ for $X^n+(1+X^u)(1+X^v)$. A zero mask selects a candidate passing every test. The low bits mark failed tests for the distinct known primes in increasing order, and the next bit marks an order dividing the known part. NTL reproduces the counts or emits every support with `--list`. FLINT checks every listed polynomial independently. [Counts by degree](data/open-product-census.csv) · [All irreducible supports](data/open-product-irreducibles.csv) · [Order bounds](results.pdf#page=77)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_open_product_census.py --parameters > /tmp/gf2-product-parameters
g++ -O3 -std=c++17 -fopenmp scripts/census_product_gaps.cpp -lntl -lgmp -o /tmp/gf2-product-census
OMP_NUM_THREADS=16 /tmp/gf2-product-census < /tmp/gf2-product-parameters
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_open_product_census.py --jobs 16
~~~

The semiprime census checks every eligible support in each degree. PARI/GP and NTL provide independent factorizations of the trinomials used in the proof. The Python checker also supports FLINT directly. To replay the census through 1280 with PARI/GP, or with the parallel NTL enumerator, run

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_subfield_census.py --through 1280 --gp gp
g++ -O3 -std=c++17 -fopenmp scripts/subfield_trinomial_factors.cpp -lntl -lgmp -o /tmp/gf2-subfield-factors
OMP_NUM_THREADS=8 uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_subfield_census.py --through 1280 --ntl /tmp/gf2-subfield-factors
~~~

All 639,166 irreducible degree-1229 pentanomials pass the first ten exterior-power tests. No product of one to ten conjugate roots equals one, even with repetitions. Within each polynomial the 23,270,993,347,436 products from subsets of at most five distinct roots, including the empty product, are all different. The integer checker enumerates 18,934,901,015 cyclic subset orbits for each of two order divisors. For a smaller-memory run, append a half-open range of residue classes to each command. The respective ranges are 0 through 16 and 0 through 20, with the upper endpoints excluded. [Ten-test proof](results.pdf#page=201) · [Full checker](scripts/check_1229_five_products.cpp) · [Lean product lemmas](GF2Sparse/RootProducts.lean) · [Earlier nine-test computation](scripts/check_1229_short_products.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/check_1229_five_products.cpp -lgmpxx -lgmp -o /tmp/gf2-five-products
OMP_NUM_THREADS=16 /tmp/gf2-five-products 36871
OMP_NUM_THREADS=16 /tmp/gf2-five-products 46703
~~~

The upper bound on the first failing rank comes from counting the ones in binary multiples of a possible root order. The same calculation bounds the first failing ranks in degrees 1231, 1237, 1243, 1249 and 1259 by 597, 600, 603, 606 and 611 respectively, for candidates passing the known prime-index tests. To verify all six bounds and the subset counts for degree 1229, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_failure_ranks.py --all
~~~

The checker verifies the frequency exclusions modulo each cofactor and evaluates the bounds in rational arithmetic. [Frequency products](data/exterior-failure-frequency-products.json) · [Lean moment and counting bounds](GF2Sparse/FailureRanks.lean)

For a nonprimitive irreducible in even degree, the smallest nonempty subset of conjugates with product one has size exactly half the degree if and only if a power of two is minus one modulo the root index. A primitive trinomial of odd degree $m\ge3$ gives a five-term example in degree $2m$. The example $X^{4094}+X^{2050}+X^{2047}+X^6+1$ has root order $3(2^{2047}-1)$ and first fails at rank 2047. Starting from Brent and Zimmermann's degree-74,207,281 trinomial gives an irreducible pentanomial whose first failure is at rank 74,207,281. [Construction and proof](results.pdf#page=203) · [Exact checks](scripts/check_middle_rank_twists.py) · [Published trinomial](https://arxiv.org/abs/1605.09213)

The two degree-1229 candidate fields also admit a common polynomial coordinate. Let $r$ be the root of the selected candidate and $a=z+z^{-1}$ for an element $z$ of order 2459. To obtain the exact mask of $a$ in the power basis of $r$, run the command below. It checks $a\ne0$, $D_{2459}(a)=0$, and the degree-1229 period polynomial at $a$. Here $D_j(z+z^{-1})=z^j+z^{-j}$. The residues $\pm2^k$ for $0\le k<1229$ exhaust the nonzero residues modulo 2459, so $D_j(a)$ for each such residue is a known Frobenius power of $a$. Lean proves the signed Frobenius identity, the degree of every order-2459 period, and the subgroup step for an invertible coefficient. [Coordinate construction](scripts/period_coordinate.py) · [Lean proofs](GF2Sparse/GaussPeriod.lean)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/period_coordinate.py
~~~

For a proof attempt, one open subproblem is to find a squarefree pentanomial in every sufficiently large degree that passes the first three exterior-power tests. The dyadic construction supplies four tests in every multiple of eight. The reciprocal-root sieve supplies the first two tests for all sufficiently large degrees. The third asks that no three distinct roots have product 1. Passing all ranks through half the prescribed degree on the same candidate proves it primitive. One explicit sequence of reducible pentanomials passes arbitrarily many tests. At degree 511 its polynomial has exactly seven factors of degree 73, and all factors in its degree-$2^{513}-1$ example have degree 262657. [Determinant criterion and sieve](results.pdf#page=11) · [Splitting-field obstruction](results.pdf#page=22) · [Lean factor degrees](GF2Sparse/ShortProducts.lean)

For the all-degree three-test problem it suffices to handle $p$ and $2p$ for each prime $p\ge5$. A squarefree, constant-one witness in either seed degree gives one in each odd multiple by substituting $X^m$ for $X$. Seeds 6 and 9 handle the remaining powers of three and their doubles, and the existing construction covers multiples of four. The signed-power theorem supplies some of these prime and twice-prime degrees. [Reduction and signed-degree proof](results.pdf#page=29)

The two degree-2047 trinomial lifts now have full order. Among the other sparse degree-11 seeds, two lift orders omit 47 and the remaining 42 pentanomial lifts pass all seven known prime-index tests. [Trinomial proof](results.pdf#page=172) · [Partial census of all 46 lifts](scripts/check_ore_2047.py)


For a Lean contribution, Section 28 gives an explicit normal basis in the field generated by an Ore root. The Vandermonde criterion for independence is formalized. The remaining step is to formalize the expansion of the Moore determinant that supplies its distinct nodes. [Written proof](results.pdf#page=35) · [Lean criterion](GF2Sparse/OreNorms.lean)

For work on the first unresolved degree, run the degree-1229 checker below. It prints the exact 284-digit cofactor. A factor of this integer would narrow the remaining order tests. A complete factorization, together with a nonidentity power for each remaining prime divisor, would certify the displayed pentanomial.

For the period-coordinate targets, a submission row `mask,exponent` means $B_{\rm mask}(a)=r^{\rm exponent}$ for the selected sparse root. Bit $i$ of the mask is the coefficient of $T^i$. Contributors can take disjoint rows. The checker accepts partial lists and verifies each supplied or derived exponent in the chosen field. [Download the 3,380 targets](data/degree-1229-period-wheel.csv) · [Earlier 3,399 targets](data/degree-1229-period-compact.csv) · [Original 3,531 targets](data/degree-1229-period-targets.csv) · [Polynomial identities](data/degree-1229-period-relations.jsonl)

Contributors can also work entirely in the subgroup of order $C=(2^{1229}-1)/K$. With the `--projected` flag, a row supplies $0\le e<C$ satisfying $B_{\rm mask}(a)^K=(r^K)^e$. The four known prime factors of $K$ already divide the order of $r$, so each verified projected power proves membership in the original subgroup generated by $r$. Use one convention per invocation. Supply `--taps A B C` for any participating polynomial $X^{1229}+X^C+X^B+X^A+1$. For example, the support with interior taps 600, 609 and 615 passes all five checks. [Lean projection proof](GF2Sparse/GaussPeriod.lean) · [Submission checker](scripts/check_period_relations.py)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_period_relations.py --wheel --candidate seroussi --projected --logs my-projected-logs.csv
~~~

For a relation search, both candidate roots are available in two other power bases. With $q=1024$ and $y=x^q$, the field generator satisfies $x=(y^5+y^2+1)/(y^3+y)$. Norm circles and trace lines give 120 independent relations among binary polynomial values of degrees dividing 20. The $q=256$ model gives 21 relations in degrees dividing 16. The commands reconstruct the roots and export the $q=1024$ rows as pairs of polynomial masks and signed exponents. [Field moduli and sparse roots](data/degree-1229-frobenius-models.json) · [Relation parameters](data/degree-1229-circle-pivots.csv) · [Derivation and criterion for primitivity](results.pdf#page=66)

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_frobenius_models.py
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_circle_relations.py --q 1024 --relations > /tmp/gf2-circle-1024.jsonl
~~~

Allowing all centers in the auxiliary field gives 92,910 split circles up to binary conjugation. Their equations eliminate at least 4,096 of the 52,488 factor-base values modulo the full group order. The CSV contains the center, norm radius and six roots of each sextic, encoded as polynomial-basis integers. The checker computes a 10,296-bit integer determinant coprime to $2^{1229}-1$. Use `--minor 1536` for a shorter check. [Circle equations and proof](results.pdf#page=105)

~~~sh
g++ -O3 -std=c++17 scripts/enumerate_1229_translated_circles.cpp -o /tmp/gf2-translated-circles
/tmp/gf2-translated-circles --csv > /tmp/gf2-translated-circles.csv
uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_translated_circles.py /tmp/gf2-translated-circles.csv --minor 4096
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_factor_generation.py --factors
~~~

The quadratic model uses a separate field of order $1024^{1229}$. Check the binary modulus, the constant-field embedding, and the two period-coordinate roots with PARI/GP.

~~~sh
python3 scripts/check_1229_quadratic_model.py
~~~

The forward models use a larger constant field for logarithm descent. The following command checks the six field degrees, the trap exclusions, and the norm identities for both sparse roots and all ten period targets of degree at most six. Each coefficient list starts at the constant term. Use `--quotients-only` to check the degree-16 quotients and their optimality.

~~~sh
python3 scripts/check_1229_forward_descent.py
~~~

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_period_relations.py --wheel
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_period_relations.py --wheel --candidate seroussi --logs /path/to/period-logs.csv
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

For a computational contribution, choose a degree interval beyond the Lean-verified range and run it on your own machine. The example below certifies degrees 673 through 688 from their public CSV witnesses with Python, SymPy and FLINT. The published factorizations give the orders to test, and FLINT speeds up the search for primality certificates. Lean checks the primality proofs, the product of the supplied factors, and the polynomial orders. [Cunningham Project](https://homes.cerias.purdue.edu/~ssw/cun/) · [Pinned JSON transcription](https://github.com/postvakje/Reformatted-Cunningham-Project-tables/blob/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json)

~~~sh
curl -fsSL https://raw.githubusercontent.com/postvakje/Reformatted-Cunningham-Project-tables/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json -o /tmp/gf2-cunningham.json &&
  uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/make_packed_table.py 673 688 --factor-table /tmp/gf2-cunningham.json > /tmp/gf2-673-688.lean &&
  cp /tmp/gf2-673-688.lean GF2Sparse/Witnesses673To688.lean &&
  lake build GF2Sparse.Witnesses673To688 &&
  lake env leanchecker -v GF2Sparse.Witnesses673To688
~~~

A pull request can include the generated table and the corresponding interval theorem. Existing tables can be checked independently, so contributors can work on disjoint ranges. [Combining verified intervals](GF2Sparse/Coverage.lean)

## Verification

To reproduce the density bounds, run `python3 scripts/check_trinomial_density.py` with the Python standard library. It counts residue classes using fields through degree 25. Add `--through 18` for a shorter calculation that already excludes primitive trinomials from more than 35.1% of all degrees. Use `--prime-powers` to reproduce the bound for all odd powers of the same prime with fields through degree 16.

To replay the Mers Project witnesses, install PARI/GP and run the command below. Add `--degree 3987` to check one row. Each witness lists the interior exponents in increasing order. The constant and leading coefficients are one. [Mers Project factor table](https://mers.sourceforge.io/factoredM.txt) · [Seroussi's irreducible polynomial table](https://shiftleft.com/mirrors/www.hpl.hp.com/techreports/98/HPL-98-135.pdf)

```bash
uv run --no-project --with python-flint==0.9.0 python scripts/check_mers_project_orders.py
```

To repeat the trinomial enumeration and verify the exact orders of the eight exceptions, compile the NTL backend and pass its path to the verifier. Add `--degree 3537` to select the degree with four primitive pairs and one pair of index seven. For the twenty larger census rows, use `--table data/mers-project-large-orders.json` and select one or more of `17683`, `17698`, `19121`, `20521`, `20887`, `22193`, `22327`, `25243`, `25933`, `26903`, `28381`, `28759`, `28771`, `29473`, `32531`, `33511`, `35339`, `35737`, `41263` and `41521` with `--degree`. [Trinomial census](data/mers-project-trinomial-census.csv)

```bash
c++ -std=c++17 -O3 scripts/prime_degree_trinomials.cpp -lntl -lgmp -o /tmp/gf2fun-trinomials
uv run --no-project --with python-flint==0.9.0 python scripts/check_mers_project_orders.py \
  --trinomial-census /tmp/gf2fun-trinomials
```

The irreducibility census can also be replayed without supplying any integer factors. For degree 35,737, the following command reproduces the empty list of irreducible taps.

~~~sh
printf '%s\n' 35737 | /tmp/gf2fun-trinomials --irreducible-only | diff -u data/mers-project-trinomial-census-supplement.csv -
~~~

To find more candidate field orders, download the two Mers Project files and choose specific degrees or an interval. The command below reconstructs the factors in degrees 4,952 and 5,689. The search checks probable primality. The witness verifier above checks primality proofs and polynomial orders. For a missing subfield, `--supplement` accepts an existing factor table and also uses its factorizations in extension degrees. [Archive format](https://mers.sourceforge.io/mersfmt.txt) · [Factor reconstruction](scripts/mers_project_factor_candidates.py)

```bash
curl -fsSLo /tmp/gf2fun-factoredM.txt https://mers.sourceforge.io/factoredM.txt
curl -fsSLo /tmp/gf2fun-primeM.txt https://mers.sourceforge.io/primeM.txt
uv run --no-project --with python-flint==0.9.0 python scripts/mers_project_factor_candidates.py \
  /tmp/gf2fun-factoredM.txt /tmp/gf2fun-primeM.txt --degrees 4952 5689
```

To regenerate and verify every large five-term power image from the published trinomial lists, run the first command. The next commands replay the complete source classifications for degrees 110,503 and 132,049. They check a proper polynomial factor for every excluded tap, Lucas–Lehmer primality for the two group orders and the full polynomial powers for the seven positive seeds. Lean checks the degree-74,207,281 implication from the published trinomial. [Brent and collaborators’ extended factor certificates](https://maths-people.anu.edu.au/~brent/trinomlg.html)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_large_trinomial_samples.py
for n in 110503 132049; do
  curl -fsSL "https://maths-people.anu.edu.au/~brent/ftp/trinom/i${n}.log-ext.gz" -o "/tmp/gf2fun-${n}.log-ext.gz" &&
    uv run --no-project --with python-flint==0.9.0 python scripts/check_large_trinomial_samples.py --replay "$n" --factor-log "/tmp/gf2fun-${n}.log-ext.gz" || exit 1
done
lake build GF2Sparse.LargeTrinomialSamples
lake env leanchecker -v GF2Sparse.LargeTrinomialSamples
~~~

In degree 4112, the first command checks the eleven-term primitive polynomial by direct powering and verifies the known order divisor of the five-term candidate. The descent checker verifies the subfield multiple and its factorizations. The projective solver reconstructs the original 129 exponents from the circle equations. A contributor with a candidate scalar can pass it to the first command using `--target-exponent E`.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_projective_4112.py --jobs 6 --target
uv run --no-project --with python-flint==0.9.0 python scripts/check_4112_descent.py
uv run --no-project --with python-flint==0.9.0 --with gmpy2 python scripts/solve_projective_4112.py > /tmp/gf2fun-4112-logs.csv
gzip -cd data/degree-4112-projective-logs.csv.gz | cmp - /tmp/gf2fun-4112-logs.csv
~~~

The following two commands independently verify the 2,048 binomial logarithms and reproduce the same order counts. The first checks each power directly in the binary field. The second rebuilds the table from the 129 projective logarithms.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_4112_binomials.py --jobs 8
uv run --no-project --with python-flint==0.9.0 --with gmpy2 python scripts/check_4112_binomials.py --rebuild
~~~

To verify the trace-translate census, the weight bound and a direct sample of all three quadratic reductions, run the first command below. The next command exports the 568 open factors for the five-term candidate. Each row gives a monic polynomial in ascending coefficient order, its signed multiplier and a place for its projected exponent. The 16-bit coefficients are in the binary power basis of $a$. In a copy of the JSON, fill any `exponent` with the integer $0\le e<C$ satisfying $H(y)^D=(r^D)^e$. The last command checks each supplied power and writes the remaining factors. Multiple `--logs` arguments accept contributions from different machines. Adding `--max-degree 11` to the export gives a shorter list with larger factors, and a verified exponent for an earlier factor also resolves its descendants.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_4112_trace_translates.py --sample-powers
uv run --no-project --with python-flint==0.9.0 python scripts/check_4112_descent.py --tasks /tmp/gf2fun-4112-tasks.json
uv run --no-project --with python-flint==0.9.0 python scripts/check_4112_descent.py --logs /tmp/gf2fun-4112-tasks.json --tasks /tmp/gf2fun-4112-remaining.json
~~~

To reproduce the complete order and term-count census of the 52,488 degree-1229 factor-base values, use a C++17 compiler with NTL and OpenMP. Omitting the `--census` argument and its executable checks the two minimum-weight examples and the exceptional order directly in Python.

~~~sh
g++ -std=c++17 -O3 -fopenmp scripts/census_1229_factor_base.cpp -lntl -o /tmp/gf2-factor-base-orders
OMP_NUM_THREADS=8 uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_factor_base_orders.py --census /tmp/gf2-factor-base-orders
~~~

Add `--extended` to that Python command to check all 90,839 orders and term counts. Run it with only `--extended` to check the two minimum-weight examples and the four exceptional orders with FLINT.

The same NTL executable checks all 37,751 isogeny lifts. The following commands also export their exponents and replay the Lean coordinate identities.

~~~sh
OMP_NUM_THREADS=8 uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_isogeny_logs.py --second-step --verify-powers /tmp/gf2-factor-base-orders --export /tmp/gf2-isogeny-logs.csv
OMP_NUM_THREADS=8 uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_1229_partial_circles.py --verify-powers /tmp/gf2-factor-base-orders --isogeny-logs /tmp/gf2-isogeny-logs.csv
lake build GF2Sparse.QuinticIsogeny && lake env leanchecker -v GF2Sparse.QuinticIsogeny
~~~

With PARI/GP on the path, the following commands reconstruct the elliptic norms and check the degree-53 logarithms and the degree-1229 targets.

~~~sh
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_elliptic_ray.py --degree 53
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_elliptic_ray.py --degree 1229
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_elliptic_ray.py --degree 1229 --no-order-tests
~~~

The last command verifies all 733 full-group targets. Add `--taps 136 683 819 --logs answers.csv` to check any submitted logarithms for the elliptic pentanomial. The CSV columns are `target,exponent`. A complete set proves full order. The pure-Python command `python3 scripts/elliptic_ray_bound.py 1229 --level 6` computes the general construction parameters for that degree and sieve level.

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

The fifteen tables for degrees 433 through 672 use packed binary squaring for the full power and each prime-factor test. To reproduce an interval, run

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

The odd-degree table from 1281 through 1535 uses every odd degree with a complete factorization in the two specified files. To replay the 80 full orders, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 1281 --end 1535 --step 2 --available --factor-table /tmp/gf2-cunningham.json --factor-table data/mersenne-odd-1281-1535-extra.json --verify data/odd-product-witnesses-1281-1535.csv --jobs 4
~~~

The next seven tables include the complete factorizations needed to verify their 307 witnesses locally.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 1537 --end 1791 --step 2 --available --factor-table data/mersenne-odd-1537-1791.json --verify data/odd-product-witnesses-1537-1791.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 1793 --end 2047 --step 2 --available --factor-table data/mersenne-odd-1793-2047.json --verify data/odd-product-witnesses-1793-2047.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 2049 --end 2291 --step 2 --available --factor-table data/mersenne-odd-2049-2291.json --verify data/odd-product-witnesses-2049-2291.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 2293 --end 2416 --available --factor-table data/mersenne-2293-2416.json --verify data/product-witnesses-2293-2416.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 2417 --end 2560 --available --factor-table data/mersenne-2417-2560.json --verify data/product-witnesses-2417-2560.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 2561 --end 2688 --available --factor-table data/mersenne-2561-2688.json --verify data/product-witnesses-2561-2688.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 2689 --end 2816 --available --factor-table data/mersenne-2689-2816.json --verify data/product-witnesses-2689-2816.csv --jobs 4
~~~

The 35 witnesses from degree 3073 through 3200 can be checked from the published factorizations.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 3073 --end 3200 --available --factor-table data/mersenne-3073-3200.json --verify data/product-witnesses-3073-3200.csv --jobs 4
~~~

To verify the 58 witnesses from degree 3201 through 3456, the following command uses PARI/GP to check the ten largest primes against their archived elliptic-curve primality certificates. FLINT proves the other 1,467 primes and checks every polynomial order. Omitting `--prime-certificates` and its path makes FLINT prove all 1,477 primes. To reproduce the minimum spans with PARI/GP, replace `--verify` and `--prime-certificates` and their paths with `--search --least-span`.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 3201 --end 3456 --available --factor-table data/mersenne-3201-3456.json --verify data/product-witnesses-3201-3456.csv --prime-certificates data/mersenne-3201-3456-prime-certificates.json.gz --jobs 6
~~~

The 81 product witnesses from 3460 through 4096 use 2,426 distinct prime factors. The second command also checks the order of Seroussi’s degree-4096 polynomial and the exclusions for every other pentanomial with all interior exponents at most 27. [Proper divisors](data/degree-4096-small-tap-factors.csv.gz) · [Primality certificate for the 564-digit factor](data/mersenne-3457-4096-prime-certificates.json.gz)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 3457 --end 4096 --available --factor-table data/mersenne-3457-4096.json --verify data/product-witnesses-3457-4096.csv --prime-certificates data/mersenne-3457-4096-prime-certificates.json.gz --jobs 6
uv run --no-project --with python-flint==0.9.0 python scripts/check_4096_small_taps.py
~~~

To classify the quaternary factors, run the rational enumeration. The degree checks use PARI/GP. The degree-30 example has full order, and the degree-2458 run computes the norm polynomial of its single irreducible candidate.

~~~sh
uv run --no-project --with sympy python scripts/check_quaternary_norm_shapes.py
uv run --no-project --with sympy python scripts/check_quaternary_norm_shapes.py --degree 30 --orders
uv run --no-project --with sympy python scripts/check_quaternary_norm_shapes.py --degree 2458
~~~

The progression test checks 72 factorizations over four finite fields, all 1,173 symmetric-tap discriminants and factor counts in even degrees 6 through 96, and full-order examples in degrees 3150, 5964 and 6300. It also reconstructs both degree-3780 factors of the degree-7560 witness. Add `--central` with PARI/GP installed to reproduce the 1,500-degree census and the three primitive reciprocal pairs.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_progression_factor_parity.py
~~~

The 122 witnesses in degrees 4100 through 5964 use 4,040 distinct primes. The checker proves primality, reconstructs each group order and verifies 5,611 prime-index powers. To reproduce the search in order of increasing tap span, replace `--verify` and its CSV path with `--search --least-span`.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 4100 --end 5964 --step 8 --available --factor-table data/mersenne-4097-5964.json --verify data/product-witnesses-4097-5964.csv --jobs 8
~~~

The ten additional degrees from 4224 through 7560 use the same verifier and an archived factor table.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 4224 --end 7560 --available --factor-table data/mersenne-4224-7560-extra.json --verify data/product-witnesses-4224-7560-extra.csv --jobs 8
~~~

For the five witnesses in degrees 7854 through 9576, each row gives the degree $n$ and the two exponents $b,a$ in $X^n+X^{n-b}+X^a+X^b+1$.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 7854 --end 9576 --available --symmetric --factor-table data/mersenne-symmetric-above-7560.json --verify data/symmetric-witnesses-above-7560.csv --jobs 4
~~~

To verify the eleven semiprime degrees, compile both NTL enumerators and run the norm and primality certificates with PARI/GP available. Add `--degree 14971` to verify just that row. Omit `--scalar-pairs` to repeat the pair census with the independent Python implementation.

~~~sh
c++ -std=c++17 -O3 scripts/prime_degree_trinomials.cpp -lntl -lgmp -o /tmp/gf2-trinomials
c++ -std=c++17 -O3 scripts/check_scalar_pairs.cpp -lntl -lgmp -o /tmp/gf2-scalar-pairs
uv run --no-project --with python-flint==0.9.0 --with sympy python scripts/check_semiprime_scalar_norms.py --trinomials /tmp/gf2-trinomials --scalar-pairs /tmp/gf2-scalar-pairs
~~~

The scalar-order sieves run with standard Python. The product census uses NTL and PARI/GP. Select a single large degree with `--degree 5403`, or omit the option to check every archived row. Use `--orders-only` for the individual witness certificates. The odd-degree sweep uses the same binary.

~~~sh
python scripts/check_scalar_order_bound.py
python scripts/check_coprime_scalar_orders.py
c++ -std=c++17 -O3 -fopenmp scripts/check_scalar_pair_products.cpp -lntl -lgmp -o /tmp/gf2-pair-products
uv run --no-project --with python-flint==0.9.0 --with sympy python scripts/check_scalar_product_orders.py --products /tmp/gf2-pair-products --trinomials /tmp/gf2-trinomials --degree 5403
python scripts/check_odd_scalar_splits.py --check-counts
python scripts/check_odd_scalar_splits.py --products /tmp/gf2-pair-products --jobs 8
uv run --no-project --with python-flint==0.9.0 --with sympy python scripts/check_progression_scalar_orders.py
lake build GF2Sparse.ScalarOrderBound
lake env leanchecker GF2Sparse.ScalarOrderBound
~~~

To reproduce the six prime-degree weight distributions, compile the enumerator with NTL and run the verifier with PARI/GP available. Add `--degree 28771` to check that spectrum and the prime-divisor bound through $2^{44}$. The degree-28,759 and degree-28,771 checks use only the small order primes and the polynomial data.

~~~sh
c++ -std=c++17 -O3 -fopenmp scripts/cyclotomic_weight_census.cpp -lntl -lgmp -o /tmp/gf2-cyclotomic-weights
uv run --no-project --with python-flint==0.9.0 python scripts/check_cyclotomic_weights.py --census /tmp/gf2-cyclotomic-weights
~~~

The prime-degree order classification uses the same executable. The signed cubing test also checks the three excluded orders above one million.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_sparse_root_orders.py --census /tmp/gf2-cyclotomic-weights
uv run --no-project --with python-flint==0.9.0 python scripts/check_cubing_chains.py --signed-orders
uv run --no-project --with python-flint==0.9.0 python scripts/check_sparse_power_orbits.py
~~~

The following checks all signed orbit collisions between powers 1, 3, 5 and 7 for normalized trinomials and pentanomials in arbitrary degree. It also checks every normalized irreducible through degree 40 by an independent order calculation. Add `--pair 3 5` to select just the third and fifth powers.

~~~sh
c++ -std=c++17 -O3 scripts/power_orbit_collisions.cpp -o /tmp/gf2-power-orbit-collisions
uv run --no-project --with python-flint==0.9.0 python scripts/check_power_orbit_collisions.py --solver /tmp/gf2-power-orbit-collisions --through 40
~~~

The same executable checks the seventh-power degree theorem. The Python verifier also tests every sparse irreducible up to reciprocity through degree 64 by direct Frobenius powering.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_seventh_power_degree.py --solver /tmp/gf2-power-orbit-collisions
~~~

To reproduce the subfield bound's finite cases, compile the NTL product test. The verifier checks all 88 partner cases in both parities, the square identities, and the exceptions to the 31st-power theorem. The first two commands below independently reconstruct the scalar orders used in the proof.

~~~sh
python3 scripts/check_coprime_scalar_orders.py --limit 1000
python3 scripts/check_scalar_order_bound.py --limit 10000
c++ -std=c++17 -O3 -fopenmp scripts/check_scalar_pair_products.cpp -lntl -lgmp -o /tmp/gf2-scalar-products
uv run --no-project --with python-flint==0.9.0 python scripts/check_subfield_square.py --products /tmp/gf2-scalar-products --through 64
uv run --no-project --with python-flint==0.9.0 python scripts/check_semiprime_order_primes.py
~~~

The NTL enumeration lists every exceptional reciprocal pair in the first three exceptional degrees.

~~~sh
c++ -O3 -std=c++17 -fopenmp scripts/check_semiprime_order_exceptions.cpp -lntl -lgmp -o /tmp/gf2-order-exceptions
/tmp/gf2-order-exceptions 3 7
/tmp/gf2-order-exceptions 5 31
/tmp/gf2-order-exceptions 11 23
~~~

The following calculation checks all characteristics for the thirteen smaller primes in the two-prime degree theorem and lists the eight residual tap patterns modulo 31.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_cyclotomic_row_isolation.py
~~~

The exact two-bit count uses the lifts of those residues modulo 961. To replay all determinant tests and the eighteen expanded examples, run

~~~sh
uv run --no-project --with python-flint==0.9.0 --with sympy python scripts/check_five_31_tower.py
~~~

The simultaneous substitution theorem has an independent check in degrees 22,517 and 517,891. The same verifier recomputes the 20-bit counts for every nonempty subset of the four known degree-1229 primes.

~~~sh
uv run --no-project --with python-flint==0.9.0 --with sympy python scripts/check_multiprime_supports.py
~~~

The five-row determinant calculation proves the substitution criterion for every prime $q\ge37$. The same command checks the six exceptional semiprime degrees through 1,280, the two towers from the degree-1,229 census, all 30 exceptional reciprocal pairs at levels 5,819 and 112,903, and the trinomial tap rule through 384. The NTL enumerator above accepts `7 127` to recover the seven degree-889 pairs by direct enumeration.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_kummer_sparse_orders.py
~~~

The same binary verifies the 1,235 sparse witnesses through 70,000. The Python driver also computes the order-prime graph counts through one million.

~~~sh
python3 scripts/check_order_prime_partitions.py --ntl /tmp/gf2-order-exceptions
~~~

To exhaust the binary-digit graphs for the two cubic substitutions and to check the translated trinomial families through degree 262,145, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_cubic_components.py
~~~

To compare the 22 known order-test failures against the 639,144 surviving degree-1,229 pentanomials and check the primitive trace count, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_prescribed_root_traces.py --census
~~~

The 1,180-bit and 1,200-bit exceptional fractions and a complete two-ended trace histogram in a small field can be checked with

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_trace_incompressibility.py
~~~

To list the two degree-1229 pairs and check all 256 and 1,024 polynomials in the shorter records, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_trace_fibres.py
~~~

To replay the elliptic function counts in degrees 262,146 and $2^{84}+2$, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_elliptic_quotient_counts.py
~~~

To reproduce the order projections and subfield certificates, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1331_order_projections.py --gp gp
uv run --no-project --with python-flint==0.9.0 python scripts/check_relative_fourier_minors.py
uv run --no-project --with python-flint==0.9.0 python scripts/check_seven_position_orders.py
uv run --no-project --with python-flint==0.9.0 python scripts/check_trinomial_subfield_pairs.py
lake build GF2Sparse
~~~

To check the progression census for intersecting maximal subfields, run

~~~sh
c++ -std=c++17 -O3 scripts/relative_progression_orders.cpp -lntl -lgmp -o /tmp/gf2-relative-orders
uv run --no-project --with sympy python scripts/check_relative_progressions.py --limit 20000 --checker /tmp/gf2-relative-orders --jobs 4
uv run --no-project --with sympy python scripts/check_relative_progressions.py --limit 10000 --short-triples --checker /tmp/gf2-relative-orders --jobs 4
uv run --no-project --with sympy python scripts/check_relative_progressions.py --limit 100000
uv run --no-project --with sympy python scripts/check_relative_progressions.py --family 23 101 7920
uv run --no-project --with sympy python scripts/check_relative_progressions.py --degree 12231 --checker /tmp/gf2-relative-orders
uv run --no-project --with python-flint==0.9.0 python scripts/check_relative_progression_witnesses.py
~~~

To repeat the degree-3,073 tap census and list the 23 reciprocal pairs of pentanomials, run the Python verifier. The C++ program counts the split circles of the selected auxiliary field.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_3073_trinomials.py --census --images
c++ -O3 -std=c++17 scripts/count_3073_circles.cpp -o /tmp/gf2-3073-circles
/tmp/gf2-3073-circles 1024
~~~

With PARI/GP and the NTL development libraries installed, these commands verify all orders in the additional cyclotomic table, repeat the exhaustive trinomial searches and reproduce the weight bound at degree 17,029.

~~~sh
c++ -O3 -std=c++17 scripts/prime_degree_trinomials.cpp -lntl -lgmp -o /tmp/gf2-trinomials
uv run --no-project --with python-flint==0.9.0 python scripts/check_composite_orders.py --table data/cyclotomic-order-witnesses.json --ntl /tmp/gf2-trinomials
c++ -O3 -std=c++17 scripts/cyclotomic_weight_census.cpp -lntl -lgmp -o /tmp/gf2-cyclotomic-weights
/tmp/gf2-cyclotomic-weights --prefix-bound 17029 418879343 1 2 560
~~~

The Python command verifies all 22 composite degrees in the original witness table with PARI/GP. Add `--degree 24853` to check only that degree, or `--ntl` with the path to the compiled trinomial enumerator to repeat the exhaustive tap search. The Lean command builds the general norm criterion. [Trinomial enumerator](scripts/prime_degree_trinomials.cpp)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_composite_orders.py
lake build GF2Sparse.PartialOrder
~~~

Workers can search disjoint degree intervals for further candidates. The search removes small primes from $\Phi_n(2)$ and reports the maximal subfield degrees whose group orders supply the other factors. A probable-prime remainder still needs a primality certificate before it can support a full-order result. [Cyclotomic search](scripts/search_cyclotomic_parts.py)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/search_cyclotomic_parts.py --start 24260 --end 24265 --jobs 4
~~~

For large trial bounds the search sieves the possible prime divisors in segments. At degree 3,837 a bound of two billion recovers 30,697 and 4,819,273 and leaves the 759-digit prime in the witness table.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/search_cyclotomic_parts.py --start 3837 --end 3837 --trial-limit 2000000000
~~~

In degree 16,129 the verifier checks the archived 514-step PRIMO certificate against the 4,789-digit factor of the group order. The same file can also be checked with `gzip -dc data/degree-16129-primality.cert.gz | vcert -q -`. [Original certificate](https://factordb.com/cert/1100000000252268434) · [Independent GMP verifier](https://github.com/danaj/Math-Prime-Util-GMP/blob/531591c6aa56c0f42450b8ca202dac56ab573b43/examples/vcert.c)

To check the twisted cyclotomic family, the first command tests the root orders and the exclusion of every odd exponent strictly between 191 and 16,541. The second compares the cubic character with certified PARI class groups and checks the order formula for the projection to the subfield of half the degree.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_translation_lift_orders.py --extended-cyclotomic
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_cubic.py --gp gp
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_cubic.py --gp gp --reflection-survey 100000
lake build GF2Sparse.TwistedCyclotomic
~~~

The ray class checker compares the Frobenius action on an ordinary ray class group modulo two with direct binary powering. The sample covers 253 number fields, with 325 prime-index tests for the twisted roots and 195 for the Gauss periods. At $p=2053$, a cubic field detects the factor seven in the index of the degree-2052 pentanomial.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_ray.py --case 2053 3
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_ray.py --jobs 4
~~~

For the five-term examples in degrees $2^{141}+4$ and $2^{191}+4$, the first two commands certify the quadratic, cubic and quartic number fields that test index primes 3, 7 and 5. The third proves the exact powers of three in the two root orders without assuming the generalized Riemann hypothesis. It bounds the imaginary quadratic class numbers using signed sums with prime cutoffs $2^{21}$ and $2^{26}$, respectively, then checks a quadratic form of conductor three. The final PARI calculation gives the stronger real class-number value $h(4p)=1$ under GRH. [Field equations](results.pdf#page=250) · [Unconditional proof](results.pdf#page=257)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_ray.py --fields 141
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_ray.py --fields 191
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_three_class.py
gp -fq -s 512M <<'GP'
for(i=1,2,my(k=[141,191][i]); print([k,quadclassunit(4*(2^k+5)).no]))
GP
~~~

For the explicit gcd in the full-order criterion, every possible prime divisor at $k=141$ is one modulo $2\cdot51542639524661795300074174250365699$. At $k=191$ the multiplicative order of two modulo any such prime must exceed $10^{16}$. The calculation reduces a two-dimensional lattice and checks 52 gcds to cover 710 divisors in the second case. Lean verifies both discrete logarithms and the order restriction at $k=141$. Prime factors can still enter the root-order index through the ray class group. [Proof](results.pdf#page=251) · [Lean certificate](GF2Sparse/TwistedCyclotomic.lean)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_correction.py --jobs 4
~~~

The ray quotient also gives the exact prime-power multiplicities in the root-order index away from primes dividing the degree. For $k=141$ the only exceptional prime is 3. For $k=191$ they are 3, 19 and 87,211. Lean certifies both lists. [Index formula](results.pdf#page=252) · [Lean certificates](GF2Sparse/TwistedCyclotomic.lean)

The first command verifies both large certificates by multiplying quadratic ideal lattices with FLINT. It needs only the Python wheel. The second also checks both large cases against PARI and compares the prediction with direct binary powering for every eligible prime through 2,053. The form survey covers all 248,761 eligible primes through ten million. Exactly the 74,706 primes congruent to 23 modulo 24 divide the corresponding root-order index. [Certificate exponents](data/translation-lift-orders.json)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_conductor.py
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_conductor.py --small
uv run --no-project --with python-flint==0.9.0 python scripts/check_twisted_conductor.py --survey 10000000
~~~

To reproduce the optimal normal basis classification, run the finite orbit and order checks and the formal coefficient bound.

~~~sh
uv run --no-project --with sympy python scripts/check_gauss_period_weights.py
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_quadratic_period_images.py
lake build GF2Sparse.GaussPeriodWeights
~~~

The seventeen additional prime degrees from 3467 to 5087 each have a pentanomial certificate. The NTL calculation checks every trinomial up to reciprocation and prints both sets of surviving taps.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 3467 --end 5087 --available --symmetric --factor-table data/mersenne-prime-degrees-3467-5087.json --prime-certificates data/mersenne-prime-degrees-ecpp.json.gz --verify data/complementary-prime-degrees-3467-5087.csv --jobs 6
c++ -std=c++17 -O3 scripts/prime_degree_trinomials.cpp -lntl -lgmp -o /tmp/gf2-prime-degree-trinomials
python3 -c 'import json; d=json.load(open("data/mersenne-prime-degrees-3467-5087.json")); [print(n,len(ps),*ps) for n,ps in d.items()]' | /tmp/gf2-prime-degree-trinomials > /tmp/gf2-prime-degree-trinomials.csv
cmp /tmp/gf2-prime-degree-trinomials.csv data/prime-degree-trinomial-census.csv
~~~

The same NTL program checks all 1,963 trinomial reciprocal pairs at degree 3,927. The FLINT checker reads the factors from the table for degree 7,854 and verifies the exact orders of all ten irreducible trinomials and eleven pentanomials.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_3927_thirds.py --ntl /tmp/gf2-prime-degree-trinomials
~~~

The additional composite degrees have a self-contained factor table and compressed PARI ECPP certificates. FLINT checks every polynomial order and proves the remaining factors prime.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 3464 --end 4032 --available --symmetric --factor-table data/mersenne-complementary-cyclotomic.json --prime-certificates data/mersenne-cyclotomic-prime-certificates.json.gz --verify data/complementary-width-cyclotomic.csv --jobs 6
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 3510 --end 10351 --available --symmetric --factor-table data/mersenne-complementary-width-extra.json --prime-certificates data/mersenne-complementary-width-prime-certificates.json.gz --verify data/complementary-width-extra.csv --jobs 6
~~~

To reproduce the search in degree 10,351, compile the NTL program and feed it the complete factor list. It searches all complementary orientations in increasing normalized width. The separate norm check uses PARI/GP, FLINT and the archived certificates for degrees 3415 and 9583.

~~~sh
c++ -std=c++17 -O3 scripts/search_complementary_width.cpp -lntl -lgmp -o /tmp/gf2-search-width
python3 -c 'import json; print(*json.load(open("data/mersenne-complementary-width-extra.json"))["10351"])' | /tmp/gf2-search-width 10351 3
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_two_subfield_norms.py
~~~

The prime-order checker replays Lucas–Lehmer and the full polynomial powers for both degree-216,091 witnesses and the two published degree-86,243 pentanomials of Kumada et al. The prefix option checks one witness at each of the first 33 Mersenne prime exponents. [Original report, Table 2](https://www.math.keio.ac.jp/wp-content/uploads/2022/03/98009.pdf)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_large_circle_orders.py --degree 86243
uv run --no-project --with python-flint==0.9.0 python scripts/check_large_circle_orders.py --degree 216091
uv run --no-project --with python-flint==0.9.0 python scripts/check_large_circle_orders.py --mersenne-prefix
uv run --no-project --with 'numpy>=2,<3' --with python-flint==0.9.0 python scripts/check_almost_trinomial_powers.py --cross-check-small
~~~

To search a Mersenne prime exponent directly, divide the largest interior exponent into intervals across machines. The optional fourth argument fixes the middle exponent. The search filters divisors through degree 16, runs NTL's irreducibility test, and prints the first matching support as `degree,low,middle,high`. These commands reproduce the second degree-216,091 witness and independently check its order.

~~~sh
c++ -std=c++17 -O3 scripts/search_low_pentanomials.cpp -lntl -o /tmp/gf2-search-low
/tmp/gf2-search-low 216091 130 130 10
uv run --no-project --with python-flint==0.9.0 python scripts/check_large_circle_orders.py --pentanomial 216091 3 10 130
~~~

On a CUDA 12 GPU, the following checks ordered tap triples in batches of eight. For prime degree $n$ and $2c-2<n$, two folds reduce each square modulo $X^n+X^c+X^b+X^a+1$. The program decides irreducibility by testing $X^{2^n}=X$. It prints a result for every input triple. At a Mersenne prime exponent an irreducible result also certifies primitivity. The self-test compares 216 GPU residues with binary long division. [GPU checker](scripts/check_low_tap_frobenius.py) · [Squaring kernel](scripts/low_tap_frobenius.cu)

~~~sh
uv run --no-project --with cupy-cuda12x==14.2.0 --with nvidia-cuda-nvrtc-cu12==12.9.86 --with nvidia-cuda-runtime-cu12==12.9.79 python scripts/check_low_tap_frobenius.py --self-test
uv run --no-project --with cupy-cuda12x==14.2.0 --with nvidia-cuda-nvrtc-cu12==12.9.86 --with nvidia-cuda-runtime-cu12==12.9.79 python scripts/check_low_tap_frobenius.py 216091 <<'TAPS'
13 26 68
3 10 130
2 3 6
TAPS
~~~

The first two triples give irreducibles. The third has the factor $X^2+X+1$.

At degree 1,257,787, all 1,280 triples in the first sample gave reducible polynomials. The list contains only the tested triples, with largest tap at most 90. Contributors can skip these triples in later searches or replay them with the command below. [Tested triples](data/degree-1257787-reducible-taps.txt)

~~~sh
uv run --no-project --with cupy-cuda12x==14.2.0 --with nvidia-cuda-nvrtc-cu12==12.9.86 --with nvidia-cuda-runtime-cu12==12.9.79 python scripts/check_low_tap_frobenius.py 1257787 < data/degree-1257787-reducible-taps.txt
~~~

The two normalized-width tables use the same factor tables and verification commands as the spacing tables below. Substitute `complementary-width-5-1228.csv` and `complementary-width-1230-2292.csv` for the corresponding `symmetric-witnesses` filenames. To check sharpness, run

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_complementary_width.py --sharpness
~~~

The ranges with $b\le13$ use the pinned Cunningham table and two small supplements. The third order check verifies the alternative witnesses in multiples of eight. The census uses PARI/GP and accepts its executable path with the --gp option.

~~~sh
curl -fsSL https://raw.githubusercontent.com/postvakje/Reformatted-Cunningham-Project-tables/dff2e282ff15399b16b4fb840a410aa2a37076b7/pmain422_table2-.json -o /tmp/gf2-cunningham.json
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --end 1228 --symmetric --factor-table /tmp/gf2-cunningham.json --factor-table data/mersenne-1207-1228-factors.json --verify data/symmetric-witnesses-5-1228.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 1230 --end 2292 --step 2 --symmetric --factor-table /tmp/gf2-cunningham.json --factor-table data/mersenne-even-2182-2292-extra.json --verify data/symmetric-witnesses-1230-2292.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_product_range.py --start 8 --end 2288 --step 8 --symmetric --factor-table /tmp/gf2-cunningham.json --factor-table data/mersenne-even-2182-2292-extra.json --verify data/symmetric-witnesses-multiples-of-eight-through-2288.csv --jobs 4
uv run --no-project --with python-flint==0.9.0 python scripts/check_complementary_taps.py --census
uv run --no-project --with python-flint==0.9.0 python scripts/check_complementary_taps.py --local-cutoff 16
~~~

To search another multiple of eight, export one representative per even-spacing reciprocal pair that passes factor parity and exponent coprimality. For example, the file below includes the certified degree-9576 witness.

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_complementary_taps.py --candidates 9576 > /tmp/gf2-9576-candidates.csv
~~~

The following commands replay the polynomial-tail theorem, list the 55 trinomial witnesses and verify the published degree-1229 factors.

~~~sh
lake build GF2Sparse.BinomialTail
lake env leanchecker -v GF2Sparse.BinomialTail
uv run --no-project --with python-flint==0.9.0 --with sympy python scripts/check_binomial_tails.py --list --powers --factors-1229 .lake/ratio-factors.csv
cmp .lake/ratio-factors.csv data/degree-1229-product-ratio-factors.csv
~~~

Lean checks the degree-2520 witness with one theorem per prime-index power. The following commands build the certificate and independently replay its module. [Lean certificate](GF2Sparse/Witness2520.lean) · [Generator with the --separate-powers option](scripts/make_packed_table.py)

~~~sh
lake build GF2Sparse.Witness2520
lake env leanchecker -v GF2Sparse.Witness2520
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

The following commands check the two sets of degree-2047 logarithms and the uniform order bound for seed degrees at least 40.

~~~sh
lake build GF2Sparse.OreClassLogs2047 GF2Sparse.OreCircle2047
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_logarithms.py --bound 11 --seed 0x805 --cap 31
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_logarithms.py --seed 0xa01 --cap 31
uv run --no-project --with python-flint==0.9.0 python scripts/check_ore_uniform_order.py
~~~

The roots of $X^{2047}+X^3+1$ and $X^{2047}+X^{511}+1$ can be converted in either direction by exponentiation or polynomial substitution. The trace in the degree-11 seed field supplies the exponents. [Coordinate file](data/degree-2047-ore-coordinate.json) · [Verifier](scripts/check_ore_trace_coordinate.py) · [Proof](results.pdf#page=169)

Across all 176 primitive degree-11 seeds and all 176 trace exponents, the 30,800 off-diagonal minimal polynomials have 941 to 1,121 terms. To reproduce the census with NTL, run

~~~sh
c++ -O3 -fopenmp scripts/census_2047_trace_powers.cpp -lntl -lgmp -o /tmp/gf2-ore-trace
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_ore_trace_coordinate.py --census /tmp/gf2-ore-trace --jobs 4
~~~

<a id="verify-degree-2047"></a>

**Verify degree 2047 on a CPU.** The two archives contain 14,602 and 52,488 polynomial masks with their projected logarithms. The command checks every identity by direct field powering, checks the character bound and verifies the twelve sparse witnesses. It uses NTL, GMP, a C++17 compiler and Python. [Degree-18 archive](data/degree-2047-q512-projected.bin.gz) · [Degree-20 archive](data/degree-2047-q1024-projected.bin.gz)

~~~sh
c++ -O3 -std=c++17 -fopenmp scripts/verify_2047_ore_logs.cpp -lntl -lgmp -o /tmp/gf2-ore-logs
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_2047_ore_circles.py --verify-logs /tmp/gf2-ore-logs --sparse-images --jobs 4
~~~

To reconstruct the two matrices for the degree-2047 trinomial, run

~~~sh
mkdir -p .lake/ore-2047
c++ -O3 -std=c++17 scripts/gen_2047_ore_circles.cpp -o .lake/ore-2047/circles
for q in 512 1024; do
  .lake/ore-2047/circles "$q" ".lake/ore-2047/q$q.bin"
  uv run --no-project --with numpy --with sympy --with python-flint==0.9.0 python scripts/check_2047_ore_circles.py --q "$q" --relations ".lake/ore-2047/q$q.bin"
done
~~~

After reconstructing a matrix, the following regenerates its projected logarithms. The two matrix-vector phases use a CUDA 12 GPU and resume from checkpoints. The polynomial phase uses FLINT on the CPU.

~~~sh
uv venv .lake/ore-2047/venv
uv pip install --python .lake/ore-2047/venv/bin/python numpy sympy python-flint==0.9.0 cupy-cuda12x nvidia-cuda-nvrtc-cu12 nvidia-cuda-runtime-cu12
for phase in moments polynomial recover; do
  .lake/ore-2047/venv/bin/python scripts/solve_2047_ore_circles.py "$phase" 512
done
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

The first command checks the degree-1229 field arithmetic. The second replays the divisor bound from the beginning. Add `--continuation-only` to replay the 41 Newton products beyond 818,085,338,814,611,457 using four smaller Lagrange products for each. All 41 Newton residues have gcd one with the cofactor, excluding every remaining prime divisor through 8,317,007,399,072,301,057. The archive also includes the 64 independent Lagrange residues for the first 16 panels. [Residues](data/degree-1229-wheel-continuation.json) · [Order bounds](results.pdf#page=387)

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
