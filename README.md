# Primitive binary pentanomials

Does every positive degree $n$ have a primitive polynomial over $\mathbb F_2$ with at most five terms? This is Conjecture 4.3.5 in the *Handbook of Finite Fields*. The all-degree question remains open here. A primitive polynomial is monic and irreducible, and the residue of $X$ has multiplicative order $2^n-1$. [Stephen D. Cohen, “Weights of primitive polynomials”](https://archive.ymsc.tsinghua.edu.cn/pacm_download/672/12637-dingjt-p2.pdf#page=133)

The [research note](results.pdf) gives the proofs, examples, and references. Its [LaTeX source](results.tex) is included.

## Results

- **Four primitive trinomials and eight primitive pentanomials in degree 2047.** The roots of $X^{2047}+X^{511}+1$ have order $2^{2047}-1$. A trace power gives $X^{2047}+X^3+1$, reciprocation gives two more trinomials, and cubes and fifth powers give eight pentanomials, including $X^{2047}+X^3+X^2+X+1$. The certificate uses 67,087 distinct polynomial logarithms. A CPU can verify the full order while leaving a 549-digit cofactor unfactored. [Proof](results.pdf#page=172) · [Twelve witnesses](data/degree-2047-sparse-witnesses.csv) · [CPU verification](#verify-degree-2047) · [Rank certificates](data/degree-2047-ore-rank.json) · [Lean algebra and arithmetic](GF2Sparse/OreCircle2047.lean)
- **Two constant fields give a linear index bound in every degree $n\ge24$.** Let $d$ be least with $n\le2^{d+1}+2$ and put $q=2^{d-1}$. For any degree-$n$ element $a$, the values $P(a)$ for irreducibles of degrees dividing $2d-2$ or $2d$ generate a subgroup of index at most $83q$. If those values are powers of a candidate root, at most six prime-index tests suffice in prime degree. In degree 1229 the list contains only 36,871. [Proof](results.pdf#page=175) · [Exact checker](scripts/check_factor_field_index.py) · [Lean arithmetic and sieve](GF2Sparse/FactorFieldIndex.lean)
- **A uniform order bound for sparse Ore lifts.** If a primitive binary seed has degree $s\ge40$, every root of its lift of degree $n=2^s-1$ has order greater than $2^{5\sqrt{n+1}}$. A three- or five-term seed gives a lift with the same number of terms. [Proof](results.pdf#page=168) · [Integer certificate](scripts/check_ore_uniform_order.py)
- **Explicit logarithms at roots of irreducible Ore lifts.** Logarithms in the seed field determine products of binary irreducibles with prescribed Frobenius annihilator. For each of two degree-2047 trinomials, Lean and direct powering verify 47 identities through factor degree 31, including 38 individual irreducibles. Counting reduced fractions through degree 1023 gives an order bound above $2^{218}$ for every primitive degree-11 seed. [Proof](results.pdf#page=167) · [Lean certificate](GF2Sparse/OreClassLogs2047.lean) · [Reproduce the logarithms and bounds](scripts/check_ore_logarithms.py)
- **Midpoint powers of primitive trinomials have an exact weight formula.** If one of $0,a,n$ is the midpoint of the other two modulo the odd part $m>1$ of the power, then for $m\le n$ the weight is two plus the $m$th term of Stern's diatomic sequence. For $m>n>7$ there are exactly two sparse images up to reciprocation. The degree-11 trinomial with tap 2 gives a primitive pentanomial at power 13, and the degree-28 trinomial with tap 3 gives one at power 31. [Proof](results.pdf#page=164) · [Lean trace and weight identities](GF2Sparse/SternPowers.lean) · [Check the finite enumeration](scripts/check_trinomial_decimations.py)
- **All powers up to the degree of a primitive trinomial are classified.** For degree $n>7$, strip powers of two from the exponent to obtain $m\le n$. The image is a trinomial for $m=1$. It has five terms precisely when $m=2^k+1$ and two source exponents agree modulo $m$, or when $m=5,7$ and the three distinct residues have a midpoint. Every other image has at least seven terms. At degree 153 all 612 root powers of the four primitive trinomials give exactly sixteen distinct primitive pentanomials. [Proof and exact count](results.pdf#page=160) · [Lean multiplicity and injectivity lemmas](GF2Sparse/TrinomialPowers.lean) · [Independent matrix check with --all-powers](scripts/check_trinomial_decimations.py)
- **In degree 153, four primitive trinomials give sixteen distinct primitive pentanomials.** More generally, in odd degree $n>11$, each divisor of $n$ of the form $2^k+1$ with $k\ge3$ gives one more distinct pentanomial per primitive trinomial, in addition to the third- and fifth-power images. Choosing several such divisors gives an explicit progression of degrees for any prescribed multiplier. [Counting theorem](results.pdf#page=158) · [Lean construction](GF2Sparse/TrinomialPowers.lean) · [Verify or explore a degree](scripts/check_trinomial_decimations.py)
- **At least 2,285 of the first 3,200 degrees have a verified primitive polynomial with at most five terms.** The 35 new degrees from 3073 through 3200 include $X^{3200}+X^{41}+X^{27}+X^{14}+1$. PARI/GP and FLINT checked their full orders. [Proof](results.pdf#page=174) · [35 witnesses](data/product-witnesses-3073-3200.csv) · [Complete factorizations](data/mersenne-3073-3200.json) · [Previous 38 witnesses](data/product-witnesses-2945-3072.csv)
- **There is one family of primitive pentanomials whose roots can still have sparse seventh powers above degree 25.** Up to translation the exponents must be $0,2u,3u,4u,t$ with $7\mid u+2t$. This reduces degree 1229 to 176 supports and two irreducible sources. Across all primitive sources, three successive sparse polynomials can occur under seventh powering only through degree 10. The sharp cutoff for fifth powering is degree 13. In degrees divisible by seven above 14, even a single sparse seventh-power step is impossible for a primitive sparse source. [Proof and examples](results.pdf#page=155) · [Classify seventh powers or list one degree](scripts/check_seventh_power_supports.py)
- **Exactly 72 primitive pentanomials have a root whose fifth power still has a minimal polynomial with at most five terms.** The largest degree is 25, where the two sources are reciprocals. In every larger degree, among primitive trinomials and pentanomials only trinomials give a sparse fifth power. Their twenty-fifth powers have more than five terms. [Proof](results.pdf#page=154) · [Complete enumeration](scripts/check_fifth_power_chains.py) · [Lean certificate for degree 25](GF2Sparse/FifthImage.lean)
- **Every odd degree above seven has at least twice as many primitive pentanomials as primitive trinomials.** Cubing and fifth powering give disjoint sets. Seventh powering can add a third set, with an exact count from the source exponents modulo seven. The six primitive trinomials in degree 17 produce sixteen distinct primitive pentanomials. [Proof](results.pdf#page=152) · [Lean power formulas and a nine-term exception](GF2Sparse/TrinomialPowers.lean) · [Check the disjointness and small degrees](scripts/check_trinomial_decimations.py)
- **Four degree-1229 pentanomials have exactly the same root order.** If $r$ is a root of the polynomial with interior exponents $(166,249,332)$, then $r^7$ is a root of the one with exponents $(332,726,1089)$. These two polynomials and their reciprocals are irreducible. One verified logarithm gives their common index, which is still unknown. It also splits into six factor logarithms of degrees 5, 7, 9, 11, 19, and 21 over $\mathbb F_{2^{20}}$. Among all 639,166 irreducible pentanomials only the first and its reciprocal have a five-term seventh-power image. The same construction gives a proved primitive pair in degree 16. [Proof](results.pdf#page=151) · [Lean theorem](GF2Sparse/SeventhImage.lean) · [Degree-1229 certificate](GF2Sparse/SparseRootModels.lean) · [Census and logarithm task](scripts/check_1229_power_images.py)
- **A fixed Frobenius bidegree can cover only logarithmically many degrees through $X$.** This holds for primitive binary polynomials of every weight when their original terms are rewritten in a root coordinate and its Frobenius conjugate. For each fixed $\varepsilon>0$, the degrees permitting both variables to have degree at most $n^{1/2-\varepsilon}$ have density zero. Writing each exponent in base $2^s$ gives a side length below $2\sqrt n$ for every degree. [Proof](results.pdf#page=150) · [Lean proof of the area bound](GF2Sparse/FrobeniusBoxes.lean)
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
- **A primitive norm in the degree-1229 model over $\mathbb F_4$ has a 599-term binary minimal polynomial.** Adding its coordinate to the $q=1024$ circle equations gives rank 104,968 modulo the unfactored cofactor. This proves the norm has order $2^{1229}-1$. Each of the 29,144 projected norms in the smaller table consequently has exact order equal to the 943-bit cofactor. [Rank proof](results.pdf#page=162) · [Polynomial and verification digests](data/degree-1229-q1024-quaternary-rank.json) · [209,936 scalar moments](data/degree-1229-q1024-quaternary-moments.bin.gz) · [Matrix checker](scripts/check_1229_quaternary_pencils.py)
- **Exactly 29,143 of the 29,144 quaternary norms at $q=512$ are primitive.** The remaining norm, labelled `0x87f`, has index 46,703. The smallest weight of a primitive binary minimal polynomial in the table is 549, attained only at `0x3d02`. The table gives every projected exponent to a common primitive base. [Full order and weight census](data/degree-1229-q512-quaternary-orders.json) · [29,144 exponents](data/degree-1229-q512-quaternary-logs.csv.gz) · [Logarithm derivation](results.pdf#page=134) · [Field and embedding certificates](data/degree-1229-quaternary-models.json)
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
- **Elliptic-curve order certificates in every degree.** At most $\lceil\sqrt{2}\,n\rceil+1$ explicit subgroup-membership targets and order tests for specified small primes suffice in degree $n\ge2$. Prime degrees $n\ge7$ require only the membership targets. For $X^{53}+X^{23}+X^{21}+X^2+1$ the first 30 elliptic logarithms suffice with trial division, or all 38 suffice using the degree alone. [Proof](results.pdf#page=117) · [Point and logarithm checker](scripts/check_elliptic_ray.py) · [Lean arithmetic](GF2Sparse/EllipticRay.lean)
- **Unconditional primitivity in degree 1229 without factoring $2^{1229}-1$, and a single-scalar pentanomial reduction.** For the $q=1024$ Frobenius model $I(X)\mid h_0(X^{1024})+Xh_1(X^{1024})$ ($h_0=T^5+T^2+1$, $h_1=T^3+T$), Hermitian circle norm-projection over $\mathbb F_{2^{20}}$ yields 93,656 exact multiplicative relations (92,910 canonically unique) of exact corank one across all 52,488 binary irreducibles of degree dividing 20. Solving the full $52{,}488\times 52{,}488$ system modulo the unfactored 284-digit cofactor $C$ via AVX2 Wiedemann and FLINT Half-GCD yields all 52,488 projected discrete logarithms $(x^K)^{e_P}\equiv P(x)^K\pmod{I(X)}$, every one directly verified in $\mathbb F_{2^{1229}}$ with $\gcd(e_P,C)=1$. The character-sum bound gives $Q=1294.90>1227$ using only one trial division ($C\bmod 2459\ne0\Rightarrow J\ge 9833$, and $Q=1366.00>1227$ with the sieved wheel), unconditionally proving $I(X)$ (weight 613) and all 111 degree-$\le10$ evaluations $P(x)$ primitive of exact order $2^{1229}-1$. Certifying any of the 639,144 eligible degree-1229 pentanomials now reduces from 3,380 targets to one single scalar $e_r$ with $(r^K)^{e_r}\equiv x^K$. [52,488 verified logs](data/degree-1229-q1024-projected-logs.csv.gz) · [Certificate metadata](data/degree-1229-q1024-certificate.json) · [Direct verifier](scripts/check_1229_q1024_logs.py) · [Single-scalar checker](scripts/check_1229_single_log.py) · [Relation generator & 943-bit solver](scripts/wiedemann_943.cpp)
- **Four exterior-power tests for 100% of six infinite shifted-dyadic trinomial families (including all Mersenne and Fermat degrees).** For any shifted dyadic trinomial $X^{2^s+d}+X^a+1$, any product-one triple or quartet of reciprocal roots satisfies $K(1)=1$ immediately, reducing the quartet dynamics to a 2-variable denominator-free polynomial map with resultants as small as degree 8. This gives 100% all-$s$ squarefree trinomial fourth-test covers for every Mersenne degree $2^s-1\ge7$ using two trinomials ($a\in\{1,3\}$, period 3), every Fermat number $2^{2^k}+1\ge5$ using two trinomials ($a\in\{2,5\}$), every $2^s+2\ge6$ using two trinomials ($a\in\{1,7\}$, period 12), and every $2^s-3\ge13$, $2^s+1\ge5$, $2^s+3\ge5$, and $2^s+5\ge7$ using three trinomials each (plus all odd pullbacks $T(X^m)$). [Certificates](data/shifted-dyadic-trinomial-4test-certificates.json) · [Exact algebraic prover](scripts/check_shifted_trinomial_quartets.py) · [C++ degree-261 checker](scripts/check_trinomial_4test.cpp)
- **At most $0.21925n$ terms in every sufficiently large degree.** At least $2^{n/2}$ distinct primitive binary polynomials meet this bound in each such degree. The proof combines a character sum over field elements with the binary Fourier transform of a function on the middle coefficients. In degree 1229, more than $2^{622}$ primitive polynomials have at most 313 terms using only the degree. The known cofactor bound gives more than $2^{619}$ with at most 311 terms. [General proof](results.pdf#page=98) · [Degree-1229 sieve](results.pdf#page=166) · [Exact calculation](scripts/check_primitive_weight_bound.py) · [Lean check of the earlier 315- and 313-term bounds](GF2Sparse/FourierWeightBounds.lean) · [Shparlinski's earlier bound](https://www.mathnet.ru/eng/ppi820)
- **Lower exponents at most 80 in every degree from seven.** There is a squarefree product pentanomial with exponent gcd one, odd factor count, no inverse pair and no factor of degree at most six. Thirty fixed tap pairs cover the odd degrees above 80, and 24 cover the even degrees above 150. A direct check handles the smaller degrees. At degree 1229 the list includes the irreducible $X^{1229}+X^{64}+X^{43}+X^{21}+1$, which passes every known order projection. [Odd-degree proof and tap list](results.pdf#page=91) · [Even-degree proof and tap list](results.pdf#page=93) · [Coverage checker](scripts/check_fixed_tap_cover.py)
- **Long intervals where every bounded choice of exponents factors.** Fix a distance from the two endpoints and any desired number of factors. In arbitrarily long intervals starting at a prime, every odd-weight polynomial with constant term one supported within that distance has at least that many distinct primitive factors of prime degree. The starts can lie in any prescribed reduced residue class. At a 269-digit prime and its successor, all ten choices from the two tap lists above have two certified primitive factors each, all of degrees greater than six. [Proof](results.pdf#page=94) · [Twenty factor certificates](data/fixed-tap-primitive-factors.csv) · [Checker](scripts/check_fixed_tap_block.py)
- **The first unresolved consecutive degree is 1229.** Lean proves that $X^{1229}+X^{77}+X^{50}+X^{27}+1$ is irreducible. If $K$ is the product of the four known prime factors of $2^{1229}-1$, its root order is $Kt$ with $t>1$ dividing the remaining 284-digit cofactor. A sieved product excludes every cofactor prime through 818,085,338,814,611,457. Both candidate root orders exceed $2^{345}$, and the cofactor has at most 15 prime factors counted with multiplicity. Proving that $t$ equals the cofactor for either root would extend the consecutive range through 1230, since degree 1230 already has a witness. The next gap is 1231. [Product certificate](GF2Sparse/Degree1229.lean) · [Seroussi certificate](GF2Sparse/Seroussi1229.lean) · [Independent check](scripts/check_degree_1229.py) · [Sieved divisor check](scripts/check_1229_wheel.py) · [Factorization](https://factordb.com/index.php?query=2%5E1229-1)
- **Every degree-1229 sparse irreducible has root order above $2^{330}$.** Of the 639,166 irreducible pentanomials, 639,144 have root order above $2^{345}$ and pass all four known-prime tests. All 639,166 have a root order divisible by a prime of the remaining cofactor. The eleven exceptional reciprocal pairs each miss either 36,871 or 46,703. [Proof](results.pdf#page=68) · [Counts by smallest tap](data/degree-1229-pentanomial-census.csv) · [Exceptional supports](data/degree-1229-order-exceptions.csv) · [Independent audit](scripts/check_1229_pentanomial_census.py) · [All 319,583 reciprocal representatives with order-test flags](data/degree-1229-irreducible-supports.csv.gz)
- **An exact quadratic logarithm in degree 1229.** For a root $r$ of $X^{1229}+X^{1066}+X^{533}+X^{163}+1$, take $a=(1+r^{533})^{-1}$. Then $a^2+a+1=r^{163}$ and $(a+1)/a=r^{533}$. The quadratic value generates the same subgroup as $r$, of order greater than $2^{345}$. A second pentanomial gives a quadratic equation relating a fifth root to its 256th power. A binomial multiplier cannot reduce such a direct relation to degree one. The full order of both roots remains open. [Quadratic logarithm](results.pdf#page=101) · [Frobenius equation and proof of minimality](results.pdf#page=102) · [Lean certificates](GF2Sparse/SparseRootModels.lean) · [Reproduce both searches](scripts/check_sparse_root_models.py)
- **A trinomial logarithm in degree 1229 requires a quotient with at least 25 terms.** A relation $1+r^a=r^b$ for a pentanomial root makes its polynomial divide $1+X^a+X^b$. In any degree $n$, if a pentanomial has exponent gcd one and the quotient has $h$ terms, then $27n\le 2(h+2)^3$. For quotients of at most nine terms, the largest possible degree of a primitive pentanomial divisor is 17. Lean also proves that closure of the powers and zero under addition of one characterizes primitivity. [General bound and finite counts](results.pdf#page=103) · [Lean criterion](GF2Sparse/TrinomialMultiples.lean) · [Direct enumeration](scripts/check_trinomial_multiples.cpp)
- **Generators in every prime extension degree $n\ge17$.** For any element $x$ of degree $n$, the values $B(x)$ of binary irreducibles with degree dividing $m$ generate the multiplicative group whenever $2m<n$ and $2n^2\le3\cdot2^m$. In degree 1229, any 44,919 degree-20 irreducibles suffice in every coordinate. In the published $q=1024$ coordinate, the sparse root times $x^{6655}$ factors in auxiliary degrees 7, 13, 19, and 29. [Proof](results.pdf#page=106) · [Exact generation bounds and sparse-root factors](scripts/check_1229_factor_generation.py)
- **Logarithm descent for the six open degrees through 1280.** Explicit field equations meet the hypotheses of the Granger–Kleinjung–Zumbrägel algorithm in each degree. In degree 1229, the two selected sparse roots and all ten period targets of degree at most six are explicit quotients of norms of good degree-16 values. For these targets the least degree is 16 for a quotient and 32 for a single norm to the same field. With linear inputs, the smallest possible constant fields have binary degrees 3744 and 7410, respectively. Taking the norm down to the binary target field gives a further bound in all six degrees. Every nonzero element is the norm of a good degree-16 value and can also be written as a product of at most 15 norms of linear values. [Quotient certificates](data/degree-1229-norm-quotients.json) · [Optimality proof](results.pdf#page=112) · [Lean degree bound](GF2Sparse/NormQuotients.lean) · [Smallest constant fields for linear norms](results.pdf#page=114) · [Single norm factors](data/degree-1229-norm-factors.json) · [Field models](results.pdf#page=109) · [Binary target theorem](results.pdf#page=113) · [Lean numerical bounds](GF2Sparse/NormCoverBounds.lean) · [PARI/GP checker](scripts/check_1229_forward_descent.py)
- **A quadratic Frobenius model for the first open degree.** A four-term polynomial over $\mathbb F_{1024}$ has a factor of degree 1229. Its root satisfies $t=(y^2+vy+u)/(uy)$ with $y=t^{1024}$. Both sparse roots and their common Gauss period are given explicitly in this field. All 1,023 centered norm circles have split quadratic right-hand sides. Norms of the linear and irreducible quadratic values generate the binary target group. [Field data](data/degree-1229-quadratic-frobenius.json) · [Proof](results.pdf#page=107) · [PARI/GP checker](scripts/check_1229_quadratic_model.py)
- **A route around the unresolved factorization.** For any one of 639,144 degree-1229 candidates, 3,380 specified logarithms in a Gauss period coordinate would prove full order. Each logarithm can be computed in the subgroup of 943-bit order. The checker obtains 6,741 polynomial logarithms from those inputs. The new list is a subset of the 3,399-row list. All three published lists use the same coordinate and submission format. The requested exponents remain open. The character-sum and counting methods already certify examples in degrees 47, 61, and 89 without factoring their group orders. Lean checks their 213 logarithm identities. [3,380 targets](data/degree-1229-period-wheel.csv) · [Original target list](data/degree-1229-period-targets.csv) · [Relation checker](scripts/check_period_relations.py) · [Character-sum and counting proofs](results.pdf#page=44) · [Lean logarithm checks](GF2Sparse/FactorBaseExamples.lean)
- **Root orders in 380,093 semiprime degrees.** For odd primes $p<q\le10000$ with $4q\le9p$, every irreducible binary trinomial or pentanomial of degree $pq$ has a root-order prime power $\ell^a$ with $\operatorname{ord}_{\ell^a}(2)=pq$. A prime is forced except at 61 pairs, each with an explicit sparse counterexample to the prime conclusion. At arbitrary sizes in the same ratio range, a root in the product of the two proper subfields would force three support exponents $t,t+P,t+2P$ and a specific gap between the other two. [Proof](results.pdf#page=67) · [Census checker](scripts/check_semiprime_gap.cpp) · [61 counterexample seeds](data/semiprime-gap-seeds.csv)
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

Four degree-1229 candidates share one discrete logarithm task. The JSON gives the binary field modulus, a base of order $C$, and the target as hexadecimal polynomial masks with bit $i$ as the coefficient of $X^i$. Find an integer $0\le e<C$ with $\mathrm{base}^e=\mathrm{target}$ in that field. Replace `--task` with `--log E` to check an answer. The checker computes the exact index of all four roots, and an index of one proves all four primitive. [Download the task](data/degree-1229-seventh-power-task.json)

~~~sh
uv run --no-project --with python-flint==0.9.0 python scripts/check_1229_power_images.py --task
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

To verify the quaternary logarithm table, compile the NTL backend and run the model checker. Add `--orders` to reproduce the full order and weight census. The last command exports the task for the four seventh-power candidates using the table's primitive normalization. For the original two candidates use `--task product` or `--task seroussi`. Supply `--log E` to verify a submitted exponent and obtain the sparse root's exact index. [Model checker](scripts/check_1229_quaternary_models.py) · [Independent binary-field verification](scripts/degree_1229_quaternary_logs.cpp)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/degree_1229_quaternary_logs.cpp -lntl -o /tmp/gf2-quaternary-logs
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_quaternary_models.py --verify-logs /tmp/gf2-quaternary-logs
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

Every degree-1229 irreducible of weight below 521 has a root order divisible by a prime greater than 818,085,338,814,611,457. In the subgroup generated by the two primes below that bound, the minimum weights at orders 36,871, 46,703 and 1,721,986,313 are 605, 579 and 521. An independent check using field traces rules out weight five in all 1,401,128 conjugacy classes. [Counts and minimum witnesses](data/degree-1229-small-subgroup-weights.csv) · [Proof](results.pdf#page=65)

~~~sh
g++ -O3 -std=c++17 -fopenmp scripts/check_1229_subgroup_weights.cpp -lntl -lgmp -o /tmp/gf2-1229-weights
OMP_NUM_THREADS=16 /tmp/gf2-1229-weights
uv run --no-project --with sympy --with python-flint==0.9.0 python scripts/check_1229_subgroup_traces.py
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

All 639,166 irreducible degree-1229 pentanomials pass the first nine exterior-power tests. No product of one to nine roots is one, even with repetitions. Within each polynomial the 94,905,665,941 products of subsets of at most four roots are all distinct, including the empty product. The checker compares 77,221,860 exact residues and tests 3,662,491,560 five-term windows for rank nine. [Short-product computation](results.pdf#page=52) · [Proof for all candidates](results.pdf#page=69) · [Integer checker](scripts/check_1229_short_products.cpp) · [Lean orbit lemmas](GF2Sparse/RootProducts.lean)

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
~~~

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
