# gf2fun research handoff

Updated 28 November 2026 at 14:47 UTC. The public default branch is `master`. The latest merged research at this checkpoint is `bc8ad75`. The goal is to prove that every positive degree has a primitive binary polynomial with at most five nonzero terms. Every degree through 1,228 has a verified witness. Degree 1,229 and the all-degree conjecture remain open. [Research overview](README.md) · [Proofs](results.pdf)

## Where degree 1,229 stands

All trinomials are reducible. Of 639,166 irreducible pentanomials, 639,144 pass all four known prime-index tests. Identifying a polynomial with its reciprocal leaves **319,572 surviving pairs**. The remaining 284-digit composite cofactor of $2^{1229}-1$ has at most fourteen prime factors counted with multiplicity. The four known primes and the exact cofactor are defined in the verifier. [Support census](data/degree-1229-irreducible-supports.csv.gz) · [Known failures](data/degree-1229-order-exceptions.csv) · [Order verifier](scripts/check_degree_1229.py)

The incompressibility target is to **encode the tap triple of a failing pair**, given the degree and the failed prime. A 14-bit index for each remaining prime would leave at least $319572-14\cdot2^{14}=90196$ primitive pairs. Conversely, a counterexample would force one prime to exclude at least 22,827 pairs. The missing step is an upper bound on how many sparse pairs can fail the same unknown prime. [Counting proof, p. 387](results.pdf#page=387)

## What is already on the default branch

- Given the degree, two bits identify any reciprocal pentanomial class of root order strictly below $127n/7$. At equality five classes occur in a single subgroup in every degree $7\cdot127^j$. [Sharp bound and examples](results.pdf#page=424)
- For a prime divisor $p$ of $2^n-1$, write $h=(2^n-1)/p$. Across all tests with $h<341n/10$, two bits and the degree identify any failing pentanomial pair. For $h\le300n$, at most ten pairs fail a specified prime, and at most eighteen fail any such prime in one degree. Both maxima occur in degree twelve. From degree 23 onward all sparse irreducibles pass every test in this size range. The unknown degree-1,229 tests have much larger subgroups. [Proof and table](results.pdf#page=425) · [Exact code sizes and decoder](scripts/check_prime_index_codes.py)
- Seven trace positions recover all four known test outcomes on 454 degree-1,229 supports. A proposed non-Frobenius multiplier preserving a survivor's unit traces can be checked by gcd against the cofactor. A genuine extra symmetry yields a proper factor. [Sample and proof](results.pdf#page=423) · [Multiplier checker](scripts/check_1229_unit_trace_probes.py)

To reproduce the small-subgroup table and list its ten-pair example, run these from the repository root.

```bash
uv run --no-project --with python-flint==0.9.0 python scripts/check_prime_index_codes.py
uv run --no-project --with python-flint==0.9.0 python scripts/check_prime_index_codes.py --degree 12 --prime 3
```

## Degree 48,617 verification in progress

Draft PR #66 contains the five directly tested witnesses, the factorization and the archived integer certificate. NTL exhausted all 24,308 reciprocal trinomial representatives. The four irreducible taps are 4,275, 9,095, 14,600 and 17,166. The pentanomial has taps 5, 10 and 25. NTL and FLINT independently checked irreducibility and all nine factor-index powers. Powers of the trinomials give 26 further distinct five-term polynomials. The full-order conclusion is pending the final integer certificate replay. [Draft PR and data](https://github.com/rudi-cilibrasi/gf2fun/pull/66)

On Rudi's checkout, the running replay writes to `.lake/degree-48617/primality.log`. It has verified the eight smaller primes and the factor product. Its remaining input is the 1,278-record PRIMO certificate for the 14,377-digit factor. The working copy for this PR is `.lake/degree-48617/worktree`. After a successful replay, publish the prepared proof and PDF from that worktree, merge #66 into `master`, and update this section. To reproduce independently from the PR checkout with PARI/GP installed, run the following command.

```bash
uv run --no-project --with python-flint==0.9.0 python scripts/check_mers_project_orders.py --table data/degree-48617-orders.json
```
