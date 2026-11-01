# Erdős Problem 657: Straus's isosceles-free point sets

[![CI](https://github.com/veljjanoski/erdos657-palomar/actions/workflows/ci.yml/badge.svg)](https://github.com/veljjanoski/erdos657-palomar/actions/workflows/ci.yml)

A Lean 4 proof of a solved statement about
[Erdős Problem 657](https://www.erdosproblems.com/657), prepared for the
[Palomar](https://palomar-registry.org/) registry (submission form:
<https://submit.palomar-registry.org/>).

Erdős asked whether $n$ points in the plane with no isosceles triangle must determine at least
$f(n)n$ distinct distances for some $f(n) \to \infty$. Straus observed that in high dimension
this fails. The proved statement is:

- `Erdos657.erdos_657.variants.straus`: for every $k$ there are $2^k$ points in $\mathbb{R}^k$
  with no isosceles triangle that determine at most $2^k - 1$ distinct distances.

The definitions and the statement in `Challenge.lean` are copied verbatim from
[formal-conjectures](https://github.com/google-deepmind/formal-conjectures) (commit
`a64e959c32c270df4dd0d96d2027481f15750534`), where the statement is stated with `sorry`.

The proof in `Solution.lean` uses the points whose $i$-th coordinate is $0$ or $\sqrt{2^i}$. The
squared distance between two of them is a sum of distinct powers of $2$, so it determines the set
of coordinates where they differ.

## Repository map

- `Challenge.lean`: the statement (with `sorry`) a reader audits.
- `Solution.lean`: the same declarations with a proof.
- `comparator.json`: the declarations `lake comparator` checks.
- `formalization.yaml`: provenance, authorship, automation and review metadata.
- `scripts/`, `test/`, `Gemfile*` and `.github/workflows/ci.yml` come from
  [PalomarTemplate](https://github.com/PalomarRegistry/PalomarTemplate).

Build with `lake exe cache get && lake build`; check with `scripts/verify-comparator.sh` (Linux,
needs `bwrap`).

## Licence

Apache License 2.0, see `LICENSE`. The statement and definitions copied from formal-conjectures
are also under Apache-2.0.
