# Gallai Path Decomposition — Verified Constructions, a Classification Programme, and Conditional Reductions

## Overview

This repository accompanies the paper *Verified constructions, a classification programme,
and conditional reductions for Gallai's path decomposition conjecture* (`paper/main.pdf`).

Gallai conjectured (1966) that the edges of every connected graph on `n` vertices can be
decomposed into at most `⌈n/2⌉` paths. The paper is a self-contained study organised around
three kinds of results:

1. **Exact constructions** — the exact path number `p(K_{4,n}) = (n+1)/2` for every odd
   `n ≥ 3`; a structure theory and a ring-closure theorem reducing the even columns of the
   odd-`n₁` case of the Constantinou–Ellinas problem to finitely many base instances
   (columns `n₂ = 2, 4, 6` closed; columns `n₂ = 8, 10` closed except five named bases);
   and a chain theorem for odd clique chains (`p(G) ≤ ⌊n/2⌋` for `b ≥ 2` blocks,
   `p(G) ≤ ⌊n/2⌋ − 1` for `b ≥ 4`), via a new decomposition lemma for complete graphs of
   odd order minus an arbitrarily prescribed Hamilton path.
2. **A classification programme** — the prime-family theorem (for `n = p+1` with `p ≥ 7`
   prime, `p ≡ 3 mod 4`, every non-infinity placement regime is dead), corrected Fourier
   identities for the infinity branch, and the registered evidence structure of the
   exception-set candidate.
3. **Conditional reductions and formalisation** — an endpoint-budget framework whose
   budget conjecture `K` implies Gallai's conjecture, a conditional chain registering
   Gallai against an explicit eight-item premise ledger, per-domain theorem-form closure
   of the aligned valuation criterion for `N ∈ {6, 8, 10, 12}`, Lean formalisations, and
   a machine-account layer for a six-family covering identity.

## Results at a glance

| Theorem | Status | Verification |
|---|---|---|
| `p(K_{4,n}) = (n+1)/2` for odd `n ≥ 3` (and `p(K_{4,1}) = 2`) | Theorem (paper proof, complete) | Paper proof (lower bound + closed-form construction + small-case witnesses); Lean formalization `pNumK4n_odd_all` (axioms `[propext, Classical.choice, Quot.sound]`, no `sorryAx`); independent recheck script |
| `p(K_{2k+1}) = k+1` for `k ≥ 1` | Theorem (paper proof, complete) | Paper proof; Lean formalization `pCompleteOdd` (standard axiom profile) |
| Ring-closure theorem (column closure for even `n₂`) | Theorem (paper proof, complete) | Paper proof; 280 parameter pairs re-checked by the independent recheck script; witnesses verified by two independent implementations |
| Odd clique chain theorem (`b ≥ 2`: `⌊n/2⌋`; `b ≥ 4`: `⌊n/2⌋ − 1`) | Theorem (paper proof, complete; domain: all blocks of order ≡ 3 mod 4) | Paper proof; construction-level machine anchors; **no Lean formalization** |
| Fan-type theorems admitting a block of the even-degree subgraph of maximum degree ≥ 4 | Theorems (paper proofs, complete; Lean formalization in progress) | Paper proofs; 166 + 413 tested instances with zero violations; five `sorry` placeholders remain in the Lean sources and are never quoted as machine-verified |
| Budget conjecture `K` ⇒ Gallai's conjecture | Theorem (paper proof, complete) | Paper proof; conjecture `K` itself open, zero violations on five exhaustively enumerated domains (39,027 graphs / 178,860 instances) |
| Prime-family theorem (non-infinity regimes, `n = p+1`, `p ≡ 3 mod 4`, `p ≥ 7`) | Theorem (paper proof, complete; infinity branch open) | Paper proof; 86-prime arithmetic re-check in the recheck script |
| Corrected Fourier identity for the infinity branch | Theorem (paper proof, complete; falsified predecessor documented) | Paper proof; exact `Z[ω]` arithmetic on all infinity placements at `k = 3, 6, 10`; the superseded form's failure on the `K₃` configuration is reproduced by the recheck script |
| Aligned valuation criterion, per-`N` closure at `N ∈ {6,8,10,12}` | Theorem-form per `N` (general `N` open) | Three-tier finite search proved complete and terminating on paper; zero residue on 588 / 30,760 / 634,960 / 7,798,903 instances; Lean kernel-checked instance counts and ledgers |
| Six-family covering identity | Paper candidate (independently re-audited; **not** mechanized) | Paper proofs of both directions plus an independent from-scratch re-derivation audit; machine checks run in a one-way no-`V₇` superset reading |
| Budget conjecture `K` / exception-set uniqueness / general-`N` existence half | Open | Machine evidence only; see paper Sections 4–5 |

## Paper

- `paper/main.pdf` — the compiled paper (60 pages).
- Source: `paper/main.tex` + `paper/sec-*.tex` + `paper/refs.bib`.

## How to verify

```bash
# 1. Rebuild the paper (tectonic; any recent TeX distribution works too)
cd paper
tectonic main.tex        # produces paper/main.pdf

# 2. Run the independent recheck script (pure Python 3, no dependencies)
cd verification
python3 checks.py        # writes check_results.json; exits nonzero on any failure
```

`verification/checks.py` is a self-contained, from-scratch re-verification script (no
project research code is imported; it verifies against the SHA-256-pinned source snapshot
in `verification/snapshot/`). It runs ten checks in about three seconds and covers: the
corrected
Fourier identity (including reproduction of the superseded form's failure), the
block-versus-global-degree witness, the ring-closure construction (280 parameter pairs),
the `K_{4,n}` construction (95 parameter values), the non-infinity prime-family arithmetic
(86 primes), the odd-clique local engine (odd `j ≤ 121`), the `K₉@36` census ledger
arithmetic, the non-infinity death table accounting, the Lean placeholder scan, and
snapshot integrity (SHA-256). A PASS is an execution record, not a certificate of global
correctness.

The per-theorem machine anchors (scripts and certificate files) are referenced in the
paper's computational-appendix table and are released with the paper.

## Formalization

The Lean development (toolchain `leanprover/lean4:4.34.0`) certifies a precise subset of
the paper's statements; every quoted declaration carries an audited axiom profile — e.g.
`pNumK4n_odd_all` and `pCompleteOdd` rest on the standard three axioms only, while
`native_decide` certificates carry the `Lean.ofReduceBool` kernel-reflection axiom and are
quoted as "machine-checked by kernel reduction", never as pure proofs. An axiom audit
(`#print axioms`) accompanies the released sources; the Fan-type theorem chain carries
five declared `sorry` placeholders and is cited strictly as paper proofs with
formalization in progress.

## Scope and limitations

The paper states every claim at its verified strength. In particular it does **not**
claim: closure at `L ≥ 13`; general-`N` paper closure of the covering identity (the
general-`N` existence half is open); completeness of the four-piece (E)+(R) landing;
paper closure of the general-`L` uniform-construction account; full closure of the
channel-or-menu dichotomy programme; or an unconditional theorem-form statement of the
aligned valuation criterion (its Lean formalization is a bound under an unproved
hypothesis). Machine evidence on finite domains is never extrapolated; key-weighted and
instance-weighted accountings are kept separate; and the `N = 14` affine-normalized
domain's equivalence to exhaustive enumeration is unproven. Open problems are collected
in Section 5 of the paper.

## Citation

```bibtex
@misc{gallai-path-decomposition-2026,
  title  = {Verified constructions, a classification programme, and conditional
            reductions for Gallai's path decomposition conjecture},
  author = {Independent Researcher},
  year   = {2026},
  note   = {Preprint, 60 pages}
}
```

## License

This repository is released under the MIT License.

## Acknowledgment

Parts of the mathematical and bibliographic work in this project — including automated
literature cross-checking, large-scale machine verification of the computational
accounts, and the Lean formalizations — were carried out with computer assistance (AI-assisted
research). The division of labour is summarised in the paper's computational-methodology
section, and every machine-checked claim is stated at its measured strength with explicit
trust boundaries.
