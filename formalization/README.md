# Formalization — Lean sources for the packing-table certificates

This directory releases the Lean 4 sources for the certificate tier described
in the paper's computational appendix (Section "The status of the formal
results", the `Pi3L2b` / `Pi3Uni` / `pkg_downset` rows): the Z_7 packing-table
certificates for the packing residual of the aligned valuation criterion. The
three
files are released verbatim; the lake project files (`lakefile.toml`,
`lean-toolchain`, `lake-manifest.json`) and the audit probe `AxiomAudit.lean`
were added so the sources build standalone with no external dependencies
(the library imports Lean core only; `lake-manifest.json` lists zero
packages, so no network access is needed).

## Contents

| File | Content |
|---|---|
| `Front583/Pi3L2b.lean` | The packing predicate `pkg` (a Lean reimplementation of the reference Python implementation's `_pkg` routine: lattice x block x key three-dimensional matching, with the M-side bans), the embedded certificate data (120 canonical orbits, 330 demand vectors, 1,761 top-failure vectors), and the main table theorem `l2b_toplevel_certificate` checking all 79,200 points (120 x 330 x two board sides) pointwise. Also data anchors: `dem330_len`, `dem330_sum`, `orbits_len`, `cert_count`, `cert_count_N` (= 204), `cert_count_M` (= 1,557). |
| `Front583/Pi3Uni.lean` | Nine table-domain theorems over the same 79,200-point domain: downset tables on both sides, the uniform layer (Sigma d <= |S| - 1 feasible on both sides), the no-threshold witness `m_no_threshold_witness` (two demands with equal Sigma d = 4, one feasible and one not), `fails_top_only` (all 1,761 failures in the top layer), `mf_upset`, and the failure-orbit counts `mf_orbits` (= 110) / `nf_orbits` (= 2). || `Front583/Pi3Downset.lean` | `pkg_downset`, the general-form downset theorem, proved with plain tactics only: if `slot(d', i) = slot(d, i) - 1` with all other slots equal and `slot(d, i) >= 1`, then feasibility of `d` implies feasibility of `d'` — for arbitrary inputs, not just the 120-orbit table domain. |

## How to build

Toolchain: `leanprover/lean4:4.34.0` (see `lean-toolchain`). Install it with
elan (`elan toolchain install leanprover/lean4:4.34.0`) or point PATH at an
existing 4.34.0 toolchain, then:

```sh
cd formalization
lake build          # builds all three modules, ~35 s cold on an M-series Mac
```

## Axiom audit

After a successful build, print the axiom profile of every quoted theorem:

```sh
lake env lean AxiomAudit.lean
```

The expected output is recorded in `lean_axioms.log` (generated from this
directory's build). Summarised:

- Every `native_decide` certificate theorem (16 of the 17, including
  `l2b_toplevel_certificate` and the whole `Pi3Uni` table) carries the
  kernel-reflection axiom `..._native.native_decide.ax_1_1` (the
  `Lean.ofReduceBool` family) alongside `propext`. These are machine-checked
  by kernel reduction, not pure proofs; the paper quotes them strictly in
  that sense ("certificate grade", flagged `[P, nd]` in the paper's
  status table).
- No theorem depends on `sorryAx`; the three files contain no `sorry`.
- `pkg_downset` (Pi3Downset.lean) depends only on
  `[propext, Classical.choice, Quot.sound]` — the three standard logical
  axioms of Lean — with no `native_decide` and no `sorryAx`. It is a plain
  proof, and it is the only theorem here whose quantification is general
  rather than table-domain.

## Scope boundaries

- Module and file names (`Front583`, `Pi3*`, `2663`) preserve the project's
  internal provenance labels and are retained verbatim for auditability; they
  are provenance anchors, not paper terminology.
- The `val <= 1` hypothesis (min-val-<=1-type criterion in the paper's
  wording) mentioned in the released 2026-10-10 review log
  (`lean_axioms_2026-10-10-review.log`, covering earlier declarations
  `thmA2663_upgraded` and `case2_struct_alpha_iff`) belongs to a different,
  earlier part of the development (the 266.3 criterion layer) and is *not*
  discharged by any theorem here: those theorems are conditional, with the
  `val <= 1` side condition stated as a hypothesis. They are included in the
  review log for provenance; the packing-table sources released in this
  directory are a separate, later module chain.
- The Lean reimplementation of the packing predicate is not proven
  program-level identical to the reference Python implementation; that
  identity rests on three-way machine cross-checks (the 79,200-point sweep
  with zero violations, bit-level reconstruction of the certificate data,
  and a full Lean-side sweep), as stated in the paper's computational
  appendix.
- The general theorem `pkg_downset` is stated with slot-value relations
  (the subtraction form is not yet formalized; instances are discharged
  through the slot relations).

## Provenance

`Front583/Pi3*.lean` are the sources developed in the underlying research
workspace, released verbatim with header comments edited for public release
(the semantics, data, and theorem statements are unchanged).
`lean_axioms_2026-10-10-review.log` is the byte-identical copy of the axiom
audit recorded in the 2026-10-10 independent review (covering the earlier
declarations); `lean_axioms.log` is the fresh audit of this directory's
build.
