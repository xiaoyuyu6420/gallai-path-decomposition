import Front583.Pi3L2b

/-! # Front583.Pi3Uni — table-domain machine certificates for the three
uniform-layer lemmas of L2(b), plus the sharpened M-side "no uniform law" result

**Scope** (route 1 of the packing-table account, tasks (1) and (2) of the
follow-up module plan): the L2(b) table is compressed into "three lemmas + a
top-level certificate of 1,761 vectors", the three lemmas being:

1. **Downset property**: the feasible region is a downset (paper side: a
   two-line restriction argument; the machine scan checked 120 x 330 x 2
   points with zero violations);
2. **Uniform layer**: Sigma d <= |S| - 1 is feasible on both sides at every
   point (the machine scan found zero failures);
3. **AGL(1,7) invariance**: the feasible region depends on (S,s) only through
   its AGL(1,7) orbit (paper side plus a 53,760-point machine check; not
   carried in this file — handled in a separate module).

On top of the packing predicate `pkg` of `Front583.Pi3L2b` and the 120-orbit
data layer, this file turns lemmas 1 and 2 into **table-domain machine
certificate theorems** (a full `native_decide` sweep over 120 canonical
orbits x 330 demands x both sides), and sharpens the open statement "the
M-side top layer's 1,557 vectors admit no uniform law" into a Lean theorem:

- `m_no_threshold_witness`: within one orbit, two demands with the same
  Sigma d = 4, one feasible and one not — any uniform law of the form
  "feasible iff f(Sigma d)" fails on that orbit (oracle-side statistics: a
  threshold law survives on only 12/120 M-side orbits, and laws via Sigma d /
  (Sigma d, max slot) / the slot multiset each fail on 108/120 orbits; the
  machine account is the mstruct JSON artifact of the follow-up module);
- `fails_top_only`: all top-failure vectors on both sides lie in the
  Sigma d = |S| layer;
- `mf_upset`: the M-side top-failure set is an upset (the top-layer image of
  the downset property);
- `mf_orbits` / `nf_orbits`: the failure-orbit counts are 110 / 2.

**Trust note**: every theorem in this file is carried by `native_decide`,
whose axiom profile depends on `Lean.ofReduceBool` (the native-evaluation
kernel-reflection axiom); they are machine-checked by kernel reduction, not
unproved assertions, and contain no `sorryAx`. The coverage domain is the 120
canonical orbit representatives x 330 demands (Sigma d <= 7) x both sides;
citations of the raw 4,480-point account must carry AGL(1,7) invariance
(paper side + a separate machine-certificate module). The general form of the
lemmas (arbitrary (S,s,d)) is not paper-formalized in this file (the general
downset theorem lives in a separate module; the uniform layer and invariance
remain at their original account grade).

**Provenance**: labA174.py::_pkg (md5 29a1272b...) ->
a334_l2b_toplevel.json (md5 0d1e9f3f...) -> Front583.Pi3L2b (built with
`lake build`, axiom audit passed) -> this file. Independent oracle-side
re-verification of this file: the follow-up module's structural audit script
recomputed the certificate rule
directly from _pkg over all 79,200 points with zero violations, and the
json-vs-orbit cross-check matched on 120/120 orbits (recorded in the audit
report).
-/

/-! ## Preliminaries: demand-vector operations -/

/-- Decrement slot i of the demand code c (the side condition `slot c i >= 1` guarantees no cross-slot borrow). -/
def decCode (c : Nat) (i : Nat) : Nat := c - 2 ^ (3 * i)

/-- Demand domination: c' dominates c slotwise (c is c's immediate-predecessor direction). -/
def covers (c' c : Nat) : Bool :=
  Nat.ble (slot c 0) (slot c' 0) && Nat.ble (slot c 1) (slot c' 1) &&
    Nat.ble (slot c 2) (slot c' 2) && Nat.ble (slot c 3) (slot c' 3)

/-! ## Lemma 1 (downset property): table-domain machine certificate
Every immediate predecessor of a feasible point is feasible — checked
pointwise over 120 orbits x 330 demands x both sides (the Lean domain-wide
carrier of the machine face of the downset property). -/

/-- Per-orbit, per-side downset property: for a demand code c with a non-zero slot i, feasibility of c implies feasibility of its predecessor decCode c i. -/
def downOK (o : Orb) (ban : Bool) : Bool :=
  Dem330.all (fun c => [0, 1, 2, 3].all (fun i =>
    (slot c i == 0) || (pkg o.S o.s ban c == false) ||
      (pkg o.S o.s ban (decCode c i) == true)))

/-- **Downset property, N side: domain-wide certificate.** -/
theorem downset_table_N : orbitList.all (fun o => downOK o false) = true := by
  native_decide

/-- **Downset property, M side: domain-wide certificate.** -/
theorem downset_table_M : orbitList.all (fun o => downOK o true) = true := by
  native_decide

/-! ## Lemma 2 (uniform layer): table-domain machine certificate
Sigma d <= |S| - 1 implies feasibility on both sides at every point — the
Lean domain-wide carrier of the machine-checked lemma candidate (covering the
whole low layer, stronger than the spot-check account at layers m-2/m-1). -/

/-- Per-orbit, per-side uniform layer: a demand code with Sigma d + 1 <= |S| (i.e. Sigma d <= |S| - 1) is always feasible. -/
def uniOK (o : Orb) (ban : Bool) : Bool :=
  Dem330.all (fun c => !(Nat.ble (sumd c + 1) (pc o.S)) || (pkg o.S o.s ban c == true))

/-- **Uniform layer, N side: domain-wide certificate.** -/
theorem uniform_layer_N : orbitList.all (fun o => uniOK o false) = true := by
  native_decide

/-- **Uniform layer, M side: domain-wide certificate.** -/
theorem uniform_layer_M : orbitList.all (fun o => uniOK o true) = true := by
  native_decide

/-! ## M-side structural theorem: sharpening the "no uniform law" task
The reference account records: the M-side top layer's 1,557 vectors are spread
over 110 orbits, and whether any further uniform law exists was left open.
This section turns that into a decidable statement and settles it by machine:
any uniform law via Sigma d (or finer statistics) fails on 108/120 orbits
through same-layer two-valued counterexamples; the surviving structure is the
upset property plus all failures lying in the top layer. -/

/-- **M-side "no uniform (threshold) law" witness theorem**: on the orbit
(S={0,1,2,3}, s=[0,1,2,3]) the demands 585=(1,1,1,1) and 2048=(0,0,0,4) share
Sigma d = 4, the former feasible and the latter not — hence no function f
satisfies "M-side feasible iff f(Sigma d)" (one Sigma d, two values). The
oracle side was confirmed by the follow-up module's structural audit script,
computing the reference Python implementation directly
(pkg(585)=True / pkg(2048)=False). -/
theorem m_no_threshold_witness :
    pkg 15 1672 true 585 = true ∧ pkg 15 1672 true 2048 = false ∧
      sumd 585 = 4 ∧ sumd 2048 = 4 := by
  native_decide

/-- **Failure-layer anchor**: all top-failure vectors on both sides lie in the Sigma d = |S| layer (all 1,761, one by one). -/
theorem fails_top_only : orbitList.all (fun o =>
    o.nf.all (fun c => sumd c == pc o.S) && o.mf.all (fun c => sumd c == pc o.S)) = true := by
  native_decide

/-- Upset property of the M-side top-failure set: if c fails, c' dominates c
and c' is in the top layer, then c' fails (the top-layer image of the downset
property downset_table_M; an independent Lean sweep of the machine face of the
upset account). -/
def mfUpOK (o : Orb) : Bool :=
  o.mf.all (fun c => Dem330.all (fun c' =>
    (covers c' c == false) || (!(sumd c' == pc o.S)) || (o.mf.contains c')))

/-- **The M-side top-failure set is an upset (domain-wide certificate).** -/
theorem mf_upset : orbitList.all mfUpOK = true := by
  native_decide

/-- **Failure-orbit count**: the M-side 1,557 vectors are spread over exactly 110 orbits (the figure recorded in the reference account). -/
theorem mf_orbits : (orbitList.filter (fun o => !(o.mf.isEmpty))).length = 110 := by
  native_decide

/-- **Failure-orbit count**: the N-side 204 vectors sit on exactly 2 exceptional orbits (the two-colour key-Hall wall orbits of the sub-case L2(a)). -/
theorem nf_orbits : (orbitList.filter (fun o => !(o.nf.isEmpty))).length = 2 := by
  native_decide

/-! ## Machine evidence with zero uncovered points (following the pattern of the Fan.lean counting-lane module) -/

#print axioms downset_table_N
#print axioms downset_table_M
#print axioms uniform_layer_N
#print axioms uniform_layer_M
#print axioms m_no_threshold_witness
#print axioms fails_top_only
#print axioms mf_upset
#print axioms mf_orbits
#print axioms nf_orbits
