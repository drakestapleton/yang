# Certified minimum split-face middle

Contract row 2; base `f10fd3c407abd56760a4d3970beb00f86d179f5b`.
Contract SHA-256: `90c6af671d9b50961d1b338ef9244141bfc3e3010158b4138a2614fa9ff2354f`.
Implementation: `scripts/face_min_cut.py`; dependencies: Python standard library and NumPy only.

## Exact minimization class

`minimum_middle(faces, pinned, source, target)` returns a flat NumPy boolean
middle mask and a Python integer minimum. `faces` is an integer array with four
dense link indices per row; all three masks are flat boolean arrays of the same
link count. Invalid shapes, types, indices, or intersecting forced regions raise
`ValueError`. The caller supplies endpoint anchor masks excluding pins; labels
placed on pinned entries are nevertheless ignored, and returned pinned bits are
always false. Inputs are not modified.

Let P be the pinned links, A and B the source and target free-link anchor sets,
and E_f the set of distinct nonpinned links in face row f. A face is mixed by X
exactly when E_f intersects both X and its complement. Write this set of face
rows as boundary(X). Empty and singleton E_f are never mixed. Repeated rows are
separate unit-cost faces; repeated incidences within a row are not extra costs.

The minimized class is **all** subsets M of the free links satisfying:

- A is contained in M and M is disjoint from B;
- boundary(M) is disjoint from boundary(A) union boundary(B).

The objective is the number of mixed face rows, each costing one, not a count
of cut incidences or cut link pairs. No connectedness, regularity, time-slab,
volume, or topology constraint is imposed. Free links absent from every face
are permitted: an isolated source anchor is included, an isolated target anchor
is excluded, and an unconstrained isolated link is returned false.

Every face split by A has some A-link; avoiding a middle split therefore forces
**all** its free links into M. Faces split by B similarly force all their free
links out. Expand both anchor regions this way once. An intersection proves
infeasibility. Otherwise a labeling extending these disjoint regions is feasible;
there is no propagation along faces not split by the original endpoint masks.

## Unit-face network and checked certificate

Each effective face has auxiliary nodes a_f and b_f. Insert the directed arc
a_f -> b_f of unit capacity, and, for every free link v of the face, arcs
v -> a_f and b_f -> v with capacity H. Forced source and target links receive
terminal arcs of capacity H, where H is the number of input face rows plus one.
Faces with fewer than two distinct free links need no gadget.

For any mixed face, a source-side link forces a_f source-side and a target-side
link forces b_f target-side, so exactly one unit bottleneck is required. An
unmixed face can place both auxiliary nodes with its links at zero cost.
Thus every feasible geometric mask extends to a network cut with exactly its
mixed-face count. Such a cut never needs a hard arc, since its total cost is at
most the number of face rows, strictly below H. Conversely a minimum network
cut cannot cross a hard arc and hence respects the expanded anchors. The
network therefore minimizes exactly the class above.

The implementation deterministically augments integer flow along shortest
residual paths, using iterative traversals rather than recursion. It extracts
the residual source-side mask, then independently recounts actual mixed faces
and checks anchors and disjoint endpoint boundaries on the original face data.
Before returning it checks the **actual flow on every original directed arc**:

- integral flow, nonnegativity, and the arc capacity, including unit bottlenecks;
- forward residual capacity equals original capacity minus that flow;
- flow conservation at every nonterminal, including auxiliary nodes;
- equal source outflow and target inflow, both equal to the recounted primal;
- terminal separation and total network cut capacity equal to that same primal.

An equal feasible flow is a lower bound for every network cut, while the returned
geometric mask attains it. This is an integer primal/flow certificate checked
inside every successful API call, not merely a solver-reported scalar. Certificate
failures raise `RuntimeError`; the checks do not rely on Python assertions.
The four-link local truth table is also checked through Wolfram in
`wilson_face_cut_math.txt` (`math-check`); it is not presented as a general
formal proof of the implementation.

## Narrow acceptance and replay

From the repository root:

```sh
python3 scripts/face_min_cut.py
```

The entrypoint exhaustively enumerates middle masks using a separate set-based
oracle that checks the original class, without reusing anchor expansion or the
network. Its main small graph contains repeated incidences, empty and singleton
effective faces, isolated free anchors, an isolated optional link, and a forced
mixed face with multiple links on both sides. The measured optimum is 3 with
16 admissible masks. Every source/target pin-label combination returns the same
middle. A second geometry has disjoint original anchors but overlapping expanded
regions; exhaustive enumeration finds no feasible mask and the solver rejects it.

It additionally checks all disjoint ternary anchor assignments on six tiny face
families with and without a pinned link, including no faces and duplicate faces.
The measured outcomes are 594 feasible and 378 infeasible cases, all agreeing
with exhaustive enumeration. Repeated calls agree bit-for-bit. Deliberately
corrupted flow certificates are rejected separately for unit capacity,
integrality, conservation, and primal equality.

Observed command: `python3 scripts/face_min_cut.py`.
Timestamp: `2026-11-23T13:20:22Z`; exit status: `0`.
Output: `wilson_face_cut_controls.txt`, mirrored from
`/tmp/yang-mask.R58ROy/face-cut-controls.log`.
SHA-256 of that control log:
`73a5bbfa83067ba2ce5c6d64e3da71154d2defdc10af6dc1c568320214c3887a`.
Wolfram raw query/reply log: `/tmp/yang-mask.R58ROy/face-cut-math.log`,
SHA-256 `d06afdfa8ce9957b38d251d7a1c88e6209330f5cd7fc244182ccdce68c48075a`;
the durable mathematical receipt records its timestamp, query, result and exit status.

## Limits

This is a finite, fixed-pinning, unweighted hypergraph optimum. It does not
optimize the gauge tree, endpoint choice, Wilson action, sampled fields, exchange
loss, or ensemble rate. It imposes no physical lattice structure beyond the
supplied faces. It makes no continuum or mass-gap claim. The flow certificate
uses exact Python integers, but this is trusted scientific code, not a
hostile-input or independently formalized solver. No sampler, axial-tree,
SU(2)/U(1), or Lean integration result is claimed by this row's controls.
No commits or publication were performed by this row's worker.
