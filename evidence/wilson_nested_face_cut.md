# Joint nested minimum split-face cut

Contract row 1 (general algorithm only); base `0cc5f925842f9b0a639bea4f7a5ca771f9a0ea71`.
Contract SHA-256: `091b3430014619b53d55c8d2389cc6a86004b8b76838e9f9792c1ad4de1a26f2`.
Implementation: `scripts/nested_face_cut.py`, using the unchanged integral residual
network and certificate in `scripts/face_min_cut.py`. Dependencies are NumPy and
the Python standard library. No sampler, neighborhood construction, or field-data
selection is part of this implementation.

## Interface and minimization class

```python
from scripts.nested_face_cut import minimum_nested
small, big, total = minimum_nested(faces, pinned, left, right)
```

`faces` is an integer array of shape `(nfaces, 4)`. Every other input is a flat
boolean array indexed by link, with identical shape. `left` and `right` are
**already-forced protected free-link sets**. They are not endpoint masks to be
expanded: no closure, growth, or boundary protection is added by this function.
Pinned anchor bits, invalid shapes/types/indices, and infeasible constraints
raise `ValueError`. Inputs are not modified. Returned masks are flat NumPy bool
arrays with pins false; `total` is an exact Python integer.

For each face row let E be its distinct free links. A row belongs to boundary(X)
when E meets both X and its complement. Empty or singleton E is never split;
repeated incidences have no extra cost, while repeated rows are distinct unit
costs. The optimization class is precisely

- `left <= small <= big`, and `big` disjoint from `right`;
- both masks are free-link sets;
- boundary(small) and boundary(big) are disjoint.

Minimize `len(boundary(small)) + len(boundary(big))`. There are no volume,
connectedness, regularity, time-slice, topology, or strict-inclusion constraints.
Free links absent from all faces remain valid inputs. In particular, an isolated
left anchor belongs to both returned masks. Unforced isolated links are false.
The routine selects one residual-reachable optimum; it does not claim uniqueness.

## Exact two-layer incidence network

Use height 2 on `small`, height 1 on `big \\ small`, and height 0 outside `big`.
Each free link has high and low nodes indicating height at least 2 and at least
1, respectively; source-side membership means true. A hard arc high(v) -> low(v)
for **every free link, including isolates**, enforces nesting. Force every left
high node to the source and every right low node to the sink using hard arcs.
Pins have no terminal or incidence arcs.

At each face, in each layer, create auxiliary nodes a and b. Add a -> b with
unit capacity, and for each distinct free incident link v add v -> a and b -> v
with hard capacity. A mixed layer forces a source-side and b sink-side, charging
one unit. A constant layer can put both auxiliaries with its links at zero cost.
Faces with fewer than two distinct free links need no auxiliaries or arcs.

In addition add the hard arc a_high -> b_low. Together with the incidence arcs,
this is a linear-size encoding of **high(v) -> low(w) for all free v,w in that
face**. Thus no face contains both a height-2 link and a height-0 link. For nested
masks, splitting both thresholds is equivalent to exactly that forbidden span.
This is stronger than per-link nesting; that constraint alone would not prevent
a face being charged twice. A permissible face has height range at most one.

All capacities are Python integers. With m input rows choose `H = 2*m + 1`.
Any admissible geometric labeling extends to a network cut whose cost is its
total number of threshold splits, at most `2*m`, strictly less than H.
Conversely any cut of cost below H respects every hard implication and has
capacity at least its decoded geometric objective. An optimum geometric labeling
therefore extends to an optimum network cut; a network optimum below H decodes to a geometric
optimum. There is no floating infinity or fixed-width capacity arithmetic.

### Infeasibility is decided before augmentation

Intersecting left/right sets are impossible. A face meeting both left and right
is also impossible: it is forced to contain heights 2 and 0. These are the only
obstructions. If neither occurs, assign height 2 on left, 0 on right, and 1 on
every other free link. No face then has span two, so this is a finite feasible
witness. This proves both rejection and feasibility using actual free incidences;
it does not rely on thresholding a possibly overflowed max-flow value.

### Checked finite certificate

The reused solver performs integral shortest-residual-path augmentation and
extracts source reachability when the sink is unreachable. Before returning,
the implementation recomputes both free boundaries and checks anchors, pins,
nesting, and disjointness. The shared certificate then inspects every original
arc: integral nonnegative flow within capacity, exact forward/reverse residual
agreement, conservation at every internal node, and equal source outflow, sink
inflow, cut capacity, and recomputed geometric total. These checks certify a
feasible flow and cut of the same integer value, not an augmentation counter.
No external flow package or approximate solver is used.

## Independent tiny oracle and semantic controls

`python3 scripts/nested_face_cut.py` runs the entire owned control module. Its
oracle enumerates two boolean masks independently, rejects pairs using direct
subset and boundary-set tests, and minimizes their direct row counts. It does
not enumerate graph cuts or reuse the reduction's height/auxiliary constraints.

The exhaustive family covers all multisets of up to two nonempty face supports
on three links, every pin set, and every disjoint left/right labeling of the
free links. Repeated incidences pad supports to four entries. Additional controls
include empty graphs, all pins, isolated anchors, unforced isolates, duplicate
four-link hyperedges with a required two-versus-two split, and a two-step chain
whose two cuts are both necessary. That chain becomes infeasible if its supplied
anchors are incorrectly expanded: it directly tests the no-expansion contract.
Every oracle comparison also checks that all inputs remain unchanged.

Semantic negatives distinguish classes rather than relaxing the oracle:

- A direct left/right face admits two equal endpoint-separating masks if one
  drops boundary disjointness, but both split that same face. The exported
  optimization must reject it. Per-link nesting alone would incorrectly admit it.
- Crossed masks on two faces can have disjoint boundaries while neither contains
  the other. They are not themselves members of the nested class. This control
  is not a proof of the separately supplied uncrossing theorem.

Malformed input, contradictory anchors, false primal values, and fractional
certificate flow are rejected by explicit negative controls.

## Portable reproduction and receipts

Run from the repository root, with Python 3 and NumPy:

```bash
export PYTHONDONTWRITEBYTECODE=1 VECLIB_MAXIMUM_THREADS=1
export OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
python3 scripts/nested_face_cut.py
python3 scripts/face_min_cut.py
```

The second command is the complete existing network control module, not a
selected subset of its cases. These controls concern finite combinatorial
geometry only. Actual side-eight neighborhood construction, performance,
four-mask separation, orbit measurements, and comparisons with endpoint collars
are integration responsibilities and are not claimed by this worker.

### math-check

Wolfram Language query (session `PGZhjyai`, saved result in
`/tmp/yang-local.5bzC63/nested_math.log`):

```wolfram
With[{rows=Tuples[Range[0,2],4]}, {
 And@@Map[Function[h, With[{a=Min[h],b=Max[h]},
  (Length[Union[Boole[Thread[h>=1]]]]==2 &&
   Length[Union[Boole[Thread[h>=2]]]]==2)==(b-a==2)]],rows],
 And@@Map[Function[h,
  Count[{1,2},k_/;Min[h]<k<=Max[h]]==Max[h]-Min[h]],rows],
 FullSimplify[2 m < 2 m+1, Element[m,Integers] && m>=0]}]
```

Recorded reply: `Out[2]= {True, True, True}`. This checks the threshold/span
identity for four incidences and the exact hard-capacity inequality, not lattice
physics or measured attenuation. The independent pair oracle above checks the
implemented reduction separately.

### Final focused control receipt

Observed environment: Python `3.14.6`, NumPy `2.5.3`.
Start `2026-11-23T14:32:32Z`; finish `2026-11-23T14:32:33Z`.
Both complete module commands above exited `0`.
Log: `/tmp/yang-local.5bzC63/nested_controls.log`.
SHA-256: `eee02600ef3d09ded4f872a0d0b25c73a0b7d571912acba43b9d1e9080a6e686`.

Portable output from the nested module:

```text
independent pair oracle: 2311 cases; 307 infeasible
anchors not expanded; pins, isolated links, repeated rows/incidences: PASS
semantic negatives: double-split and crossed masks are inadmissible: PASS
invalid-input controls: 9; certificate corruption controls: PASS
```

The unchanged existing module also passed its complete exhaustive and certificate
controls (`admissible=16`, minimum/certified flow `3`; tiny families
`feasible=594 infeasible=378`). These are quoted control outputs, not side-eight
measurements.

Artifact SHA-256:

- `scripts/nested_face_cut.py`:
  `b38e814ac6886e863251740952c2b268fca2ec7904f2ba67e4ba5b8c4dca869a`
- unchanged `scripts/face_min_cut.py`:
  `28880504fb032c06995c7e7500bdc19dab2237383698d7bb785854098e30b72e`
- `nested_math.log`:
  `087f17376a81ebf6b2feb9e24f665949896b199ecc943a5139bd44473be60696`

Consistency check found the integration caller in `scripts/local_neighborhood.py`
using the exact four-argument interface and supplied free-link protected sets.
No existing exported signature, duplicate solver, or caller was changed by this
worker. The scope is only the new solver/control module and this evidence file;
the existing residual network is unchanged. The interface is ready for the
parent's side-eight integration. No commits, publication, key use, GPU work, or
sampler changes were performed by this worker.
