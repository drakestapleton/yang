# Sharp interior geometry between the time-zero and time-four slices

This is a finite geometric certificate, not a Wilson-field measurement. On the periodic side-eight four-dimensional lattice, with the previous first-nonzero parent tree fixed, **every mask separating all free spatial links at time zero from all free spatial links at time four splits at least 2050 effective faces**. The cyclic-radius-one and cyclic-radius-two slabs both attain the bound. Their split-face sets are disjoint from one another and from both single-plaquette endpoint boundaries. No split face of either slab has a vertex at either endpoint time.

Scope: contract row 1, base `a002e52ccf1467a6e19c2a96ee9434d6db1736c8`, contract SHA256 `01e9776502eb668f6a7d06c310ee7cce110bc98c3799c6c5b5cb53598adec9e4`. Only `scripts/interior_geometry.py` and this note are owned here. No Monte Carlo, sampler, field, tree optimization, equilibrium, continuum, transfer-operator or mass-gap result is asserted. The associated Lean work is separate; this executable certificate constructs the concrete tree and packing, rather than attributing those constructions to Lean.

## Masks and effective faces

`interior_geometry(lat, pinned)` accepts the existing side-eight `Lattice` convention and the supplied Boolean tree-pin array of shape `(4, num_sites)`. It returns a tuple of four flat Boolean masks, in order:

1. Free links of the spatial 0–1 plaquette at site `(0,0,0,0)`.
2. Every free link based at cyclic time radius at most one: times `7,0,1`.
3. Every free link based at cyclic time radius at most two: times `6,7,0,1,2`.
4. Free links of the corresponding plaquette at site `(0,0,0,4)`.

Pinned bits are false in every returned mask. The implementation does not construct or change the caller's tree. The executable controls independently construct the specified first-nonzero tree: each nonroot child backs up along its first nonzero coordinate; coordinate sum strictly decreases. Positive links are flattened direction first, then C-order site coordinates, with time last.

Exactly as in `middle_cut_probe`, a face is in the effective boundary if and only if it contains a **free** link inside and a **free** link outside the mask. Pinned links carry no effective label. The controls inspect every enumerated face, including wrapped faces.

## Both-arc packing and sharpness

For every free spatial link at time zero, translate that same oriented spatial link through time. Spatial pin status is independent of time for this tree, so all its translates remain free. Join successive translates using their actual temporal plaquette, once along each temporal arc from zero to four:

- Forward link times: `0,1,2,3,4`; face base times `0,1,2,3`.
- Reverse link times: `0,7,6,5,4`; face base times `7,6,5,4`.

These are face-disjoint paths: the plane and spatial base identify the parallel spatial link, and each arc uses different temporal face bases. Different paths may share endpoint links; **faces**, not vertices or links, are the disjoint resource. The script explicitly checks freeness, both incidences of every step, the endpoint times, global uniqueness of all packed face IDs, and use of the periodic seam.

For any whole-slice separator, the labels at the ends of every path differ. A finite binary sequence with different endpoint labels changes somewhere. The corresponding face contains two free links with opposite labels, so it belongs to the effective boundary. Face-disjointness makes these witnesses distinct, giving one required split face per path. This lower bound applies to every mask meeting the slice condition, not just slabs, without searching masks or configurations.

At each time the free spatial-link counts by direction are `{64,456,505}`, totaling `1025`. The two arcs therefore supply `2050` paths. Each slab changes label exactly once on each path. The script checks that these witness IDs equal its **entire** directly enumerated effective boundary, so there are no unaccounted faces. Each slab has exactly `2050` split faces and hence is optimal in this class.

| Mask | Effective faces | Lower temporal face-base times | Actual face-vertex times |
|---|---:|---|---|
| Source local plaquette | 5 | — | — |
| Radius one | 2050 | `{1,6}` | `{1,2,6,7}` |
| Radius two | 2050 | `{2,5}` | `{2,3,5,6}` |
| Target local plaquette | 5 | — | — |

Actual vertex times are obtained from both the bases **and heads** of all four links of every split face. Neither interior boundary touches time zero or four. The four effective boundaries are pairwise disjoint. Overlap of some vertex times between the interior cuts is harmless: their face IDs are disjoint.

## General finite area count and assumptions

Let the periodic four-dimensional side be an integer `L >= 3`, and let the target time be `h` with `1 <= h <= L-1`. Keep precisely this first-nonzero tree, with time the last coordinate, and require opposite labels on the complete free spatial slices at zero and `h`. There is no claim here for an arbitrary pinned frame or a different tree.

The pinned spatial links per time slice in directions zero, one and two are respectively

```
(L-1)L^2, (L-1)L, (L-1).
```

The free spatial count is consequently

```
F(L) = 3L^3 - (L-1)(L^2+L+1) = 2L^3+1.
```

The temporal arcs have lengths `h` and `L-h`. Both are nonempty, and the same face-disjoint construction gives the sharp lower bound

```
2F(L) = 4L^3+2 effective split faces.
```

To attain it, choose a nonempty proper cyclic interval of time bases containing zero and not `h`, and exchange all free links based there. A spatial plaquette stays on one time slice. A temporal plaquette with two pinned parallel spatial links cannot split: all its remaining free temporal links have the same base time and label. Every other temporal plaquette splits exactly when its two parallel free spatial links cross one of the interval's two transitions. Thus each transition contributes exactly `F(L)` faces, with no others.

For the particular symmetric slabs `min(t,L-t) <= r`, require `r < min(h,L-h)`. To avoid all vertices at either endpoint time, the sufficient stronger condition is `1 <= r <= min(h,L-h)-2`. In particular radii one and two give two distinct, endpoint-avoiding, pairwise face-disjoint sharp cuts when `min(h,L-h) >= 4`. The general sharp area count itself does not require endpoint avoidance or antipodality. Direct Python enumeration covers adjacent endpoints, odd side, unequal arcs and the periodic seam; this is not an assertion of all-side endpoint-slice connectivity.

## Finite endpoint-slice connectivity and the weaker wrong class

At time zero and separately at time four, build the co-incidence graph whose vertices are **all free spatial links** at that time. Join every pair of free links lying in a spatial plaquette at that time. Direct enumeration finds one component containing all `1025` vertices at each endpoint. The local observed plaquette supplies one free anchor in each graph. An independent Wolfram graph construction below agrees; spatial pinning is time independent, so that graph is the same at both times.

This yields a finite corollary for this side-eight tree: if a mask contains the local source anchor, excludes the local target anchor, and splits **no spatial plaquette anywhere on either complete endpoint slice**, labels must be constant along every graph edge and therefore across each connected slice. It already satisfies the whole-slice condition, and the `2050` lower bound applies. This is a checked finite graph plus the label-propagation argument, **not an all-sides connectivity theorem**.

Buffers only around the two observed loops are weaker. For a negative control, take the source free support together with all free links on its effective boundary faces. This mask contains the source, excludes the target, and has boundary disjoint from both endpoint boundaries, yet splits only `51` faces and fails to contain the whole free source slice. It also splits a spatial plaquette on an endpoint slice. Thus neither the whole-slice assumption nor the finite corollary can be replaced by local endpoint separation or endpoint-loop buffer constraints.

## Reproduction and observed controls

From the repository root, with Python 3 and NumPy, run the complete geometry control file:

```bash
PYTHONDONTWRITEBYTECODE=1 python3 scripts/interior_geometry.py
```

Observed at `2026-11-23T13:36:16Z`, exit `0`, raw log `/tmp/yang-collar.mLCOQp/geometry-controls.log`, SHA256 `82a4da82310bcf8607adac139a6e1e5f977d3d08ec18135c8e597c92f07feb99`. The tested source SHA256 is `8ddc8255fd3c3f3183008008550fc7b54f6a3a8a060ccf410b389f28d783dbb9`.

```text
interior: faces=2050 lower_base_times=[1, 6] vertex_times=[1, 2, 6, 7] paths_hit_once=2050
interior: faces=2050 lower_base_times=[2, 5] vertex_times=[2, 3, 5, 6] paths_hit_once=2050
endpoint_spatial_graph: time=0 vertices=1025 components=1 local_anchor_count=1
endpoint_spatial_graph: time=4 vertices=1025 components=1 local_anchor_count=1
side8: free_spatial_per_direction=[64, 456, 505] path_count=2050 boundary_counts=[5, 2050, 2050, 5] all_four_boundaries_pairwise_disjoint=True wraparound_checked=True
wrong_class: endpoint_collar_faces=51 endpoint_separates=True endpoint_boundaries_disjoint=True whole_source_slice_contained=False endpoint_spatial_face_split=True
general: side=4 separation=1 radius=0 free_spatial_per_direction=[16, 52, 61] sharp_faces=258
general: side=5 separation=2 radius=0 free_spatial_per_direction=[25, 105, 121] sharp_faces=502
general: side=6 separation=3 radius=1 free_spatial_per_direction=[36, 186, 211] sharp_faces=866
general: side=8 separation=4 radius=2 free_spatial_per_direction=[64, 456, 505] sharp_faces=2050
PASS: geometry only; no configuration generation or field measurement
```

Consistency review located the new `middle_cut_probe.py` import and call of the interface; no existing API was renamed, and no duplicate implementation or unrelated change was required. The full executable geometry module above, not a selected individual assertion, was run. Existing sampling and Lean checks belong to their respective owners.

## Independent Wolfram math-check receipts

These checks use direct coordinate enumeration and symbolic algebra, not Python outputs as inputs. All commands are `mcp__wolfram_wolframlanguageevaluator '<query>' --session XCu3ETh7`, with successful transport exit `0`. The raw queries and returned results are preserved here so the check remains inspectable without the temporary logs.

Health query at `2026-11-23T13:34:07Z`:

```wolfram
{Integrate[x^2,{x,0,1}],WolframAlpha["sqrt(27)/2","Result"]}
(* Out[1]= {1/3, (3*Sqrt[3])/2} *)
```

Log `geometry-wolfram-health.log`, SHA256 `81a2b89669e7fce7a66e8907d43e1dc7bf7869c7ae368d607462fc70cebb6a76`, under `/tmp/yang-collar.mLCOQp/`.

Coordinate enumeration, symbolic sharp count, and transition-sheet check at `2026-11-23T13:35:46Z`:

```wolfram
Module[{l=8,h=4,xyz,pins,free,arcs,sheets},
 xyz=Tuples[Range[0,l-1],3];
 pins=Table[Count[xyz,p_List /; p[[i]]>0 &&
   AllTrue[Take[p,i-1],#==0&]],{i,3}];
 free=l^3-pins;
 arcs={Range[0,h-1],Reverse[Range[h,l-1]]};
 sheets=Table[Select[Range[0,l-1],Function[t,
   Xor[Min[t,l-t]<=r,Min[Mod[t+1,l],l-Mod[t+1,l]]<=r]]],{r,1,2}];
 {Expand[2 (3 n^3-(n-1)(n^2+n+1))],pins,free,Total[free],
  2 Total[free],arcs,sheets}]
(* Out[3]= {2 + 4*n^3, {448,56,7}, {64,456,505}, 1025,2050,
             {{0,1,2,3},{7,6,5,4}}, {{1,6},{2,5}}} *)
```

Log `geometry-wolfram-count-corrected.log`, SHA256 `ba434322a4f1978e942509c46b8fbbea485374f4698ea3bad86e2360ff3f63cc`. First material discrepancy: an initial `FirstPosition`/association lookup query returned `Missing["KeyAbsent", ...]` instead of counts; that result was rejected, not compared as a numeric certificate. The direct coordinate-predicate query above corrected the query, not the Python implementation. The rejected raw attempt is `geometry-wolfram-count.log`, SHA256 `fdf8e053be490a15e1d819bc552e52bb67145d29a0958b71f37ef7c25206d4e3`.

General arithmetic check at `2026-11-23T13:36:16Z`:

```wolfram
{Table[{l,{l^3-(l-1) l^2,l^3-(l-1) l,l^3-(l-1)},4 l^3+2},
 {l,{4,5,6,8}}],
 FullSimplify[2 (3 l^3-(l-1) Sum[l^k,{k,0,2}])==4 l^3+2,
 Element[l,Integers]&&l>=3]}
(* Out[4]= {{{4,{16,52,61},258},{5,{25,105,121},502},
              {6,{36,186,211},866},{8,{64,456,505},2050}},True} *)
```

Log `geometry-wolfram-general.log`, SHA256 `7722d623ece6229c59f625127487437f2a147bb1fd48892e699e4c0045ee789e`.

Independent finite connectivity check at `2026-11-23T13:36:42Z`:

```wolfram
Module[{l=8,xyz,freeQ,vertices,rows,edges,g},
 xyz=Tuples[Range[0,l-1],3];
 freeQ[e_]:=!(e[[e[[1]]+1]]<l-1 &&
   AllTrue[Take[Rest[e],e[[1]]-1],#==0&]);
 vertices=Select[Flatten[Table[Prepend[p,i],{p,xyz},{i,3}],1],freeQ];
 rows=Flatten[Table[With[{i=ij[[1]],j=ij[[2]]},
   Select[{Prepend[p,i],Prepend[Mod[p+UnitVector[3,i],l],j],
    Prepend[Mod[p+UnitVector[3,j],l],i],Prepend[p,j]},freeQ]],
   {p,xyz},{ij,Subsets[Range[3],{2}]}],1];
 edges=DeleteDuplicates[Flatten[(UndirectedEdge@@@Subsets[#,{2}])& /@ rows,1]];
 g=Graph[vertices,edges];
 {Length[vertices],Length[ConnectedComponents[g]],Length /@ ConnectedComponents[g]}]
(* Out[5]= {1025,1,{1025}} *)
```

Log `geometry-wolfram-connectivity.log`, SHA256 `d0061b522ab225eb740d778be7d352f3576263c2051e81ec7e606cf066b81913`.

The Wolfram count and graph results agree with direct Python enumeration. None of these counts is a measured exchange field or a loss rate; those require the separate finite-chain experiment.
