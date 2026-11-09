# Bounded decision-diagram probe

8 November 2026. `sea_mdd_probe.py` represents the live forbidden-completion disjunction by a reduced ordered, h-ary decision diagram. It reuses the sparse generator's geometric patterns. It does not change the existing antichain engine.

Reading a letter restricts the first variable, shifts the remaining column indices, and unions the patterns starting at that letter. Equal-child nodes collapse, so the representation recognizes identities such as `OR_a(P AND [x=a])=P`, which subset-antichain reduction alone does not recognize.

There is a semantic qualification: a decision diagram equal to TRUE can mean that every future continuation fails within bounded memory, even if the finite prefix has not completed a forbidden pattern yet. Pruning that state preserves the bi-infinite shift but can reject transient finite prefixes earlier. The relevant comparison is recurrent structure and growth, not equality of transient state counts or raw finite-prefix acceptance.

## Results

Each reported graph was completed. Each has exactly one cyclic strongly connected component.

| Height | MDD states | Labelled edges | Cyclic SCC size | Antichain states | MDD nodes | Union-cache entries | Resident memory | Elapsed time |
|---|---:|---:|---:|---:|---:|---:|---:|---:|
| 4 | 59 | 186 | 52 | 59 | 343 | 192 | 17.6 MB | 0.015 s |
| 5 | 1,540 | 5,191 | 1,420 | 1,600 | 10,548 | 7,216 | 21.8 MB | 0.203 s |
| 6 | 64,585 | 234,976 | 62,946 | 67,689 | 632,085 | 432,956 | 242.9 MB | 9.985 s |

Ordinary floating-point iteration gave the exploratory values

\[
 3.351996777310376,\qquad
 3.543875646282720,\qquad
 3.589695840221527.
\]

These agree with the previously certified enclosures, but the probe does not provide new spectral certificates. Memory is measured resident memory at the end of each clean run. The timings cover pattern generation, graph construction, SCC analysis, and the exploratory iteration.

An initial height-six trial was interrupted during an inefficient numerical-summary step after graph construction. That summary code was fixed, and the table uses the subsequent complete run. No height-seven or height-eight MDD run was attempted.

## Assessment

The reduction in graph states is modest: about 4.6 percent at height six. The decision-diagram nodes and union cache already require roughly 243 MB. This does not justify scaling the current Python implementation under a 512 MB limit.

A next implementation would need native execution, substantial reclamation of intermediate decision-diagram nodes, or a stronger structural invariant. The probe gives no new conclusion at heights seven or eight. It supports the existing height-five and height-six recurrent-component results using a different exact representation of the same positive-pattern shift.
