# Linearity normalization: source, consumers, and evidence

Issue #694; session `mathfix-694-20260922-01`; starting commit
`99d4036e62e7dd4a21637d8f3e313c907afe39dc`. This is an author investigation,
not independent review or an adoption record. The normalization register stays
`pending`; the quotation/padding row stays `open` and is unchanged.

## Mathematical verdict

For a finite-dimensional density operator rho and binary observables A on
F_2^t, put C = E_ab Re Tr(A(a) A(b) A(a+b) rho). The provider's hypothesis
is C >= 1-delta. Its printed conclusion permits any finite pure ancillary
extension, asks for exactly linear binary observables L, and bounds their
average squared operator distance from A tensor I by delta. It is false.
The same conclusion with bound 2 delta is proved without restricting t or
delta. The printed quantifiers are retained as unasserted universal Lean Props.

There are two distance readings. The standard reading uses one density
factor. The literal definition at NV:873-875 uses the density twice, so its
squared distance is the standard distance weighted by rho^2. The two Props
retain these readings separately; neither is a construction input. Both are
formally refuted on the scalar pure input, for which every pure ancillary
extension is idempotent. No mathematical definition or game was changed.
The corrected standard-distance theorem also implies the corrected literal
bound: every density satisfies 0 <= rho'^2 <= rho', and pairing the positive
difference with (L-A)^dagger(L-A) preserves nonnegativity. This comparison is
proved mathematically in the note; no additional Lean comparison theorem is
claimed. The pure examples make coefficient 2 necessary for both readings.

The four-point sign pattern (+,+,+,-) has C=1/4 and best existence error 1,
including arbitrary ancillas. It forces coefficient 4/3, not 2. The note gives
a proof that 2 is the least *universal multiplicative coefficient*: for
f_k(x,y)=(-1)^(x dot y), all Fourier coefficients are +/-2^(-k), C_k=4^(-k),
and the best existence error is 2(1-2^(-k)). Any exact representation has
character projectors, so its scalar correlation is a convex combination of
these coefficients, even on an arbitrary ancilla. A maximizing character
attains the lower bound. The ratios 2/(1+2^(-k)) tend to 2 with positive
index length and delta in (0,1).

This proves minimality among constant-multiple repairs of the printed error
bound. It does not prove that the Fourier-square construction minimizes each
input's error, or determine the optimal bound for every fixed (t,delta).
Indeed that construction has error 3/2 on the four-point example, whereas
the optimum is 1. Its exact error is 2(1-C); the normalization identity is
d_binary^2 = d_operator^2 / 2. These statements must not be conflated.

Alternative candidates: coefficient 1 is refuted in Lean; every coefficient
c<2 is ruled out by the quadratic family. Keeping the printed conclusion
and strengthening C >= 1-delta to C >= 1-delta/2 merely reparameterizes the
correct theorem and changes an input hypothesis unnecessarily. Restricting
delta <= 1, requiring commutation, or disallowing ancillas does not remove the
four-point counterexample. Pointwise rather than averaged closeness is a
separate quotation defect. The proposal changes only the uniform error
coefficient in the conventional operator-distance reading.

## Source inventory

Abbreviations below: NV = `references/nv-paper/fullpaper.tex`;
Q14 = `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex`;
Q8 = `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex`.
Locators refer to the immutable mirrors; none was edited.

| Passage | Use and effect of the correction |
| --- | --- |
| NV:732, 753-760 | All Hilbert spaces are finite dimensional; observables are Hermitian involutions. The retained Props allow all finite spaces and all pure ancillary extensions. |
| NV:866-912, `eq:dist_observables` | The binary measurement calculation gives half the squared operator distance; line 911 equates them. The duplicated density at 875 is separately retained, not silently identified with the standard convention. |
| NV:1074-1113, `thm:qblr`, `eq:qblr-0`, `eq:qblr-1` | Printed statement and complete Fourier-square/Naimark proof. Parseval makes B_u=Ahat_u^2 a POVM; compression gives correlation C, hence operator error 2(1-C). No commutation of input observables is used. |
| NV:1115-1117; 1141-1195, `thm:qblr_game` | The forward reference promises the correlation hypothesis with delta=O(sqrt(epsilon)). The game theorem proves that hypothesis independently; it does not use the incorrect rounding conclusion. |
| NV:1537-1541, within `thm:isotwoplayer` (1307-1331, proof 1479-1598) | The only subsequent application of `thm:qblr` rounds C(a,b). The conclusion is O(epsilon^(1/8)); a factor two preserves this error form. Exact relations and the subsequent P^A definition are unchanged. |
| NV:1544-1596 | Pauli braiding uses exact linearity, then averaged consistency substitutions and relabeling. Neither requires coefficient 1. A universal multiplicative factor only changes the unspecified robustness constant. |
| NV:1347-1356, `cor:epr-test` | Consumes `thm:isotwoplayer` through its exact representation and O(epsilon^(1/8)) robustness. Both interfaces remain as stated. |
| NV:1758, `thm:main`; 1835-1842, 1886-1901, `lem:energy_consistency` | These are all later applications of `thm:isotwoplayer`: energy estimates use unspecified O(epsilon^d) constants and exact linearity. Square roots of a changed universal constant remain universal constants. The later amplification/delegation uses (1924-1957) consume the unchanged `thm:main` interface. |
| Q14:711-725, `thm:linearity` | Quotation, not a proof. Its `approx_delta` absorbs constants; its pointwise phrasing and upper error restriction belong to the separate quotation note. This does not by itself adopt the literal provider correction. |
| Q14:825-832 | Sole invocation of `thm:linearity`. On a fixed (x,z) fiber let eta be its mean squared defect. The exact BLR identity gives C=1-eta/2. Apply the corrected theorem with delta=eta/2, yielding output error <=eta, and then average over fibers. The ancillary basis Option(F_2^(2t)) and unit vector are uniform. |
| Q14:832 | The source additionally assumes zero-state padding in the fixed expanded strategy. Uniform optional dilation does not prove this absorption. This remains open in the adjacent note; normalization sufficiency is not a proof of that source step. |
| Q14:834-849 | Fourier projectors and their sum use exact linearity and L(0)=I, which are unchanged. |
| Q14:851-875 | Self-consistency, both point-product orders, and the symmetric player placements use averaged closeness and Fourier/Parseval comparison. The bound remains poly(epsilon); no exact coefficient 1 is required. |
| Q14:900-977, `lem:qld-xz-lines`; 993-1018, `lem:qld-4-12` | These consume the combined-point conclusion, respectively for line comparisons and affine coarse-graining. Replacing the underlying universal constant preserves the stated polynomial error functions. |
| Q14:1020-1264, `lem:qld-4-13`, `lem:qld-sublines`, `claim:17-1/2/3` | All later uses of combined points and lines in the extended-line argument: 1058, 1121-1132, 1194, 1226, 1238, 1241-1242. They compose polynomial error estimates; the normalization introduces no new domain restriction. Existing subline defects are not certified by this audit. |
| Q14:1267-1411, `lem:qld-4-7` | The low-degree application uses the extended measurements (1278-1282) and point comparisons (1298). Universal prefactors can be increased within the stated polynomial error form; no added hypothesis is needed for this normalization change. |
| Q14:1423, 1464-1661, `lem:qld-construct-the-paulis`, `lem:qld-constructing-the-paulis-helper` | Consumers of the global measurement and delta_S, including 1492, 1584, 1627. Exact projector identities remain unchanged; their approximate inequalities propagate the same error function with universal factors. |
| Q14:1666-1878, `lem:qld-unitary`, `thm:pauli-appendix` | Uses at 1671, 1715, 1793, 1868, 1876 depend on exact Pauli relations and O(delta_S^(1/4)+md/q). A factor from normalization changes only existential universal constants. Other registered extraction defects remain separate. |
| Q8:1431-1447, 1450-1491, 1503-1559 | `thm:pauli`, its qubit reformulation, and canonical-parameter robustness use existential universal a,b. The normalization changes neither the theorem form nor the choice rule parameterized by those constants. This is no certification of the separately pending canonical-parameter correction. |

Searches included both ordinary `ref`/`Cref` and the NV shorthand
`thmref{qblr}`. The latter is essential to find NV:1537. Searches for
`thm:linearity`, `qblr`, the provider identifier, and NV17 found no further
application in the QPBT mirror or the NEEXP Pauli-basis section. Calls to
`qblr_game` at NV:1368,1449,1466 use approximate linearity from game success;
they are not calls to the corrected rounding theorem. The downstream rows
above assess only propagation of this normalization change, not every other
mathematical assertion of those papers.

## Blueprint inventory

At the starting commit and after this change, the transitive `uses` descendant
set of `thm:linearity`, `rem:linearity-import`,
`rem:linearity-distance-normalization`, and `lem:linearity-common-ancilla`
is **empty**. In particular `lem:qld-4-10` uses a direct field-valued proof.
The complete active reference inventory follows. All locations are in
`blueprint/src/chapter/ch15_qpbt_combining.tex`, with statement and adjacent
proof spans derived using `scripts/blueprint_citations.py`.

| Node | Lines after this change | Role |
| --- | --- | --- |
| `thm:linearity` | 112-239 | Existing corrected theorem; public statement and proof unchanged. |
| `rem:linearity-import` | 241-307 | Explains fiberwise use and the still-open padding obligation; unchanged. |
| `lem:linearity-common-ancilla` | 309-337 | Uniform optional space, chosen before the family; unchanged. |
| `lem:linearity-unrestricted-parameters` | 339-362 | New full numerical-domain theorem, proved directly by the same rounding. |
| `rem:linearity-distance-normalization` | 364-403 | Distinguishes the three error claims, states the sharp universal coefficient, and retains pending adoption. |
| `def:linearity-printed-claim` | 405-418 | New unasserted Props; no proof-completion mark. |
| `lem:linearity-four-point-obstruction` | 420-448 | New formal obstruction and refutations for arbitrary ancillary dimensions. |
| `lem:boolean-fourier-transform` | 518-549 | Upstream Fourier identities; explanatory reference, not a consumer. |
| `lem:binary-measurement-distance` | 551-587 | Exact normalization identity; unchanged. |
| `lem:blr-defect-identity` | 589-641 | Converts correlation to defect with factor two; unchanged. |
| `lem:fourier-square-measurement` | 643-700 | Upstream POVM construction; unchanged. |
| `lem:naimark-rounding` | 702-817 | Upstream dilation and exact relations; unchanged. |
| `lem:boolean-representation-stability` | 819-916 | Preserves multiplicative defect as squared output error; unchanged. |
| `lem:qld-4-10` | 1330-1402 | References the import remark solely to distinguish its direct field-valued proof; no linearity assumption or invocation. |

Reproduce the graph with `build_label_index` and `_active_lines` from
`scripts/blueprint_citations.py`: read each indexed statement/adjacent-proof
span, split each `uses{...}` argument on commas, and repeatedly add nodes
whose `uses` set meets the four starting labels. Comment stripping is
essential. Scan ordinary `ref`, `Cref`, `cref`, and `eqref` separately; inspect
the raw chapter for references outside statement environments. No other
chapter contains these active references. The new two proof nodes use the
existing upstream identities, not the printed false propositions.

## Lean consumer and statement audit

The exact changed modules are `Combining/Linearity.lean` and the new
`Combining/Linearity/PrintedClaims.lean`, both under `MIPStarRE/QPBT/`.
The latter is explicitly re-exported by `MIPStarRE/QPBT.lean`; the only
importer of that aggregate is `MIPStarRE.lean`.

Declaration search found exactly one invocation of the existing
`exists_exactly_linear_observables`: its binary-distance companion, now at
`Linearity.lean:188`. The existing common-ancilla theorem, now at line 221,
uses the rounded-observable identity and BLR bound directly. No external
Lean consumer invokes either theorem, the binary companion, or the new
full-domain theorem. The negative Props are consumed only by their refutations.
The normalization identity is used in the binary correlation identity and
binary-distance companion. Its signature and proof remain unchanged.

The foundation chain is
`Defs -> BooleanFourier -> BLR -> NaimarkRounding -> Stability -> Linearity`.
`Defs` is also imported by Magic Square `Rigidity/Reflections.lean`; it was
not changed. No Magic Square consumer was edited. The actual combined-point
declarations `exists_combinedPointsWitness` and `exists_extendedQ` are at
`Combining/Points.lean:67,323`; they use the independent sandwich, rounding,
and field-valued consistency modules. Their unchanged outputs feed subsequent
line, low-degree, extraction, and soundness modules. This change does not
pretend that compilation of those modules proves the padding assumption.

| Integrity item | Result |
| --- | --- |
| Paper hypotheses | Arbitrary finite space, density, natural t, binary family, real delta, C >= 1-delta. |
| New corrected Lean hypotheses | Exactly those hypotheses, finite basis and decidable equality as representation instances. No t>0, delta>=0, commutation, producer, or conclusion-shaped premise. |
| Paper conclusion | Arbitrary finite pure ancillary extension after the family, exactly linear binary observables for every pair, averaged operator error <=delta. |
| Corrected Lean conclusion | Same witness domain, order, exact relations, and average; bound <=2 delta. |
| Verdict | Explicitly weakened numerical conclusion, with optimal universal multiplicative coefficient. Not advertised as a proof of the false printed theorem. |
| Printed Props | Original universal quantification and ancilla domain retained; both distance readings refuted. Neither is asserted or added as a theorem hypothesis. |

## Edge cases and validation

The mathematical proof handles arbitrary mixed states and noncommuting input
families. The new theorem type-checks with no numerical side conditions,
including t=0. Positivity of the defect rules out negative delta; zero defect
gives zero output error. The quadratic counterexamples have delta<1 and
positive t, so these conventional restrictions cannot improve the universal
coefficient. Arbitrary pure ancillary dimensions are quantified in both Lean
refutations; the lower-bound theorem is stronger, allowing every density.

An exact-integer Walsh transform was used to enumerate all scalar sign
families for t=0,1,2,3,4 (2,4,16,256,65536 families). For N=2^t and
unnormalized coefficients w, compute
`C=sum(w_i^3)/N^3` and `Eopt=2-2*max(w_i)/N`.
There were zero violations of Eopt<=2(1-C). The maximal nonzero-deficit ratios
were 2,1,4/3,4/3,16/9, respectively. Independent exact computations for the
quadratic family k=1,...,5 gave 4/3,8/5,16/9,32/17,64/33. These are finite
computational checks; the proof of sharpness is the unbounded family argument
in the note, not an inference from enumeration.

Focused checks already passed: both changed Lean modules, QPBT aggregate,
root aggregate, and the seven named axiom-closure probes (both refutations,
the lower bound, and all four corrected existence forms). The axiom closures
contain only `propext`, `Classical.choice`, and `Quot.sound`. The dependency
artifacts written by these checks are private to this worktree. Full build,
CI, independent review, publication, and adoption belong to main.
The exact final document/hook results are recorded in the session receipt.

## Historical budget reconciliation

The assignment admits one additional 3600-second tranche starting
2026-09-22T11:08:59Z. It does not renew the ordinary limit. The original
normalization work is anchored no later than 2026-09-04T07:06:12Z.
The supplied packet is explicitly a partial ledger. A complete cumulative
count of gap-specific mathfix attempts and total time remains unknown.

The following is an inventory of related measured execution intervals, not
a claim that all their time was exclusively normalization work. Line numbers
refer to the starting commit's two committed telemetry ledgers.

| `sessions.jsonl` group | Intervals | Seconds | Rows |
| --- | ---: | ---: | --- |
| #124 and #129 provers | 2 | 2894 | 243,343 |
| PR136 review | 8 | 5561 | 249,255,269,270,271,290,292,303 |
| PR143 (#125) review | 6 | 4588 | 267,268,272,297,306,312 |
| PR144 (#127) review | 4 | 3061 | 277,278,308,309 |
| PR148 (#128) review | 4 | 2888 | 286,289,307,310 |
| PR151 (#129) review | 8 | 7195 | 314,317,322,326,339,341,351,353 |
| #173 audit/repair | 2 | 2939 | 368,398 |
| PR184 (#173) review | 8 | 9035 | 370,372,386,389,401,404,420,422 |
| Subtotal | 42 | 38161 | |

| `owner-sessions.jsonl` group | Measured intervals after updates | Seconds | Rows retained |
| --- | ---: | ---: | --- |
| #124/#129 | 9 | 6584 | 11,27,34,37,38,44,45,66,84 |
| #125 | 3 | 3378 | 12,30,42; row 8 is superseded by 12 |
| #127 | 2 | 2138 | 14,59 |
| #128 | 2 | 2423 | 21,41 |
| #173 | 3 | 6231 | 94,98,103 |
| Subtotal | 19 | 20754 | |

The #125 same-start update at row 12 (2114 seconds) subsumes row 8
(1422 seconds); they are not added together. The ended-unrecorded aliases
at rows 1,10,15,22,91 remain part of the record. In particular row 22 around
09:30Z is not a second measured session and its unknown tail is not zero.
Row 91 is followed by the completed same-name interval at row 94.
The two #129 intervals at 10:24Z have different roles/models; rows 44 and 45
remain distinct, consistently with the assignment's 6584-second subtotal.

Later common-ancilla, preservation, and review work also remains charged.
PR212/573 entries in `sessions.jsonl` give 19 measured intervals totaling
21647.052 seconds, at rows
1078,1169,1172,1175,1190,1224,1232,1256,1274,1288,1293,1327,1376,1378,
1411,1495,1496,1992,2097. Row 1991 is the active record superseded by 1992;
failed intervals at 1256,1495,1496 remain charged.
The corresponding owner-ledger work gives 13 intervals totaling 21242 seconds,
at rows 118,345,385,399,404,468,482,613,664,683,708,717,740.
Repeated records 508,565,579 duplicate 404,468,482, respectively and are not
summed twice. Row 708 is the later PR629 blueprint-linkage work.

Thus this explicitly identified related history contains 93 measured
intervals totaling 101804.052 seconds before this assignment, plus unknown
time and broader audits not exclusively attributable to this gap. It is not
93 mathfix attempts, not a complete gap-only total, and not an authorization
to continue. Other original scaffolding and cross-cutting audit costs are
preserved rather than declared absent. Main must reconcile the complete
aggregate if a further decision requires it. The #118/B8 exception is unrelated;
the only authority here is the new finite #694 assignment.

## Operator action

The mathematical normalization packet is ready for independent review once
main has run its full CI. Proposed #27 line (not posted by this session):
"#694 retains and refutes both printed linearity claims, proves the corrected
bound on the full numerical domain, and supplies the sharp universal-constant
and complete consumer audit; normalization remains pending review/adoption,
and padding remains open."

Main owns the eventual adoption, event/design-decision entries, publication,
and any complete budget reconciliation. This session neither modifies runtime
state nor posts a message. No owner permission blocker was established.
