# Genuine application foundation

Reference for the standard operation: Richard Laver, *On the algebra of
elementary embeddings of a rank into itself*, pp. 1–3,
https://arxiv.org/pdf/math/9204204. The application graph is the union of
the images of the graph cuts k intersect V_alpha, alpha < lambda.
The results below are proved from the project's actual ZFSet rank domain and
full first-order elementary embeddings, not imported as application axioms.

## Construction and verified proof route

1. `RankRestrictionGraph` constructs the set graph of k restricted to the
   members of any domain set d in V_lambda. Its range is contained in k(d),
   so graph rank closure puts the restriction itself in V_lambda.
2. `RankApplicationRelation` takes the union of j-images of these graphs.
   Restrictions increase under domain inclusion. The union of two domain
   sets gives a common larger restriction, proving global functionality.
3. `RankPowersetPreservation` proves that elementary embeddings preserve
   powersets, using an explicit membership-language formula and absoluteness.
   `RankImageCofinality` proves V_alpha is contained in j(V_alpha) by actual
   well-founded ordinal induction. Hence every x lies in j(d) for some d,
   and one such image set covers any finite parameter tuple.
4. `RankGraphElementarity` encodes, for EACH particular finite formula phi,
   the statement that a graph preserves phi. This is a finite first-order
   formula, not an assumed satisfaction predicate. Each k-restriction
   preserves phi; elementarity of j transfers that statement to its image.
   Together with finite-tuple coverage this proves full elementarity of
   the constructed union map, bundled as `rankApply` in `RankApplication`.
5. `RankApplicationIdentification` defines the actual graph cuts k intersect
   V_alpha and proves cofinal inclusions in both directions between these
   cuts and the domain restrictions. `rankApply_graph_iff` identifies the
   constructed map pointwise with the standard union-of-image-cuts graph.
6. `RankApplicationCritical` transfers the explicit first-order statement
   that a graph fixes ordinals below a bound. It proves
   crit(j applied to k) = j(crit(k)) as a `RankCriticalPoint` theorem.
7. `RankApplicationComposition` transfers graph composition and proves
   j applied to (k composed with l) equals (j applied to k) composed with
   (j applied to l), along with the identity and finite-word versions.
   `RankApplication` also proves (j applied to k) composed with j = j composed
   with k and the corresponding ordinal-image equation.
8. `RankHierarchyGraph`, `RankHierarchyRecursion` and `RankHierarchyImage`
   construct the hierarchy recursion graph on alpha+1, encode its recursion
   as a first-order formula, and prove uniqueness by ordinal induction.
   This establishes the exact identity j(V_alpha) = V_(j(alpha)) and the
   exact set-rank equation rank(j(x)) = j(rank(x)).
9. `RankApplicationAgreement` encodes weak graph membership agreement and
   transfers it through the actual restriction graphs at V_delta. It proves
   application preserves weak agreement at the exact image cutoff.
   `RankApplicationCutoff` gives exact natural-cutoff image and certificate
   transfer for finite words of arbitrary length, including the empty case.
10. `RankApplicationBelowCritical` proves all sets below the critical point
    are fixed, and j applied to k weakly agrees with k below crit(j).
    `RankIntersectionPreservation` and `RankAgreementComposition` prove that
    weak agreement at a LIMIT rank cutoff extends to arbitrary inputs and
    survives postcomposition at the image cutoff. `RankCriticalLimit`
    derives the needed nonzero limit property of critical points from
    zero/successor preservation. `RankApplicationLowTail` combines these
    facts into low-tail replacement and historical certificate transfer.

## Actual short-copy connection

- `CopySemanticValues` defines the copied column and owner assignments and
  proves EVERY successful branch of copyEntry gives the last owner's image.
  The retained boundary column also equals the original column by the p edge.
- `CopySemanticEdges` includes the implicit endpoint in the full-row mapping
  and proves every copied step edge and the transported critical point.
  `CopyDecomposition` recovers the exact interval, length, and origin of every
  copied row. `CopySemanticColumns` and `CopySemanticRows` establish increasing
  cardinal columns, every edge and every critical point for the whole output.
- `CopyWordCertificates`, `CopyHighWord`, `CopyPrefixCertificates` and
  `CopyHighCertificates` prove exact natural weak certificates for retained
  prefix marks and the actual all-high retention branch. The all-high proof
  identifies the full factor word even when its endpoint is below p.
- `CopyLowWord`, `CopyLowWordCertificate` and `CopyLowCertificates` identify
  the actual translated high prefix and unchanged nonempty low factor tail.
  The tail trace supplies its cutoff bound below the last critical point,
  so the embedding-level low-tail theorem gives the complete actual certificate.
- `CopyMiddleWord` identifies the actual high-prefix/marked-bridge/low-tail
  word. `RankNaturalCutoffCardinal` proves the relevant natural cutoffs are
  infinite cardinals and hence limits. `RankMiddleSplice` transfers the weak
  certificate at three explicit bounds. `CopyMiddleNaturalData` supplies the
  two word bounds, and `CopyGuardCutoff` supplies the owner bound from the
  exact one-based guard and copied row geometry. No copied mark certificate
  is used to establish its own geometry or cutoff bound.
- `CopyMiddleCertificates` and `CopyAllCertificates` complete all retention
  cases. `rankRowRealization_shortCopy` in `CopyRankRealization` now constructs
  the WHOLE copied-entry row/mark realization from the parent's realization
  and literal short-copy success; Sat and internal +1 are not copy hypotheses.
- `MStarRankRealization` combines this with the existing full-scan induction.
  `rankMarkedRealization_mStar_total` proves an actual M_star output on the
  same domain for every realized Sat transient parent whose original short
  copy is legal. `mStar_exists_iff_shortCopy` shows scanning imposes no extra
  failure filter. These results include Sat and all row/mark certificates.
  `ScanBoundaryPreservation` and `MStarBoundaryPreservation` now also retain
  the first three column values, exact terminal and final owner, so the
  complete first-triple linedness family is preserved through full M_star.

All construction hypotheses are explicit: Order.IsSuccLimit lambda and the
actual elementary embeddings. Membership cofinality and application closure
are conclusions. None of these results asserts that a nontrivial embedding
exists; that existence still has to be obtained from the required I2 assumption.

## Next obligations for the manuscript

- `RankLinedWitness` now specifies an entire finite witness, with both endpoints,
  every actual same-domain factor, its critical point, and both edges. Actual
  application transports the whole witness. `AuxiliaryRankRealization` constructs
  the appended row and its short copy, preserving all row/mark certificates and
  Sat, and gives exact prefix, terminal and final-owner formulas.
- `ExpansionRankStages` realizes every stage of one fixed complete witness and
  recovers its final endpoint after all k steps. `ExpansionRankEdges` proves the
  required three ordinal image equations from the literal successor/limit row
  classification. `ExpansionRankRealization` combines these into full E semantic
  closure and preserves the whole finite witness family at the original triple.
- `FullRankRealization` packages the complete certificate and proves closure
  for each exact Step and, conditional on the standard-root certificate,
  for every Generated state on the same rank domain. All operations retain
  the first triple and its entire witness family.
- `BoundedApplicationStep` gives strict terminal descent for cut, one actual
  bounded application for M_star and two for E. `RankWellFoundedReduction`
  proves the logical reduction from a genuine root and Steel's bounded
  application theorem to the exact generated expansion relation. It proves
  accessibility for every realized assignment, so it never relies on
  independently choosing roots for finite path segments.
- Still prove the I2 root and all its complete common-endpoint witnesses,
  and the prefix-barrier/short-key comparison bridge, injectivity and final
  well-order theorem. The Steel input is now proved in RankSteelWellFounded;
  generatedStep_wellFounded_of_root has only the full root input remaining.
- `RankCriticalCardinal` now proves critical-point cardinality directly from
  elementarity and the transported function graph. `RankCriticalSequence`
  proves increasing cardinal critical sequences, and `RankFiniteLining`
  constructs actual finite linedness factors and complete witnesses.
  `RootRankRealization` constructs the SAME literal root using h = g composed
  with g. It proves the full root from a concrete finite-endpoint embedding
  family, leaving the I2 existence of that family open. This alternative
  existence witness does not assert the original g_(11) numerical formulas.
- `RankCriticalStrongLimit` constructs the graph of a hypothetical surjection
  from a fixed set to the critical ordinal and rules it out. This gives the
  low-rank size bound and strong-limit property. `RankCofinalFormula` and
  `RankOrdinalCofinalGraph` encode actual ordinal cofinal functions inside
  the same domain. `RankCriticalRegular` transports a hypothetical short
  fundamental sequence to prove regularity. `RankOmegaPreservation` defines
  omega by its least nonzero limit property and proves it fixed, and
  `RankCriticalInaccessible` combines these into genuine critical-point
  inaccessibility. `RankCriticalSequenceInaccessible` constructs embeddings
  whose critical points are each successive critical image, so every image
  is inaccessible and has the small-hierarchy bound needed by Steel.
  Kunen critical-sequence cofinality is now proved by the omega-Jonsson
  argument in `RankKunenCofinality`. `RankSteelBounds` consequently supplies
  inaccessible bounds and smaller ordinals whose images cross them.
  RankSteelHull and RankSteelHullImage construct the ordinal hull and its
  exact image. RankSteelEvaluation constructs the partial evaluation G and
  proves the small-range bound. ZFOrdinalCollection and RankSteelCollapse
  construct the actual order collapse H and low-rank H composed with G.
  RankSteelImageCut transfers these graphs to embed the child hull into a
  proper initial segment of the parent hull. RankSteelStrictDecrease proves
  strict order-type decrease, and RankSteelWellFounded establishes actual
  bounded-application well-foundedness at every bound on the same domain.

The hierarchy-image graph route proposed in the previous continuation is
now proved. All graph, limit and realization hypotheses are explicit in the
Lean declarations; no application or weak-composition axiom was added.
