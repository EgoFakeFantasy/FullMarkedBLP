# Mathematical foundations: all target obligations discharged

The complete expansion and short-key well-order theorem is proved under the
standard rank formulation `RankI2`. Local semantic closure, genuine root
existence, bounded application well-foundedness and the final comparison
proof are all discharged. The final theorem is
`rankI2_full_marked_blp_natural_cutoff_wellorder` in ShortKeyWellOrder.lean.
The full build and compiled-environment audit pass; see STATUS.md.

## Steel: completed original proof and dependencies

The primary source is [Dougherty, Critical points in an algebra of elementary
embeddings, II, Theorem 2.2, printed page 4](https://arxiv.org/pdf/math/9503204).
It treats all nontrivial elementary embeddings of the same limit rank domain.
Its proof uses the ordinal set of values i(f)(s) obtained from functions and
arguments in a fixed inaccessible V_gamma. Application strictly decreases the
order type of this set. The comparison is built from a small enumeration and
its order collapse, transported by the outer elementary embedding.

This argument also uses Kunen's theorem: each nontrivial embedding's critical
sequence is cofinal in lambda. Together with inaccessibility of critical points,
this supplies sufficiently high inaccessible gamma and the smaller ordinal
whose image crosses gamma. The present application equations alone do not
provide either conclusion by themselves. Critical-point inaccessibility is
now proved in RankCriticalInaccessible: cardinality, strong limit, regularity
and strict uncountability are all consequences of actual elementarity.
RankCriticalSequenceInaccessible proves the same for every critical image by
constructing an actual application embedding with that critical point. It also
supplies the hierarchy-size estimate |V_alpha| < critical.card for alpha below
any such critical point. Kunen cofinality is now proved in
RankKunenCofinality, not assumed as a property of RankElementaryEmbedding.

The proof takes the external critical supremum mu, proves it is an initial
ordinal with strong-limit cardinality and cofinality omega, and proves
mu is fixed if it lies inside the domain. RankCriticalPower proves
mu.card ^ aleph0 = 2 ^ mu.card. CardinalFreshChoice constructs distinct
representatives in a cardinal-sized well-order, and CardinalOmegaJonsson
uses them to construct the sequence form of an omega-Jonsson coloring.
RankJonssonConstruction encodes that coloring as an actual set graph;
RankJonssonFormula proves its first-order transfer. RankFunctionPreimage
recovers a function whose image is any countable sequence in the pointwise
image of mu. Applying the transferred coloring would then put the critical
ordinal in the range of j, which RankCriticalNotImage rules out. Thus
rankCriticalSupremum_eq_domain proves the supremum equals lambda.

This is the direct singular-strong-limit route described in
[Caicedo's partition calculus notes, Theorem 8 and Corollary 9](https://caicedoteaching.wordpress.com/2009/04/06/580-partition-calculus-3/),
using sequences instead of countably infinite subsets. The required sequence
coloring property and its cardinal selection construction are proved in Lean.

RankSteelBounds now supplies an actual inaccessible critical image above
each prescribed bound, all smaller hierarchy-size estimates, and an alpha
below gamma with j(alpha) at least gamma whenever crit(j) < gamma.

The remaining construction is now completed. RankSteelHull and
RankSteelHullFormula define the actual set of ordinal function values and
its first-order description; RankSteelHullImage proves the exact image
equation, including parameters in the whole image hierarchy. The partial
evaluation function G in RankSteelEvaluation surjects onto the hull, and
its domain has rank below gamma for alpha below gamma. Hence the hull has
cardinality below gamma. ZFOrdinalCollection gives the actual ordinal order
type and order collapse H, with the order type still in the original universe.
RankSteelCollapse constructs the ordinal-valued graph H composed with G and
proves its rank below gamma. RankSteelEvaluationImage and RankGraphOrder
provide first-order transfer of evaluation, composition and ordering.

RankSteelImageCut proves the image collapse sends the child hull into the
parent hull strictly below j(beta). The latter ordinal is itself in the
parent hull, witnessed by an actual constant graph on the singleton ordinal.
RankSteelStrictDecrease turns this proper-initial-segment embedding into
strict order-type decrease. RankSteelWellFounded chooses one sufficiently
high gamma for each fixed bound and pulls back ordinal well-foundedness.

The proved Lean theorem rankBoundedApplication_wellFounded is:

    forall bound : OrdinalDomain lambda,
      WellFounded (RankBoundedApplication hl bound)

The definition uses the constructed rankApply and an actual critical-point
witness for the left operand, with that critical point below bound. Identity
right factors cause no infinite-chain loophole: their output is the identity,
which has no critical point. No nontriviality assumption on the right factor
was used in the order-type decrease. generatedStep_wellFounded_of_root now
discharges the Steel input in the earlier modular reduction; a genuine full
root certificate is its only remaining mathematical input.

## I2: concrete endpoint embeddings, not an assumed root certificate

[Notes on Laver Tables v5, Propositions 4.8 and 4.9](https://arxiv.org/html/2501.06733v5)
uses second-order elementarity to construct a coherent family of embeddings
whose finite critical-sequence prefixes end at one fixed ordinal.
RankSecondOrder now defines the source's Sigma-two formulation using finite
syntax and full class quantification. RankClassImage identifies the actual
j-plus graph with rankApply. RankCoherentRoots proves the whole endpoint-family
extraction, and RankRootReflection proves the recursive reflection construction
conditional on finite Sigma-one definability of elementary-embedding roots.
RankRootFixedSyntax refines this to allow the actual low-rank syntax tables
as fixed parameters. Formula coding, finite assignment graphs, the actual
satisfaction class and its single finite truth matrix are now proved.
RankElementaryDefinability proves the finite Sigma-one expression of genuine
elementary-embedding graphs, in both directions on all classes.
RankNontrivialFormula and RankClassImageFormula add actual critical-point
existence and the exact class-image equation. RankRootTermMatrix adds every
finite application power and proves rankRootExists_lowRankDefinable.
RankI2Root consequently proves coherent-root existence, the full standard-root
realization and rankI2_generatedStep_wellFounded with no expressibility,
root-realization or Steel premise. Thus the I2 input is now discharged.
I2_FOUNDATION.md gives the precise target and the standard-formulation boundary.
The displayed Proposition 4.9
proof contains an apparent index typo when introducing kappa_1: the preceding
equations assign theta_2 to kappa_omega, so the new earlier cardinal must be
theta_1. Do not formalize the conflicting assignment as a premise.

The concrete sufficient input now used by RootRankRealization is, for every
positive k, an actual j on the same V_lambda such that:

    RankCriticalPoint j critical
    rankOrdinalAction j critical = left
    rankCriticalSequence j critical (k + 1) = right

The three ordinals critical, left and right are common to all k. No single
infinite witness is truncated to fake the fixed final endpoint.

RankFiniteLining constructs a complete k-step witness from each such embedding:
start with j and repeatedly apply j(j) to the preceding factor. These factors
keep the original critical point and advance through the consecutive critical
images. The final point is exactly the specified (k+1)-st image. This supplies
the whole RankAllFiniteLined family.

## A direct realization of the same standard root

The manuscript's root is a fixed five-row literal pattern, and its claimed
conclusion does not include the prototype's exact critical-point estimates.
The current existence proof realizes these same rows with the seven columns
theta_i = g^i(critical), and row owners g, g, h, h, rankApply h h, where h = g.comp g.
All cardinality, increasingness, row edges, critical points, Sat and the only
marked natural-cutoff certificate are kernel checked. The mark's owner and
single word factor are both h.

This is an alternative witness for the unchanged root, not a proof that h is
g_(11). The original g_(11) numerical estimates are neither used nor claimed.
The k=1 member of the endpoint family provides g; its first three columns are
the common critical, left and right, so the complete family augments this finite
realization to a RankFullMarkedRealization.

## Final comparison

I2 root existence and expansion well-foundedness are proved. PrefixChildren
proves literal sibling nesting, and GeneratedReachability uses the proved
well-foundedness to make all generated terms comparable by reachability.
Strict short-key decrease is now proved for the exact cut, E and M_star
operations. In particular native's bottom row preserves the copied key,
and later scan steps preserve that row. ShortKeyWellOrder then proves
comparison/reachability identification, literal key injectivity and the
well-order theorem. No comparison obligation remains in the target theorem.
