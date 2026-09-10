# I2 root construction: completed finite expressibility and expansion theorem

The I2 root, expansion well-foundedness, and final short-key comparison
well-order and injectivity theorems are proved. No root certificate
or linedness family replaces the large-cardinal assumption.

## The formulation and its scope

RankSecondOrder defines finite first-order membership formulas with finitely
many unary class predicates. Its first-order quantifiers range over actual
RankDomain lambda sets. Sigma-one and Sigma-two formulas have arbitrary finite
existential and existential-universal blocks of class variables, ranging over
ALL subsets of RankDomain lambda. Set parameters are mapped by j, and class
parameters by the actual rankClassImage j.

RankI2 uses the nontrivial Sigma-two rank-embedding formulation stated in
[Qi, Notes on Laver Tables v5, Definition 4.7 and Proposition 4.8](https://arxiv.org/html/2501.06733v5#S4).
Its fields are a limit lambda, an actual first-order elementary embedding,
an actual least moved ordinal, and Sigma-two elementarity. There is no field
asserting root extraction, endpoint embeddings, BLP realization, or termination.
RankSigmaTwoElementary implies RankSigmaOneElementary by an empty universal
class block. RankPredicateTranslation proves that every Mathlib first-order
membership formula translates into the matrix syntax with exactly the same
semantics.

The equivalence with the global j:V -> M definition of I2 is not formalized.
The primary reference for the standard rank formulation is
[Dimonte, I0 and rank-into-rank axioms, Definition 6.10 and the discussion following it](https://arxiv.org/pdf/1707.02613).
The arXiv version uses section 6 numbering, whereas Qi's reference uses
different lemma numbering. Do not claim a formal global-class equivalence.

## Actual class image and application

RankClassImage constructs separation inside each actual bounding set and
takes the union of its elementary images. rankClassImage_iff_hierarchy
identifies this with the standard union of j(A intersect V_alpha).
rankClassImage_on_domain proves the exact restriction on EVERY image set,
including its members outside the pointwise image of j.

rankClassImage_embeddingGraph identifies the entire image of the class graph
of k with the class graph of rankApply j k. RankClassImageComposition proves
j-plus after k-plus equals (j applied to k)-plus after j-plus for all classes.
Using injectivity of the graph representation gives rankApply_left_distrib
for actual embeddings. No distributivity axiom was added.

## Coherent roots give the full common-endpoint family

rankCriticalSequenceEmbedding hl j n is the source's j^(n+1). The power
identities, including the root identity, are proved in RankApplicationPowers.
Its ordinal-action theorem fixes every earlier critical image and shifts
every image in the later tail by one place.

RankCoherentRoots records actual embeddings e_n, critical points c_n, and

    e_n = rankApply (rankCriticalSequenceEmbedding e_(n+1) n) e_(n+1).

The following are proved, not stored as structure fields:

- The n-th power of e_n is e_0.
- The n-th critical image of e_n is c_0.
- The transition deletes exactly the indicated critical image, preserving
  the whole earlier prefix and the whole later tail.
- c_(n+1) = c_1, and the first image is common from e_2 onwards.
- For EVERY k > 0, e_(k+1) has critical point c_1, the fixed first image of
  e_2, and (k+1)-st image c_0. Thus its final endpoint is genuinely common.
- These embeddings give every complete finite linedness witness and the
  full realization of the unchanged literal standard root.

This resolves the algebraic and endpoint content of Propositions 4.8-4.9.
RankI2Root now proves the coherent sequence exists from RankI2, using the
finite expressibility construction described below.

## The finite reflection input, now proved

RankRootExists hl n A says that there are an actual elementary embedding x
and an actual critical point such that A is the whole graph of

    rankApply (rankCriticalSequenceEmbedding x n) x.

RankSigmaOneClassLowRankDefinable P means that an ACTUAL FINITE Sigma-one
formula with one free class parameter and finitely many fixed set parameters
of rank at most omega expresses P on all classes. This quantifies over finite
syntax, not over arbitrary predicates declared to be formulas. The proved
rankRootExists_lowRankDefinable theorem, for omega < lambda, is

    forall n, RankSigmaOneClassLowRankDefinable (RankRootExists hl n).

RankRootReflection and RankRootFixedSyntax prove the reflection argument from
this expressibility input: image parameters are identified with rankApply;
the current embedding witnesses the image statement; Sigma-one elementarity
reflects it to a new root. A dependent recursion then constructs the infinite
coherent sequence while preserving its base-power invariant.

The general exists_rankCoherentRoots_of_sigmaTwo_and_lowRank_definability theorem
retains an expressibility argument. RankI2Root supplies it using the actual
finite formula, so exists_rankCoherentRoots_of_sigmaTwo has no expressibility premise.

RankSyntaxData now constructs injective natural formula codes and the six
actual constructor tables. Every table has rank at most omega, so genuine
critical-point fixedness applies; no additional fixed-parameter premise is
required. RankFiniteAssignment constructs actual finite assignment graphs,
their injectivity, decoding and exact extension by one value.
RankSatisfactionClass constructs the actual satisfaction class and proves
agreement with formula semantics and uniqueness on valid inputs for any class
satisfying the five truth clauses. RankTruthFormulaAtoms constructs finite
formulas for graph functions, assignments and truth queries.

RankTupleFormula and RankSyntaxTableDecoding now prove exact finite table
reading, including exclusion of nonnatural coordinates on arbitrary set
inputs. RankAssignmentFormula expresses exact assignment extension and
validity. RankTruthMatrix constructs ONE finite formula with six set
parameters. RankTruthMatrixCorrectness proves its equivalence to the whole
truth recursion, proves the actual satisfaction class satisfies it, and
recovers actual truth from every satisfying class. Thus the finite truth
matrix gap is closed, without declaring an infinitary schema to be a formula.

RankClassFunction constructs and decodes whole-domain function class graphs
and proves a finite formula describes them. RankAssignmentMap proves finite
pointwise assignment transport. RankFormulaRelabel handles set-variable
substitution, and RankPredicatePureFormula translates pure matrix formulas
back to Mathlib membership formulas. RankElementaryMatrix combines these
with the truth matrix: every solution gives a genuine Mathlib elementary
embedding, and every actual elementary embedding satisfies the matrix.
rankElementaryGraph_sigmaOne proves the exact equivalence on ALL class
inputs. RankElementaryDefinability packages this as

    RankSigmaOneClassLowRankDefinable
      (fun A => exists j, rankEmbeddingClassGraph j = A).

The remaining components of root expressibility are now completed:

1. RankNontrivialFormula expresses nontriviality via a moved ordinal and
   recovers its actual least moved ordinal with rankCriticalPoint_exists.
2. RankClassImageFormula constructs the finite class-image formula: restrict an inner class to a set,
   read the outer embedding graph on that restriction, and test membership
   in its image. Its semantics is proved to be exactly rankClassImage.
3. RankRootTermMatrix constructs a finite existential block for successive application powers and the
   final root equation. The powers are encoded by n+1 intermediate class
   graphs: P_0 = X, P_(i+1) = X-plus(P_i), and A = P_n-plus(X).
   Actual application closure and rankClassImage_embeddingGraph then identify
   all these classes with genuine elementary embeddings.

The explicit root matrix has one free class parameter, n+3 existential
class witnesses (the root graph, satisfaction class and P_0 through P_n),
and six actual set parameters of rank at most omega. Both directions of
rankRootExists_sigmaOne are proved on ALL class inputs. No class is accepted
as an embedding merely by naming an arbitrary predicate elementary.

RankI2Root combines this formula with fixed-parameter reflection and the
coherent-root recursion. exists_full_root_of_rankI2 constructs the complete unchanged
standard-root realization, including every common-endpoint finite witness.
rankI2_generatedStep_wellFounded then proves manuscript Theorem 4.1 on the
exact generated domain using actual same-domain Steel well-foundedness.
Its only assumption is RankI2, in the formulation explained above.

## Verification

Full build: 1500 jobs. Compiled-environment audit: 4165 theorem constants,
including generated helpers, using only propext, Classical.choice and
Quot.sound. No source proof holes, unsafe declarations or custom axioms.
The final comparison theorem is
`rankI2_full_marked_blp_natural_cutoff_wellorder` in ShortKeyWellOrder.lean.
PrefixChildren and GeneratedReachability prove literal sibling nesting and
I2 comparability under reachability without assuming key injectivity.
MStarShortKey and its dependencies prove strict short-key decrease along
every actual operation, including all positive E parameters and complete
M_star scans. The comparison/reachability equivalence, literal key injectivity
and `IsWellOrder GeneratedPattern GeneratedKeyLT` then follow.
CheckMainTheorem.lean verifies the expanded final statement and its axiom
dependencies. The complete target is finished in the formulation above.
