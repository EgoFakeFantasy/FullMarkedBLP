# Full marked BLP formalization — current status

Target: I2 implies well-foundedness of the exact ordinary E/M_star domain in
manuscript.md, and well-ordering plus injectivity of its short-key comparison.
**The complete target is proved and the final build and axiom audit pass.**

Final theorem: `rankI2_full_marked_blp_natural_cutoff_wellorder` in
`FullMarkedBLP/ShortKeyWellOrder.lean`. Its only hypothesis is `RankI2`.
It states expansion well-foundedness, short-key well-ordering, key injectivity,
and the exact comparison/reachability equivalence on `GeneratedPattern`.

Reference: ../basic-laver-pattern-reference at commit
3c4c96a4d9039b154995aa44d4895ec66ac5f579. The target is a modified notation;
the repository is a prototype reference, not the source of the missing notes.

## Current verified state (2026-09-10)

Full build: 1500 jobs. Compiled-environment audit: 4165 theorem constants,
including compiler-generated helpers. Only propext, Classical.choice and
Quot.sound occur. No source proof holes, unsafe declarations or custom axioms.
The latest build has no errors or internal PANIC diagnostics.
`CheckMainTheorem.lean` also passes: it checks the final statement against
the literal `Generated` subtype and the expanded two-level list key.
Evidence: build-latest.txt, audit-latest.txt, main-theorem-check.txt.

## Completed proof layers

1. Literal ordinary row syntax, canonical marks, exact traces and short keys;
   cut, the partial short-copy map with the correct PDF guard, fixed-anchor E,
   native, frozen marks and the complete M_star scan. Step/Generated use the
   original computational operations without a semantic acceptance filter.
2. Same-domain local semantic closure: exact natural cutoffs, all row edges,
   proper marks, actual trace-word identification, Sat and complete finite
   common-endpoint linedness families. Every actual generated step lifts on
   the same rank domain; all required operations terminate there.
3. Actual elementary application, class image, critical-point transport,
   critical inaccessibility, Kunen critical-sequence cofinality and Steel
   bounded-application well-foundedness for arbitrary right operands on the
   same rank domain. These are proved from actual definitions, not axioms.
4. I2 root construction: finite truth syntax, real assignment graphs, one
   finite satisfaction matrix, and the exact finite Sigma-one description
   of elementary-embedding graphs. RankNontrivialFormula expresses a genuine
   critical point via a moved ordinal. RankClassImageFormula expresses the
   whole actual j-plus operation through bounded restrictions.
   RankRootTermMatrix expresses all finite powers and the final root equation.
   rankRootExists_lowRankDefinable closes the former reflection input.
   RankI2Root then constructs the actual coherent roots and extracts every
   complete common-endpoint witness and the unchanged standard-root realization.
5. Expansion theorem: rankI2_generatedStep_wellFounded proves manuscript
   Theorem 4.1 on EVERY exact Generated state, under RankI2. No root,
   linedness, expressibility or Steel premise remains in this theorem.
6. Short-key comparison: ShortKeyOrder, CopyShortKey, ExpansionShortKey,
   NativeBottomGeometry, NativeShortKey and MStarShortKey prove strict
   decrease for every actual cut, positive E and complete M_star step.
   ShortKeyWellOrder proves manuscript Theorem 5.1 and the final combined
   theorem, including injectivity of the key on literal marked patterns.

RankI2 is the source's standard Sigma-two rank-embedding formulation. Its
fields contain no BLP conclusion. Equivalence with the global j:V -> M
formulation is not formalized; see I2_FOUNDATION.md for the precise boundary.
The concrete root realizes the original literal rows via owners (g,g,h,h,h(h))
with h = g composed with g. It does not claim the prototype's g_(11) estimates
or Theorem 2.25 numerical linedness conclusions, which the manuscript excludes.

## Completed comparison proof

PrefixChildren proves literal parent cut-prefix preservation, nesting of all
E parameters, exclusion of simultaneous E/M_star branches, and prefix
comparability of EVERY pair of children of a valid Sat parent.
GeneratedReachability proves cut reachability to every prefix of length at
least two, valid/Sat/minimum-size properties throughout the I2 generated
domain, and rankI2_generated_reachable_comparable: every two generated terms
are comparable by the reflexive transitive closure of the exact Step relation.
AccessibleBranchChain supplies the well-founded induction behind this result;
it assumes no key injectivity. This uses the already-proved I2 expansion
well-foundedness, rather than an unproved unconditional prefix-barrier theorem.

CopyShortKey proves every entry of the first copied core is either below the
parent minimum or in the parent's retained high tail. The parent minimum is
omitted, giving a strictly smaller decreasing row key. ExpansionShortKey proves
the first auxiliary row is smaller at the second key entry and uses literal
nesting to cover every positive E parameter.

NativeBottomGeometry proves exact bottom core-length, step and minimum formulas
for both short and medium descent. NativeShortKey combines these with exact
high-entry retention to prove native's bottom row has the input key unchanged.
MStarShortKey skips the Sat prefix with empty records, processes the first copy,
and uses strict cursor advancement to preserve its key through the whole scan.

ShortKeyWellOrder combines strict edge decrease with reachability comparability.
It proves comparison/reachability equivalence before key injectivity, then
obtains the strict key relation as a subrelation of the well-founded transitive
closure of reverse Step. `IsWellOrder` and the literal-pattern injection follow.

## Acceptance

All obligations needed for manuscript Theorems 4.1 and 5.1 are discharged.
No conditional local interface replaces I2, Steel, root existence, finite
expressibility, same-endpoint witnesses, or short-key descent in the final theorem.
The standard rank formulation of I2 and the alternative witness for the same
literal root are documented above and in I2_FOUNDATION.md; no global-class
equivalence or excluded prototype numerical estimate is claimed.

Detailed foundations: APPLICATION_FOUNDATION.md, I2_FOUNDATION.md and
FOUNDATION_REMAINING.md. The historical entries below record earlier states;
their old gap descriptions and counts are superseded by this completed section.

## Continuation update: termination and Sat

Completed ScanTermination.lean: native block and whole-pattern row-count
formulas; mark completion preserves row count; remaining old rows decrease
by exactly one. The unbudgeted finite ScanRun relation is proved equivalent
to fullScan via scanFuel_sound/complete. Thus the scanner budget itself cannot
remove a successful finite execution. General native block legality and
existence of ScanRun on every legally copied generated state are still open.

Completed NativeTermination.lean: ordinary shape implies step < core length;
all required B lookups exist on valid cores; nativeSources_total proves that
the complete source-chain computation succeeds on valid rows. This resolves
the source-loop budget and lookup concern, not the native block closure.

Completed Sat.lean: Sat makes each native operation literally identity;
empty records make frozen mark completion identity; scanning a whole Sat
pattern with empty records returns the same literal pattern. Transporting
this to the retained prefix after copying is still needed.

Completed MarkTrace.lean: computeMarkTrace_sound and computeMarkTrace_complete
connect the executable owner-position trace to MarkTrace (completeness uses
core validity). No trace-check heuristic remains at this interface.

Immediate next work: native block legality and copy-map strictness, including
canonical sorted sets under insertColumn; prefix transport of Sat, then the
local semantic closure reconstruction. Semantic and final theorem status
above remains unchanged.


## Continuation update: actual native top geometry

Columns.lean proves exact membership of insertColumn/canonicalColumns, sortedness,
identity on sorted lists, and idempotence. NativeGeometry.lean proves exact top
core membership, old-entry retention, sorted core/marks, marks in core, and marks
strictly below the top owner (under the stated old mark bounds).

NativeSources.lean proves actual source lists strictly decreasing and duplicate
free. The source bounds and adjacency of p/e imply no actual native source is
already in the owner core. These are general theorems from core validity.

NativeCounting.lean derives the exact top core length m+2t from actual native
source computation, not from an assumed disjointness certificate. It also proves
nativeTop_actual_shape: the actual top row remains ordinary, with step L+t.
All 96 theorems are audited in audit-latest.txt (propext/Classical.choice/Quot.sound
only); full build passes 21 jobs without warnings.

Next: prove the entire downward native block has defined e lookups and preserves
ordinary shape/endpoints/proper mark target positions, including the medium
exception. The top-row results do NOT yet prove whole native block closure.
Copy strictness/prefix Sat transport and all semantic/global obligations remain.


## Continuation update: downward native step

NativeLower.lean adds 11 checked theorems: deletion is a sublist and preserves
strict sorting; a single nativeLower exists for ordinary input; its step and
exact length changes; short-row and medium-exception ordinary-shape transitions;
endpoint preservation under explicit preceding-column/source-gap hypotheses.
Those source-gap hypotheses have NOT yet been discharged for every block layer.

nativeTop_actual_coreValid now proves full CoreValid for the actual native top
at owner r+t, including its maximum/last endpoint, not just length/shape.

Build passes 22 jobs. Audit covers 107 declarations using only standard axioms.
Next is the block induction maintaining all consecutive target columns, deriving
source gaps at each descent, and proper mark target positions. The main semantic
closure, I2/Steel and comparison well-ordering remain unproved.


## Continuation update: whole native block core validity

NativePositions.lean derives source spacing e+(L-1)<=owner from increasing
natural columns. This implies all required consecutive targets survive short
descent; no new source-gap assumption is imposed on the actual operation.

NativeBlock.lean proves complete indexed BlockCoreValid and totality by
induction for short blocks, and separately for the initial medium exception.
NativeBlockActual.lean connects both to actual native sources and parent core
validity, including proof that a step-one row cannot have nonempty native
sources. nativeBlock_actual_total and native_total are now fully proved.

Build passes 25 jobs; all 119 theorem declarations audited in audit-latest.txt.
Next: transfer CoreValid to shifted later rows and whole native output; prove
proper-mark target positions and trace preservation. Then copy strictness,
mark completion packet geometry, and semantic closure. Full marked closure,
I2/Steel and comparison well-ordering remain unproved.


## Continuation update: whole native core closure

Shift.lean proves strictness of shiftAfter and preservation of CoreValid and
ProperMarks when owners and columns are mapped by that same shift.
NativeClosure.lean assembles indexed prefix/block/shifted-tail validity and
proves native_preserves_coreValid for the entire output from parent core
validity. Combined with native_total this closes native totality and ordinary
core preservation, without semantic or extra filtering assumptions.

Build passes 27 jobs without warnings; 129 declarations audited (standard
axioms only). Still open: new native block proper marks and accurate traces;
mark-completion packet legality; copy strictness and closure; E closure;
then semantic/I2/Steel and comparison bridge.

Useful next observation for proper marks: for a short row of length 2L-1,
its e index is L-1 (zero-based), strictly before every proper mark position
k>=L. Normal descent removes that e entry and the last owner, so retained
marks move down one position while step decreases by one. Medium exception
removes only the last owner and preserves step/positions. This observation
has not yet been formalized. Native top position proof needs source insertion
between adjacent p/e, not just membership/sortedness/counting.


## Continuation update: descending proper marks

NativeMarks.lean proves nativeLower_medium_proper and nativeLower_short_proper
from their explicit parent CoreValid/ProperMarks and (for short) length equality.
In the short case, e precedes every marked target; deleting the owner preserves
its index and deleting e shifts it by at most one. Sorted marks and owner bounds
are preserved as well.

The same module proves sorted_rank_at_index and target_position_iff_rank:
step-target position can equivalently be expressed by counting core entries
below the marked value. This will support native top insertion, whose proper
marks remain unproved. Next prove that the t new sources lie below every old
proper mark, and use disjoint counting to obtain the needed rank increase;
then propagate proper marks down the block using the new descent lemmas.

Build passes 28 jobs without warnings; 136 declarations audited. Main objective
is still incomplete; no semantic closure or I2/Steel/well-ordering theorem exists.


## Continuation update: native top proper marks completed

NativeTopMarks.lean proves sources precede every old mark on eligible rows,
and uses duplicate-free subset counting to bound the rank of each retained
mark after inserting t sources. A separate new-mark position proof uses the
old owner's rank and the same disjoint source count.

nativeTop_actual_properMarks now establishes all ProperMarks conditions for
the actual top from parent CoreValid and ProperMarks. This includes strict
mark sorting, owner bounds, membership, and step-target indices, not just
mark membership. No new algorithmic guard was introduced.

Build passes 29 jobs. All 143 theorem declarations audited with standard
axioms only. Next propagate proper marks through the already-defined short/
medium block recursion, then assemble whole native proper-mark preservation.
Accurate trace preservation and all semantic/global well-ordering work remain.


## Continuation update: whole native proper-mark closure

NativeBlockMarks.lean propagates ProperMarks down short blocks and the medium
exception. NativeMarksActual.lean connects these recursions to actual native
sources and the verified native top. NativeProperClosure.lean assembles the
retained prefix, new block, and shifted tail.

native_preserves_properMarks proves the entire native output has proper marks
from parent CoreValid and ProperMarks, with no additional operation filter.
Together with native_total and native_preserves_coreValid, native is total and
preserves ordinary literal row syntax and proper marks. This does NOT establish
accurate traces or semantic edges.

Build passes 32 jobs; 152 declarations audited, standard axioms only. Next:
accurate trace preservation for native (old p-chain/owners and new direct marks),
then copy strictness/trace branches and mark-completion packet geometry. All
semantic, I2/Steel, comparison and final well-ordering goals remain incomplete.


## Continuation update: trace transport and native prefix

TraceTransport.lean proves trace_map under strict order and actual predecessor
edge transport; trace_prefix from old core validity and unchanged row lookup.
It then proves native_prefix_rowAt, native_prefix_trace, and
native_prefix_markTrace for all owners strictly before the native owner.
fromRight_map and shifted_row_p/e identify the shifted-row predecessor values.

Build passes 33 jobs without warnings; 161 declarations audited. This does not
yet prove traces through the native block. Next establish the exact p values
of block rows (old bottom p retained; new direct mark chains), then use
trace_map for later shifted owners. A shift theorem alone is insufficient:
it does not supply the p values of the modified bottom row.

All copy/compTo and semantic/global goals remain incomplete.


## Continuation update: native block predecessor index formula

NativePredecessor.lean proves low-index entry preservation under descent and
nativeLower_p (the new p reads the old core at step+2 from the right).
The short and medium block recursions now have checked indexed p formulas:
if top.length=startIndex+k+top.step+1, block row j has p equal to
 top.core[startIndex+j]?. Both proofs derive the recursion invariants.

Build passes 34 jobs without warnings; 166 declarations audited. To finish
native trace transport, still identify these consecutive top entries with the
old p and reversed native sources. The formula is currently a top-index formula,
not yet a proof of the direct-mark source identity. Need exact ranks (not only
lower bounds) under canonical disjoint insertion to read those entries.
All semantic and global well-ordering goals remain incomplete.


## Continuation update: exact native ranks and old p entry

NativeRank.lean proves canonical_filter_length for duplicate-free inputs and
nativeTop_inputs_nodup for actual native insertion. nativeTop_rank_exact gives
the exact rank below any y<=owner as old-core rank plus source rank (new targets
are all above owner). nativeSources_above_p and nativeTop_old_p_entry show the
old p remains at its old index m-(L+1) in the top core.

Build passes 35 jobs without warnings; 172 theorem declarations audited.
Next instantiate nativeBlockDown_short_p/medium_p with startIndex=m-(L+1),
using top length m+2t and step L+t, and then nativeTop_old_p_entry proves the
bottom p is unchanged. Source entries between p/e still need exact rank
identification to prove all newly created direct traces. Neither that bridge
nor native trace preservation as a whole is yet complete.
Main semantic/global objectives remain unproved.

## Actual native predecessor and trace connection

NativePActual instantiates the block predecessor index formula for actual
native sources, and proves the bottom row retains the old p value, including
the empty-source case. NativeTraceActual proves the actual output retains the
predecessor at the native owner. Every old trace starting at or below that
owner therefore remains a literal trace in the output.

The next trace obligations include transport above the owner through shifted
indices, and identifying the new marked trace chains. These results do not yet
establish semantic realizability, natural cutoff descent, or the final
well-order theorem. All 176 theorem declarations passed the axiom audit.

## Native shift transport

NativeTraceShift proves the exact row lookup after the insertion point,
predecessor transport under shiftAfter, transport of every old Trace, and
transport of MarkTrace on every later old row. Earlier rows are covered by
native_prefix_markTrace. Build: 38 jobs; 180 declarations audited without
sorryAx or additional axioms.

Remaining native trace work concerns marks in the replacement block itself:
old mark source positions and the newly introduced marked chains. Global
copy/completion closure and the semantic well-order argument remain open.

## Inserted-source predecessor identification

NativeSourceRank proves insertion rank between adjacent core entries, bounds
all native sources strictly between old p and e, and identifies each source's
exact top-core index. nativeBlock_source_p then identifies that source as the
p-value of block row (number of smaller sources + 1). This connects the actual
native block formula to the inserted sources without assuming trace closure.

Build: 39 jobs. All 184 declarations passed the axiom audit. Replacement-block
mark source positions and full new marked chains remain to be proved, followed
by copy/completion closure and the still-unimplemented semantic proof.

## Native source traces in the actual output

NativeSourceTrace connects block lookup to the full output and proves
native_source_predecessor and native_source_trace: the row numbered
r + (number of sources smaller than x) + 1 has predecessor x and literal
trace [that row, x]. These statements concern actual successful native outputs
and need only original core validity, not an assumed trace invariant.

Build: 40 jobs. Audit: 187 declarations, no sorryAx or extra axioms. The next
obligation is matching marks' step-offset source positions to these traces;
this does not yet prove MarkTrace closure for the replacement block. The final
semantic and well-order proof remains open.

## First complete new top-row MarkTrace

NativeOwnerMark proves the exact step-source for target r in nativeTop,
its mark membership for nonempty sources, the actual top row lookup, and
native_top_owner_markTrace: MarkTrace b (r + sources.length) r [r,p].
This is a complete marked trace with literal target/source positions and
actual output lookup, not merely an unmarked chain.

Build: 41 jobs. Audit: 192 declarations, only standard Lean axioms. Other new
top targets, old marks in the top, and downward marked-trace preservation
remain open. No final semantic or well-order theorem has been established.

## All new top-row marks have traces

NativeTargetIndex proves exact consecutive target indices, relates their
step-source indices to actual output predecessors, and proves
native_top_new_marks_have_trace for every j < sources.length. The result
provides an actual p and MarkTrace b (r+t) (r+j) [r+j,p], deriving predecessor
existence from preserved core validity. No predecessor-existence assumption
remains in this final local theorem.

Build: 42 jobs. Audit: 198 declarations without sorryAx or additional axioms.
Old top-row marks and downward trace preservation remain open, as do global
copy/completion closure and the semantic well-order proof.

## Full native top-row trace preservation

NativeOldMark proves low source indices stay fixed, old mark target indices
increase by sources.length, and their step-offset sources stay fixed. It
transports each original MarkTrace to the actual top row. The combined theorem
native_top_all_marks_have_trace covers every top-row mark, assuming original
core validity, proper marks on the operated row, and traces for its old marks.

Build: 43 jobs. Audit: 204 declarations, only standard Lean axioms. Next:
downward marked-trace preservation through nativeLower and the entire block.
Global copy/completion closure and semantic well-ordering remain unfinished.

## Downward step-pair preservation

NativeLowerTrace proves exact index movement when deleting a smaller entry,
nativeLower_medium_pair and nativeLower_short_pair. Medium descent retains
both target and source indices; short descent moves the target left by one
and decreases the step by one, leaving the source entry unchanged. Both
results apply to actual nativeLower outputs and preserve literal sources.

Build: 44 jobs. Audit: 207 declarations, standard axioms only. These local
pair lemmas still need assembly into row-trace and whole-block preservation.
Global operation closure and the semantic well-order proof remain open.

## Row and recursive block trace preservation

RowTraces defines HasTraces for a literal row in a fixed ambient pattern and
proves its equivalence to the existing MarkTrace formulation when row lookup
is supplied. Both nativeLower cases preserve this predicate, using the exact
step-pair lemmas. NativeBlockTraces proves short and medium block recursion
preserves traces under the explicit core, proper-mark, shape, step and
consecutive-target hypotheses. These conditions are not encoded as axioms.

Build: 46 jobs. Audit: 213 declarations, standard Lean axioms only. Next:
instantiate the recursive block result with actual native top traces, then
combine prefix/block/suffix into whole-native marked-trace preservation.
Copy/completion closure and final semantic well-ordering remain open.

## Whole-native marked-trace closure

NativeTracesActual discharges recursive shape/step/target conditions for actual
native blocks, including the empty-source identity case. NativeTraceClosure
combines prefix, replacement and suffix into native_preserves_traces:
original core validity, proper marks and HasTraces on every input row imply
HasTraces on every output row of a successful native operation.

Build: 48 jobs. Audit: 216 declarations, standard Lean axioms only. Native
now has totality, core closure, proper-mark closure and marked-trace closure.
Next major obligations are completion and short-copy closure, then full-scan
and E/M-star domain invariants. Natural-cutoff semantics, I2 realization,
Steel descent and the final well-order/injectivity theorem remain unproved.

## Completion geometry foundations

CompletionGeometry proves exact core growth by 2q, ordinary-shape preservation
with step growth q, and core validity under explicit disjointness, source
bounds, target-gap and owner-bound hypotheses. These are local geometric
lemmas. The actual completionRecord guard is NOT yet proved to imply these
hypotheses; the manuscript invokes the full parallel packet and interval
argument for that implication, which remains an essential obligation.

Build: 49 jobs. Audit: 219 declarations without sorryAx or additional axioms.
Completion mark/trace geometry, actual guard sufficiency, short-copy closure,
and the final semantic well-order proof remain open.

## Completion rank and p preservation

CompletionGeometry now exposes the disjoint-input Nodup lemma used in exact
counting. CompletionRank proves the rank contribution of old columns, inserted
sources and inserted targets, derives the exact shift of an intervening old
entry, and proves completeMarkRow_p under explicit source-below-p and
p-below-target-gap conditions. These establish the algebraic part of the
old-predecessor preservation argument.

Build: 50 jobs. Audit: 223 declarations, standard Lean axioms only. Actual
scan/record geometry must still imply these conditions; it is not assumed
proved. Completion marked traces and short-copy closure, natural-cutoff
semantics and final well-ordering remain open.

## Completion preserves unmarked chains exactly

CompletionTrace proves row-replacement lookup and predecessor equality, then
trace equivalence in both directions for patterns with equal predecessor
functions. completion_trace_iff applies this to actual set-based row
completion under the explicit source/target gap hypotheses. Every untouched
row also has equivalent MarkTrace witnesses via markTrace_set_other_iff.

Build: 51 jobs. Audit: 230 declarations, standard Lean axioms only. The edited
row still needs proper-mark and step-source correspondence for all its marks.
Actual guard sufficiency and the full parallel packet remain unproved, as do
short-copy closure and the final semantic well-order argument.

## Completion proper marks

CompletionMarks proves a rank lower bound from the distinct inserted sources,
a target-position lemma, and completeMarkRow_properMarks. The latter covers
all retained and new marks under input core/proper validity, the completed
target being marked, distinct sources outside the core, sources before all
old marked targets, and the strict new-target owner bound.

Build: 52 jobs. Audit: 233 declarations, standard Lean axioms only. This is a
conditional local geometry theorem, not proof that completionRecord satisfies
its hypotheses. Step-source trace correspondence in the edited row and the
actual parallel-packet/guard argument remain open, along with short copy and
final semantic well-ordering.

## Current completion mark trace and new target indices

CompletionTargetTrace proves preservation of entries below the inserted
sources and exact consecutive target indices. completion_current_markTrace
retains the current old target's source and literal trace in the set-based
output when the new sources lie strictly between that source and target,
and the explicit disjointness/target-gap conditions hold. The trace transport
uses unchanged earlier rows, without assuming global p preservation.

Build: 53 jobs. Audit: 236 declarations, standard Lean axioms only. New target
source chains and other old marked pairs still need the parallel packet and
interval argument. Actual guard sufficiency, copy closure and the final
semantic well-order proof remain open.

## Completion new-source pairs and packet-to-mark connection

CompletionSourcePair identifies each inserted source by its rank in the old
source gap, proves the exact step-pair for its new target, and converts a
supplied actual parallel packet Trace into a new MarkTrace in the completed
pattern. The target is y + (number of inserted sources below x) + 1.
The result includes literal row lookup, mark membership and both core indices.

Build: 54 jobs. Audit: 239 declarations, standard Lean axioms only. The actual
parallel packet Trace and geometric gaps remain hypotheses to derive from
scan/realization invariants. Other old marked pairs, copy closure and the
final semantic well-order proof remain open.

## Later old completion marks

CompletionLaterMark proves the exact 2q index shift above both insertion
regions, the old step-pair correspondence when its source moves by q and its
target by 2q, and completion_later_markTrace preserving the literal chain.
The hypotheses explicitly put the source between the insertion regions and
the target above the full new target interval.

Build: 55 jobs. Audit: 242 declarations, standard Lean axioms only. Earlier
old marks and assembly of completion-row traces remain, as does proof that
actual scan events satisfy the interval/packet hypotheses. Short-copy closure
and final semantic well-ordering remain unproved.

## Earlier old completion marks and interval cases

CompletionEarlierMark proves the q target-index shift with unchanged source
index for earlier marked pairs, transports their exact MarkTrace, and combines
earlier/later cases in completion_old_markTrace. Its interval disjunction is
explicit; this is not yet derived from actual scan events.

Build: 56 jobs. Audit: 245 declarations, standard Lean axioms only. Both old
mark cases and the packet-to-new-mark conversion are now available for row
closure assembly. Actual interval/packet sufficiency, short-copy closure and
the final semantic well-order argument remain unproved.

## Conditional completion-row trace closure assembled

CompletionRowClosure proves source-rank coverage (every target rank has a
source), then completion_row_hasTraces for the entire completed row. It covers
all old and new marks under explicitly stated source-gap geometry, old-pair
interval cases and actual parallel packet traces. No guard sufficiency or
semantic realization is smuggled into the conclusion.

Build: 57 jobs. Audit: 247 declarations, standard Lean axioms only. Next is
whole-pattern completion closure and, essentially, deriving these interval
and packet hypotheses from actual scan/copy/realization invariants. The final
natural-cutoff semantics and well-order/injectivity theorem remain unproved.

## Conditional whole-pattern completion trace closure

CompletionPatternClosure adds generic single-row property replacement and
trace replacement with unchanged p. completion_pattern_hasTraces combines
actual set-based completion, p preservation and the completed row result to
cover all output rows. Source/target gaps, old-pair interval cases and actual
parallel packet traces remain explicit assumptions requiring proof from the
real scan domain. The theorem does not assert completionRecord sufficiency.

Build: 58 jobs. Audit: 250 declarations, standard Lean axioms only. Next work
must address actual guard/record invariants and copy/scan closure rather than
mistaking this conditional whole-pattern theorem for final completion. The
natural-cutoff/I2/Steel and final well-order/injectivity proofs remain open.

## Actual completion guard characterization

CompletionGuard proves recordAt returns a member of the historical record
list, characterizes currentPlusOne by each actual internal adjacent pair,
and gives a two-way characterization of completionRecord success. For a mark
still present in its row, completionRecord_sound yields the real MarkTrace,
terminal-factor lookup, nonempty historical record and internal +1 witnesses.
The current-mark membership premise is explicit because computeMarkTrace
itself reads core positions and does not check the mark list.

Build: 59 jobs. Audit: 254 declarations, standard Lean axioms only. Frozen-mark
membership persistence, historical record geometry and the full parallel
packet from Sat_rec/guard remain obligations; no guard-to-packet implication
has yet been proved. Final semantic well-ordering remains open.

## Actual scan record chronology

ScanRecords introduces ScanReach using exactly the implemented scan transition,
proves positive earlier record keys, nonempty stored sources, strict reverse
key order and preservation of old lookups when pushing a new record. Successful
scanFuel/fullScan executions reach a terminal ScanReach state; hence this
relation is connected to the actual algorithm, not a filtered generation domain.

Build: 60 jobs. Audit: 260 declarations, standard Lean axioms only. Record
chronology is proved without core/semantic assumptions. Source geometry,
frozen-mark persistence, Sat_rec/parallel packets and the final semantic
well-order proof remain open.

## Historical native origins of records

ScanRecordOrigin proves every stored pair comes from a specific earlier
ScanReach state and a successful actual native event. From explicit core
validity at historical post-completion events it derives decreasing source
order, source distinctness for completionRecord and source bounds below the
record key. Historical validity is not inferred from the currently modified
rows; it remains an explicit scan-induction obligation.

Build: 61 jobs. Audit: 265 declarations, standard Lean axioms only. Still open:
actual scan core/mark/trace closure, frozen-mark persistence, record geometry
sufficient for parallel packets, copy closure and final semantic well-ordering.

## Historical record equations in the current scan state

ScanPrefix proves completion changes no other row, a full scan step preserves
its earlier prefix, and every stored native block ends before the scan cursor.
It then transports each recorded native source-predecessor equation through
all later scan steps. scanReach_record_trace supplies the corresponding
current two-node Trace. Historical post-completion core validity remains the
explicit assumption; no current geometry was assumed in place of history.

Build: 62 jobs. Audit: 272 declarations, standard Lean axioms only. This is the
base direct packet at the recorded terminal; propagation through longer
+1-guarded words, actual scan legality, copy closure and the final semantic
well-order proof remain open.

## Actual direct-word packet

DirectPacket characterizes completionRecord on a computed two-node word and
proves completion_direct_packet from actual ScanReach history: all new direct
chains, source distinctness and the strict target-before-cursor bound. It
also proves stored sources remain above the current predecessor of their
record key, transporting the native owner's p through later prefix-preserving
steps. Historical post-completion core validity is still explicit.

Build: 63 jobs. Audit: 275 declarations, standard Lean axioms only. The direct
packet is now derived rather than assumed. Adjacent source-gap disjointness
for the current owner, longer-word propagation, actual scan legality, copy
closure and final semantic well-ordering remain open.

## Direct source bounds and later frozen marks

DirectPacketBounds extracts the predecessor equation from the actual computed
two-node marked trace and derives s < x < y for every source of a successful
direct completion. The extra known-predecessor premise is discharged. It also
proves such a completion retains every mark z >= y, a first concrete step
toward frozen-mark membership persistence. Historical event core validity
remains explicit, and the result is currently for direct words.

Build: 64 jobs. Audit: 280 declarations, standard Lean axioms only. Longer-word
packet propagation and frozen fold invariants, adjacent source/target gaps,
scan/copy legality and final semantic well-ordering remain open.

## Source bounds for arbitrary completion words

CompletionSourceBounds proves the penultimate factor points to the exact
trace endpoint and is at most the initial target. Combined with the current
historical record equations, completion_sources_between derives s < x < y
for every returned source, with no direct-word restriction. It also proves
completeMark retains all marks z >= y, including the no-completion case.
Current core validity, historical post-completion core validity and current
mark membership remain explicit premises.

Build: 65 jobs. Audit: 284 declarations, standard Lean axioms only. These are
coarse bounds, not the adjacent source-gap or parallel target packet theorem.
Frozen-fold legality, longer packet propagation, actual scan/copy closure and
final semantic well-ordering remain open.

## Source bounds inside the frozen fold

FrozenSourceBounds generalizes record source bounds to any current pattern
with the same earlier-row prefix as a ScanReach entry state. It instantiates
this with the actual fold over any processed mark list, using the proved
completeMarks_fold_other_row equality. Thus within-row intermediate states
need not incorrectly be assumed to satisfy ScanReach themselves. Current
core validity and mark membership remain explicit obligations.

Build: 66 jobs. Audit: 286 declarations, standard Lean axioms only. Next:
sorted frozen-list membership persistence and validity induction, exact
interval/packet geometry, copy closure and final semantic well-ordering.

## Frozen pending-mark induction

FrozenMarks extends later-mark preservation to intermediate prefix-equivalent
patterns and proves frozen_pending_marks by induction over processed prefixes
of the sorted original mark list. Every pending mark still occurs in the
actual current row. The theorem requires core validity at those fold-prefix
states and historical post-completion core validity; these are explicit
simultaneous-induction obligations, not assumed completed scan legality.

Build: 67 jobs. Audit: 289 declarations, standard Lean axioms only. Next major
work remains the exact interval/parallel-packet argument needed to discharge
prefix core validity, plus copy closure and final semantic well-ordering.

## Longer-word guard decomposition and chain construction

PacketChains splits currentPlusOne on words with at least two factors into
the first +1 check and the tail guard, and proves guard inheritance by tails.
trace_of_chain constructs the full actual trace from all adjacent predecessor
equations and its final source, deriving required inequalities from core
validity. This isolates the still-missing local packet propagation equations.

Build: 68 jobs. Audit: 293 declarations, standard Lean axioms only. A +1 core
membership check alone has NOT been shown to imply shifted predecessor
relations. Sat_rec/interval and semantic reasoning needed for that step,
actual scan/copy closure and final well-ordering remain open.

## Short-copy map case analysis

CopyMapCases exposes the actual defined-domain cases of copyEntry, including
all endpoint/p guards and the exact indexed step-pair in its middle branch.
copyEntry_not_below_input follows from ordinary core validity. This starts
the independent copy-closure obligation while the longer packet propagation
still lacks its local mathematical argument. Full strict monotonicity is not
yet claimed; cross-branch and same-middle comparisons remain.

Build: 69 jobs. Audit: 296 declarations, standard Lean axioms only. Copy
closure, actual scan/packet legality, natural-cutoff/I2/Steel semantics and
final well-order/injectivity remain unfinished.

## Strict short-copy map on its defined domain

CopyStrict proves middle-branch images lie below the old owner, then
copyEntry_strict across all branch combinations. It derives injectivity and
copyEntry_order_iff for successful input/output pairs under last-row core
validity. No totality on arbitrary columns is assumed. These results support
literal copied-core ordering and exact position/trace transport next.

Build: 70 jobs. Audit: 301 declarations, standard Lean axioms only. Copied row
and mark/trace closure, scan/parallel-packet legality and the final
natural-cutoff/I2/Steel well-order proof remain open.

## Copied core length, sorting and ordinary shape

CopyCore introduces a proved entry-by-entry relation for successful Option
mapM (Std has no imported Forall2 helper here), proves mapped length and strict
sorting, then copiedCore_length/copiedCore_sorted and copiedRow_shape for the
actual copying code. Full rows include the implicit endpoint before dropping
it, as required by the prototype convention.

Build: 71 jobs. Audit: 309 declarations, standard Lean axioms only. Copied owner
identification, proper marks and trace transport remain; this is not yet full
copy closure. Actual scan/packet legality and final semantic well-ordering
also remain unproved.

## Copied owner and row core validity

CopyOwner transports the entry relation through dropLast and the last entry,
proves copiedCore maps exactly the original core, and identifies its last
column as the copyEntry image of the original owner. copiedRow_coreValid now
gives full row core validity at that image owner, not just sorting/shape.
The image owner still needs alignment with the actual shortCopy output index.

Build: 72 jobs. Audit: 314 declarations, standard Lean axioms only. Whole-copy
indexing, proper marks and traces, actual scan/packet legality and the final
natural-cutoff well-order proof remain unfinished.

## Whole short-copy core closure

CopyIndex proves the high-branch owner formula, exact short-copy source list,
indexed map correspondence and copied_block_coreValid at actual output row
numbers. shortCopy_preserves_coreValid combines the unchanged old prefix with
the copied block: every successful shortCopy preserves all ordinary core
validity assumptions. No semantic admissibility filter was added.

Build: 73 jobs. Audit: 321 declarations, standard Lean axioms only. Proper-mark
and trace closure for copy, actual scan/packet legality and the final
natural-cutoff/I2/Steel well-order proof remain unfinished.

## Copied mark origins and target positions

CopyMarks proves copiedRow_mark_origin from the actual zipIdx/filterMap:
each retained mark has an old marked preimage, the same core index, an actual
copyEntry equation and the successful copyMarkAllowed guard. With old proper
marks, copiedRow_mark_position proves the retained target is before the image
owner and occupies an index at least the copied step. Sortedness of the
filtered mark list is still needed for full ProperMarks closure.

Build: 74 jobs. Audit: 323 declarations, standard Lean axioms only. Copy mark
ordering and trace branches, actual scan/packet legality and final semantic
well-ordering remain open.


## Copy proper-mark closure

CopyProper proves that actual copiedRow filterMap marks are strictly increasing,
using their inherited positions in the strictly increasing copied core. Together
with CopyMarks, this proves ProperMarks at the mapped owner.
CopyProperClosure identifies the mapped owner with the actual output index and
proves shortCopy_preserves_properMarks from input core validity and ProperMarks.
Full build succeeds (76 jobs); all 328 theorem declarations pass the axiom audit.
The copy trace-retention branches remain to be proved, as do the completion
packet obligations and the semantic/I2/Steel/well-order target.


## Copy prefix traces and retention guard

CopyPrefixTrace proves that a successful shortCopy preserves row lookup strictly
below the old last owner, and transports all traces and marked traces within
that prefix under the existing core/mark validity hypotheses.
CopyGuard extracts the three exact successful copyMarkAllowed branches,
including computed trace and penultimate witness, first below-p entry, and the
middle branch's marked shifted entry and target position guard.
Full build succeeds (78 jobs); 332 theorem declarations audited without sorryAx.
This does not yet transport traces in newly copied rows across the threshold.


## Copy predecessor transport and high traces

CopyPredecessor proves forward indexed and fromRight transport for MapsEntries,
then copiedRow_p. shortCopy_copied_rowAt identifies the actual copied output row
for every source in [p,e); shortCopy_predecessor proves its actual predecessor
is the image of the old predecessor.
CopyHighTrace proves translation of a full actual trace when its endpoint is
at least p and its head below e, under input core validity and successful copy.
This is a high-region trace lemma, not the whole high-penultimate retention
branch: a final edge to an endpoint below p and the low/middle branches remain.
Full build succeeds (80 jobs); all 338 theorem declarations audited without sorryAx.
The overall semantic and well-order theorem remains unproved.


## High terminal-factor branch

CopyTerminalTrace now transports a trace when only the penultimate factor is
at least p; the endpoint can lie below p. It uses actual shortCopy predecessor
equations, strictness of copyEntry, and a separate final-edge case.
copiedRow_high_mark_trace connects this transport to the actual copied row's
step-source index and the computed original marked trace. It yields the trace
needed for HasTraces in the high-penultimate branch, under explicit source-range
and validity hypotheses. The low/middle branches remain open.
Full build succeeds (81 jobs); all 340 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Low copy branch and middle-branch splice infrastructure

CopyLowTrace proves identity of defined low copy entries and transports the
whole trace when its first below-p entry is below the minimum. The corresponding
copiedRow_low_mark_trace proves the actual copied step-source trace obligation.
CopyTraceSplice proves joining actual traces and replacing the tail after the
first below-p entry by a supplied actual bridge in the copied pattern. The latter
still has an explicit bridge hypothesis; the middle guard must supply that bridge
using the old last-row marked trace and its position guard.
Full build succeeds (83 jobs); 345 theorem declarations audited without sorryAx.
The overall goal and the middle copy branch remain open.


## Middle bridge and trace transport

CopyMiddleBridge proves that the copy position guard forces its preceding
source entry strictly below the minimum; extracts a trace tail at a member;
recovers a marked trace from an exact indexed step pair; and constructs an
actual bridge in the unchanged prefix from the last-row marked trace and the
original low tail. copyEntry_middle_pair identifies the bridge head as the
copy image. shortCopy_middle_trace then performs actual transport, with explicit
source-image-below-minimum and low<=e hypotheses. These must still be discharged
at the selected-mark call site before combining the three guard branches.
Full build succeeds (84 jobs); 351 theorem declarations audited without sorryAx.
The overall formalization target remains unproved.


## Complete short-copy trace closure

CopyRowTraces discharges the middle branch's source-image bound from the actual
position guard and its low<=e bound from trace membership. copiedRow_hasTraces
combines the three actual copyMarkAllowed branches, with no bridge hypothesis.
CopyTraceClosure proves shortCopy_preserves_traces: given input CoreValid,
ProperMarks, and HasTraces at every row, every row in a successful shortCopy has
HasTraces in the output. Prefix rows use unchanged-prefix transport; copied rows
are recovered from the actual source mapM, with their range checked.
Together with CopyIndex and CopyProperClosure, successful shortCopy now preserves
all three structural invariants. This does not establish totality of copy on
the intended generated domain or complete the completion/Sat/semantic proofs.
Full build succeeds (86 jobs); all 355 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Direct packets throughout the frozen fold

FrozenDirectPacket generalizes the recorded direct-word packet to any pattern
agreeing with the scan state below the current owner. It proves source Nodup,
target block below the cursor, and the actual two-point traces by transporting
record predecessor equations. frozen_completion_direct_packet instantiates this
for every processed-list prefix of the actual completeMark fold. No validity
of the intermediate row is needed for this transport; historyValid remains an
explicit hypothesis. Long-word packet propagation and completion geometry remain
open, as does the overall semantic/well-order target.
Full build succeeds (87 jobs); 357 theorem declarations audited without sorryAx.


## Sat inherited-prefix inactivity

CopySatPrefix proves that after shortCopy of a CoreValid Sat parent, native
at every inherited row below the old last owner is the identity. Its e lookup
stays in the same preserved prefix, so the parent's Sat witness applies.
shortCopy_sat_prefix_scan constructs the actual unchanged ScanReach state with
empty records at every cursor through the old last owner.
shortCopy_sat_scanFuel_skip additionally proves the executable scan equality
that skips these idle prefix steps. This supplies the manuscript's initial
old-prefix inactivity argument; it does not yet establish the Sat_rec or
long-word parallel-packet propagation claims.
Full build succeeds (88 jobs); all 360 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Record and factor region in arbitrary scan histories

CopyRecordRegion proves a joint invariant of every ScanReach from a short copy
of a CoreValid Sat parent: at cursors up to the old last owner the state is the
initial copy and records are empty; all record keys are at least that old owner.
A successful completion therefore reads a terminal factor between the old owner
and the current cursor. trace_factor_ge_terminal propagates that lower bound to
all non-endpoint factors, yielding shortCopy_completion_factor_region under
current core validity. This proves an index-region condition, not that each row
is still literally an original copied row or that Sat_rec has been transported.
Full build succeeds (89 jobs); 364 theorem declarations audited without sorryAx.
Long parallel packets, completion geometry, and the final target remain open.


## Copied endpoint Sat witnesses

CopySatWitness proves copiedRow_e and copiedRow_b via exact fromRight transport,
and non-strict order preservation of defined copyEntry values. It then proves
shortCopy_sat_copied_endpoint: a parent Sat witness transports to the actual
output when its e row lies in the copied source interval. The result includes
the actual output e-row lookup and its b<=p inequality. The endpoint-range
hypothesis remains explicit; this is not a global Sat preservation assertion
and does not yet discharge Sat_rec for all completion factors.
Full build succeeds (90 jobs); all 368 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Internal-predecessor Sat transport

CopySatInternal proves row_p_lt_e, discharging the endpoint-range condition for
copied source rows whose original predecessor is at least the copy threshold.
copyEntry_high_region_iff identifies exactly the defined entries mapping to
indices at least the old owner. Consequently shortCopy_sat_output_predecessor
obtains the actual transported Sat witness directly from a high predecessor in
the copied row. Source-row identity, source-range, and eligibility remain explicit;
this does not yet identify historical rows after intervening completion/native
operations or prove long-word Sat_rec.
Full build succeeds (91 jobs); 372 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Actual output internal Sat

CopyInternalSat proves shortCopy_internal_sat directly for any actual output
row whose predecessor is at least the parent's old owner and whose core is
native-eligible. It reconstructs the original source row from the successful
mapM, transfers eligibility back by length/step preservation, and invokes the
copied Sat witness theorem. No original-row identity or endpoint-range premise
is required from the caller. Parent core validity, parent Sat, successful copy,
and the output high-predecessor/eligibility conditions remain explicit.
This establishes internal Sat immediately after copying, not persistence through
subsequent completion/native events or the full historical Sat_rec theorem.
Full build succeeds (92 jobs); 373 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Sat witnesses in preserved scan prefixes

ScanSatPrefix proves local Sat-witness transport through unchanged prefixes,
then specializes it to actual later scan steps and frozen-fold prefixes.
shortCopy_scan_old_prefix_rowAt proves that every inherited row below the old
last owner remains identical to the parent throughout every reachable scan
history. shortCopy_scan_old_sat consequently recovers its actual Sat witness
in every such state. This does not claim Sat preservation at a row while that
row itself undergoes completion/native, which remains a separate obligation.
Full build succeeds (93 jobs); 378 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Conditional completion owner Sat

CompletionSat proves completeMarkRow_e via exact middle-entry rank transport.
completion_preserves_owner_sat combines this with p preservation: for sources
below p, y>=e, fresh targets, disjoint sources, and y<owner, completion keeps
both p and e and the actual e-row Sat witness in the updated pattern. These
geometry assumptions remain explicit and must still follow from the intended
semantic interval argument; no guard-to-geometry theorem is asserted.
Full build succeeds (94 jobs); 380 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Native top Sat witness

NativeTopSat proves the actual top row retains e, and its p is the head of a
nonempty native source chain. The head is identified directly from the source
algorithm as b of the old e row. Nonempty native implies step>1, hence e<owner,
so that e row is unchanged in the actual output. native_top_sat_witness therefore
supplies b(e)=p for the literal top row in that output. Lower rows and full
native-output Sat remain to be proved; this is not a whole-block Sat theorem.
Full build succeeds (95 jobs); 384 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Native descent endpoint and source-chain edges

NativeLowerSat proves nativeLower_e_old_p for both medium and short descent:
the new e is the previous row's p, assuming CoreValid and step>1. It extracts
exact nonempty source-algorithm steps, the final stopping inequality b<=p,
and every adjacent b edge in the full source chain. The correspondence between
these chain positions and all lower block p-values still must be assembled to
obtain full native-block Sat; no full-block conclusion is asserted yet.
Full build succeeds (96 jobs); 388 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Native block endpoint indexing

NativeBlockEndpoint proves exact e-index formulas for both short and medium
blocks, then discharges their shape/target hypotheses for actual native blocks.
nativeBlock_adjacent_ep identifies each lower e with the next row's p.
nativeBlock_source_e identifies the e of row rank(x) with source x, complementing
the existing p of row rank(x)+1. Joining these positions to source-chain b edges
and the bottom stopping inequality is still required for full block Sat.
Full build succeeds (97 jobs); 393 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Native bottom Sat in the actual output

NativeBottomSat extracts the successful source-fuel computation, proves its last
source has a b-value at most the old p, and proves that last source has rank zero
in the decreasing source list. native_bottom_sat_witness then identifies the
actual output row at the old owner, proves its p is the old p and its e is the
last source, and supplies the unchanged e-row with b<=p. The middle rows still
need their adjacent source ranks linked to b edges for whole-block Sat.
Full build succeeds (98 jobs); 397 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Full nonempty native replacement-block Sat witnesses

NativeMiddleSat proves rank conversion for decreasing lists, actual adjacent
source b equations, and the corresponding actual middle-output-row witness
b(e)=p. native_block_sat_witness combines bottom, middle, and top cases and
covers every j<=sources.length of a nonempty native replacement block. It
requires input CoreValid and successful native, not parent Sat. This completes
the local block witness proof, but does not yet prove Sat for the whole output
pattern, since block-external rows need separate treatment.
Full build succeeds (99 jobs); 401 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Native suffix Sat away from the owner endpoint

NativeSuffixSat proves b transport under row shifting, monotonicity of the
index shift, and actual suffix-row Sat witness transport for e != native owner.
Endpoints below the owner use the unchanged prefix; endpoints above it use the
actual suffix lookup and shifted b value. The e=owner case remains open and
requires control of the replacement bottom row's b. No whole-output Sat theorem
is claimed by these partial suffix cases.
Full build succeeds (100 jobs); 404 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Native bottom b bound

NativeBottomBound proves that every old core entry below the owner is at most
its b entry, and every row in nativeBlockDown has core contained in the top
core. Sources lie below old e, which is below the owner for nonempty native;
new targets cannot contribute below the bottom owner. These facts give
native_bottom_b_le for the actual bottom row: its b is at most the old row's b.
This supplies the missing comparison for suffix Sat witnesses with e=owner;
its final integration into whole-pattern Sat is still pending.
Full build succeeds (101 jobs); 409 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Whole-pattern Sat for nonempty native

NativeSatClosure completes suffix witness transport including e=owner, using
the actual bottom b bound. native_sat_nonempty_of_others combines prefix,
replacement-block, and suffix cases: if all input rows are CoreValid and every
eligible row other than the processed owner has a Sat witness, a successful
nonempty native has Sat on the entire output. The processed input owner need
not satisfy Sat. This does not yet supply the hypotheses after arbitrary
completion events, or establish the whole fullScan Sat theorem.
Full build succeeds (102 jobs); 411 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Unified native Sat establishment

NativeSat proves that empty nativeSources on an eligible valid row yields an
actual Sat witness from the source algorithm's stopping condition. Combined
with native_sat_nonempty_of_others, native_sat_of_others now handles every
successful native: CoreValid plus Sat on all rows except the processed owner
implies Sat on the output. Full-scan induction still needs the weaker advancing
prefix formulation, since future unprocessed rows need not yet satisfy Sat.
Full build succeeds (103 jobs); 413 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Full scan Sat from actual intermediate legality

ScanSat defines SatBelow and proves native advances it across the replacement
block, without assuming Sat on future rows. Frozen-mark completion preserves
previously scanned witnesses because their e rows lie in the unchanged prefix.
scanReach_sat_prefix establishes the invariant on every actual reachable state
under historyValid. fullScan_sat_of_history_valid proves Sat of every successful
fullScan under that same explicit intermediate CoreValid hypothesis. No input
Sat hypothesis or packet hypothesis is required for this final combinatorial
Sat step; establishing historyValid still needs the missing local completion
geometry/semantic closure. This is conditional, not a completed domain theorem.
Full build succeeds (104 jobs); 417 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Exact +1-guard endpoint

PacketEndpoint proves row_e_of_p_succ_mem: a valid core with p and p+1 present
has e=p+1. currentPlusOne_head_endpoint applies it to the actual first internal
trace edge. scan_packet_head_b_bound combines this with the proved scanned-prefix
Sat invariant to obtain b(child+1)<=child for an eligible scanned factor.
Eligibility remains explicit: this does not settle long factor rows, and no
parallel packet is asserted from this endpoint bound alone.
Full build succeeds (105 jobs); 420 theorem declarations audited without sorryAx.
The overall target remains unproved.


## All guarded endpoints; removal of unnecessary eligibility

PacketAllEndpoints proves exact e=child+1 at every internal factor edge. It
first transports scanned-prefix Sat to every eligible edge, then strengthens
the b endpoint result: currentPlusOne_all_endpoint_b_bounds requires only
CoreValid and the actual guarded trace, with no eligibility, historyValid, or
Sat assumptions. Once e=child+1 exists within the pattern, b<child+1 follows
from core validity alone. This covers long factors for this first-endpoint
inequality only; multi-target parallel chains and historical packet propagation
remain unproved and do not follow from this bound alone.
Full build succeeds (106 jobs); 423 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Actual full-scan totality from intermediate legality

ScanTotal proves scanFuel_total_of_history_valid using actual reachable states,
native_total, preservation of length by completion, and strict decrease of
remaining old rows. The implementation's initial a.length fuel suffices.
fullScan_total_sat_of_history_valid now gives existence of a successful output
and Sat together, rather than assuming success. historyValid still quantifies
actual reached completed patterns and remains to be derived from the missing
completion geometry/semantic argument; no unconditional domain closure is claimed.
Full build succeeds (107 jobs); 426 theorem declarations audited without sorryAx.
The overall target remains unproved.


## Cut structural closure

CutClosure proves cut_is_prefix and preservation of CoreValid, ProperMarks,
actual HasTraces, and Sat by every successful cut, from the corresponding
input invariants. Trace transport uses proper marks to keep its whole chain
within the retained prefix; Sat endpoint lookup uses e<=owner. These are actual
cut operation theorems and introduce no packet or completion-history premises.
Semantic certificate restriction and the overall generated-domain closure
remain unproved, along with the final well-order target.
Full build succeeds (108 jobs); 431 theorem declarations audited without sorryAx.


## Auxiliary E-step structural closure (2026-09-10)

AuxiliaryClosure verifies the appended auxiliary row [anchor,n+1] at owner n+1
when anchor<=n, preserves old traces under the append, and proves every
successful auxiliaryStep preserves CoreValid, ProperMarks, and HasTraces.
This connects the actual E helper to the completed short-copy theorems.
Auxiliary-step totality, Sat preservation, finite E iteration, and semantic
linedness/cutoff obligations remain open; no complete E closure is claimed.
Full build succeeds (109 jobs); 438 theorem declarations audited without sorryAx.
The overall target remains unproved.


## 2026-09-10: auxiliary E totality and finite iteration

AuxiliaryTotal.lean proves existence of successful mapM/copy rows from entrywise
existence, then auxiliaryStep_total for valid input with positive anchor bounded
by input length and length at least two. The proof checks full source rows,
including implicit endpoints, against the actual copyEntry implementation.
expandFrom_total_coreValid proves every finite fixed-anchor iteration exists and
preserves CoreValid. expandFrom_preserves_marks_traces propagates CoreValid,
ProperMarks and HasTraces through successful iterations. The anchor bound is
maintained by the proved prefix property, not assumed at intermediate stages.
Verified: lake build 110 jobs; 443 theorem declarations audited, no sorryAx.
Still open: connect legal classified E inputs to these initial hypotheses,
E Sat preservation, completion history validity, long endpoint packets and
all ordinal semantics/final well-ordering obligations. Main target unproved.


## 2026-09-10: actual E entry totality and preservation

ExpansionTotal.lean connects the fixed-anchor results to expand itself.
classify_expand_last extracts a last row of core length at least four from
successor/limit classification. coreValid_expansion_bounds uses strict natural
index spacing to derive positive penultimate anchor, anchor <= owner-1 and
owner > 2. Thus expand_total_coreValid proves, from row CoreValid and actual
successor/limit classification only, existence and CoreValid for every finite
E parameter. expand_preserves_marks_traces also preserves ProperMarks and
HasTraces through the real cut-then-iterate implementation.
Verified: lake build 111 jobs; 447 declarations audited, no sorryAx.
Remaining: E Sat preservation; M_star completion history validity and long
endpoint packets; ordinal semantics, I2/Steel and final well-order/injectivity.
The complete manuscript target is not proved.


## 2026-09-10: E copied-row Sat witnesses

AuxiliarySat.lean proves auxiliary_append_sat, shortCopy_sat_low_endpoint and
auxiliary_copied_row_sat. Appending the auxiliary row preserves Sat, including
its self-endpoint witness. A copied row with endpoint below the last-row minimum
uses its unchanged old endpoint row in the retained prefix. For auxiliary E,
the minimum equals the threshold: the low case and existing copied-endpoint
transport therefore cover every copied eligible source row. No extra endpoint
hypothesis is needed in auxiliary_copied_row_sat.
Verified: build 112 jobs; audit 450 declarations, no sorryAx.
Next: classify all auxiliary output rows as old-prefix or copied-source rows,
assemble whole-step Sat preservation and induct over expandFrom/expand.
Main target and previously recorded packet/semantics obligations remain open.


## 2026-09-10: complete E combinatorial invariant closure

ExpansionSat.lean proves auxiliaryStep_preserves_sat by decomposing actual
successful shortCopy output into retained prefix and mapped source rows. The
source interval excludes the auxiliary row, so the copied-row witness theorem
applies to original rows. expandFrom_preserves_sat inducts with the prefix
length bound, and expand_preserves_sat connects the actual classified entrance.
expand_total_invariants now jointly states totality for every finite parameter
and preservation of CoreValid, ProperMarks, HasTraces and Sat from exactly those
input invariants plus successor/limit classification. No new semantic premise
or restriction on the implemented E edges was introduced.
Verified: build 113 jobs; audit 454 declarations, no sorryAx.
Next central obligations: M_star completion validity/mark/trace closure from
actual guards and history, long endpoint packets, then ordinal semantics and
the manuscript's I2 well-foundedness and short-key well-order/injectivity.
The main theorem is still unproved.


## 2026-09-10: entry-copy trace Sat transport

CopyTraceSat.lean proves exact predecessor equations for all internal trace
edges, then supplies actual Sat witnesses for every eligible internal factor
of an entry-copy trace whose factors are in the copied region. The terminal
variant derives the entire region condition from the single terminal bound
using strict trace descent. The result uses parent Sat and actual shortCopy,
without any +1 guard or global Sat assumption on its output.
Verified: build 114 jobs; audit 457 declarations, no sorryAx.
Scope: this is entry-state transport only. Connecting later scan traces to
these entry traces still requires the historical predecessor/geometry argument.
The manuscript explicitly uses natural-cutoff/critical-point interval semantics
to establish completion gaps, so those gaps cannot be asserted as consequences
of the combinatorial guard alone. Full history closure and main target remain
unproved; no stronger semantic assumption was silently added.


## 2026-09-10: remove frozen intermediate-validity premise for pending marks

FrozenEntryTrace.lean reflects traces below an unchanged prefix using validity
of the pre-edit pattern only. completion_sources_between_from_entry derives
source bounds for current-owner completions with y < owner, without assuming
validity of the modified owner or the whole modified pattern. It retains both
the current trace and its identical pre-fold trace. The resulting later-mark
preservation proves frozen_pending_marks_from_entry: pending original marks
survive every processed prefix using initial validity, sorted original marks
and their owner bound, without the previous prefixValid premise.
Verified: build 115 jobs; audit 461 declarations, no sorryAx.
This removes a local induction dependency, not the global historyValid premise.
No connection across native index shifts is asserted. Long packet geometry,
full semantic closure and the final manuscript theorem remain unproved.


## 2026-09-10: source uniqueness from successful execution alone

NativeWalkUnique.lean proves successful B walks are independent of fuel,
each emitted source has a strictly shorter successful suffix, and hence a
successful walk never revisits its initial row. Induction gives source Nodup
without any CoreValid premise. nativeSources_nodup_of_success and
scanReach_record_nodup lift this to actual source records.
completion_record_nodup_of_history covers arbitrary current-owner edits using
only the actual record history, eliminating historyValid for this obligation.
Strict decreasing order and numeric source bounds still require validity;
those stronger claims have not been inferred from termination alone.
Verified: build 116 jobs; audit 468 declarations, no sorryAx.
Main semantic closure, packet geometry and final well-order remain open.

## 2026-09-10: bounded actual-generation consistency check

CheckGenerated.lean explores all cut/M_star children and E(1), E(2) children
through depth 10, deduplicating literal states. It checks CoreValid, Sat,
proper sorted marks with valid source positions, successful computeMarkTrace
for every mark, absence of key collisions among all encountered states, and
that a transient defined shortCopy does not lead to a failed mStar scan.
The root is checked too. Check failures raise IO errors. Recorded output in
generated-check-latest.txt: 814 distinct states, no failures, exit 0.
This is finite executable evidence only: not a proof of Generated closure,
not exhaustive over E parameters or depths, and not an axiom-audited theorem.
Formal library remains at 468 audited declarations / 116 build jobs.
Main remaining work is still the natural-cutoff interval/packet semantic
argument and its connection to scan history, followed by global well-order.


## 2026-09-10: natural cutoff algebra and weak agreement definitions

NaturalCutoff.lean defines displayed-order word composition and the natural
cutoff of nonempty factor words, keeping the trace endpoint separate. The
snoc theorem is exactly the manuscript's prefix applied to theta(terminal+1).
cutoffAgreement compares membership for both arguments below the bound; it
does not assert equality of function values. Reflexivity, symmetry, transitivity
and restriction follow directly from that definition.
The cutoff interval and exact-successor-bound theorems are proved over arbitrary
actions/relations with explicit order-preservation and adjacent edge hypotheses.
They do not postulate axioms or instantiate elementary embeddings. Establishing
these hypotheses from genuine V_lambda BLS realizations remains required, as do
rank semantics, I2, Steel, interval/packet closure and the final well-order.
Verified: build 117 jobs; audit 477 declarations, no sorryAx.


## 2026-09-10: natural cutoff bounds from literal realized row edges

RealizedEdges.lean defines only the finite step-edge component of realization
on full rows, including the implicit owner+1 endpoint. realizesEdges_p and
realizesEdges_e derive the two last image equations from those literal edges.
guarded_trace_cutoff_exact uses the actual currentPlusOne guard on an actual
Trace to recover theta(y+1). realized_trace_cutoff_bounds derives the strict
lower and weak upper bounds on Delta from literal row validity, edge realization,
monotone theta and order-preserving actions, with no guard assumption.
These are conditional semantic lemmas, not an elementary-embedding model:
critical points, rank/V_lambda, realization existence and preservation still
need proofs, as do the packet/interval and final well-ordering obligations.
Verified: build 118 jobs; audit 482 declarations, no sorryAx.


## 2026-09-10: minimum characterization of natural Delta

CutoffMinimum.lean defines the list of all factor successor bounds transported
by their preceding word. Append/snoc formulas identify this list with the
manuscript's prefix-action description. naturalCutoff_minimum proves Delta is
an actual member and is below every member. realized_trace_cutoff_minimum
obtains the needed adjacent inequalities from literal full-row edge realization
and monotone theta/actions for an actual trace, without the +1 guard.
Verified: build 119 jobs; audit 486 declarations, no sorryAx.
This is still conditional on a realization; no V_lambda embedding construction,
critical-point interval lemma, packet closure, or final well-order is claimed.


## 2026-09-10: weak agreement reads ordinal edges and detects movement

WeakAgreementEdges.lean proves equality from bounded lower sections of a strict
total order. Applied to ordinal membership, cutoffAgreement reads an image below
Delta without assuming the other ordinal image lies below Delta. A separate
movement theorem only needs the moved argument below Delta, not its image;
comparison against a fixed initial segment then bounds the other critical point.
These lemmas use precisely weak membership agreement, not pointwise equality.
Their explicit ordinal membership/order/rank-interface hypotheses remain to be
instantiated by the real set-theoretic model; no model or critical-point witness
has been assumed to exist by a new axiom. Packet geometry, semantic operation
closure, I2/Steel and the final well-order theorem remain unproved.
Verified: build 120 jobs; audit 491 declarations, no sorryAx.


## 2026-09-10: exact word image from actual trace edges

TraceWordSemantics.lean proves that the factor word of an actual Trace sends
theta(source) to theta(target), using literal realized p edges. The terminal
source node is excluded from the word. Compatibility of set actions with
ordinal actions lifts this equality to ordinal sets. weak_trace_reads_source_edge
then reads the owner's source edge from membership cutoffAgreement, with
explicit bounds for source and target and no bound on the owner's unknown image.
Verified: build 121 jobs; audit 495 declarations, no sorryAx.
All realization/compatibility/order hypotheses remain explicit; actual elementary
embeddings, certificate closure, interval packets and final well-order are not
yet constructed or proved. The full target remains open.


## 2026-09-10: actual ZFC rank model infrastructure

Added mathlib v4.30.0 at c5ea00351c28e24afc9f0f84379aa41082b1188f,
matching the existing Lean toolchain. Independent package working copies were
cloned from local repositories, with upstream origins restored and locked
revisions preserved. Required 933 cache files were already available locally.
ZFCSemantics.lean defines cutoffAgreement on genuine ZFSet rank and proves its
exact equivalence with quantification over V_delta. The ordinal-image reading
lemma is instantiated using Mathlib's actual ordinal membership and rank
identities, requiring only that the unknown image is a ZFC ordinal.
RankDomain lambda represents V_lambda; rank-map extension and agreement
equivalence for delta <= lambda connect internal functions to the set-level
lemmas. No elementary or nontrivial embedding existence has been assumed.
Verified: full lake build 1070 jobs; audit 499 local theorem declarations,
no sorryAx. The build job increase is dependency infrastructure, not new proof
coverage. Actual elementary embeddings, I2, interval/packet operation closure,
Steel and the final well-order theorem remain open.


## 2026-09-10: genuine first-order rank-domain embedding interface

RankElementarity.lean installs the pure binary membership language on the
actual RankDomain lambda. RankElementaryEmbedding uses Mathlib's full
first-order ElementaryEmbedding type, rather than an arbitrary monotone map.
Membership preservation/reflection and injectivity are derived from that type.
No nontrivial embedding or I2 witness is asserted to exist. Definability and
preservation of ordinals, critical points, rank application and the I2-to-root
construction still require development, along with semantic closure and the
final well-ordering theorem.
Verified: build 1104 jobs; audit 501 local declarations, no sorryAx.


## 2026-09-10: ordinal definability and genuine elementary preservation

OrdinalDefinability.lean proves rank-domain closure under membership and the
absoluteness of the two transitivity clauses defining ZFSet.IsOrdinal. Explicit
pure-membership first-order formulas express these clauses and their conjunction.
rankElementary_isOrdinal_iff now derives preservation and reflection of actual
ZFSet ordinalhood from full elementarity on RankDomain lambda. It does not
assume ordinal preservation as an extra property of the embedding.
Verified: build 1105 jobs; audit 506 local declarations, no sorryAx.
Next: induced ordinal action and its strict monotonicity/compatibility, then
critical-point and rank-application infrastructure. I2 existence/root witnesses,
semantic packet closure and the final theorem remain unproved.


## 2026-09-10: ordinal action induced by genuine elementarity

OrdinalAction.lean constructs the action on ordinals below lambda from the
rank of the actual ordinal image. Compatibility follows from proved ordinal
preservation, and strict order preservation/reflection follows from membership.
Monotonicity and inflationarity follow; a moved ordinal strictly increases.
The action also commutes with composition of elementary embeddings. None of
these properties is added as an axiom or independent embedding assumption.
Verified: build 1106 jobs; audit 514 local declarations, no sorryAx.
Critical-point existence from nontriviality, I2/root construction, rank
application, packet/certificate closure and final well-order remain open.


## 2026-09-10: least moved ordinal and composition critical point

RankCriticalPoint.lean defines the least moved ordinal for the genuinely
induced ordinal action. Existence is proved from an explicit moved-ordinal
witness using well-foundedness; uniqueness, strict movement, minimality and
fixing all smaller ordinal sets follow. rankCriticalPoint_comp proves the
critical point of composition is the minimum of the two critical points,
using the proved inflationarity so movement cannot be undone.
This does not yet derive a moved ordinal from arbitrary nontriviality, or
construct I2/root witnesses. Those and rank application, semantic operation
closure, packet geometry and the final well-order remain open.
Verified: build 1107 jobs; audit 520 local declarations, no sorryAx.


## 2026-09-10: critical-point transfer under actual weak rank agreement

RankAgreementCritical.lean derives movement transfer directly from weak
membership agreement on RankDomain lambda and the genuine induced ordinal
actions. If one critical point is below Delta, the other is shown equal when
present; an existence theorem then removes the second critical-point premise
entirely using the transferred moved-ordinal witness. No pointwise agreement
or bound on the moved image is used. These results instantiate the earlier
abstract critical-point mechanism in actual ZFC rank domains.
Verified: build 1108 jobs; audit 523 local declarations, no sorryAx.
I2/root existence, rank application, packet/interval and certificate closure,
and the final well-ordering theorem remain open.


## 2026-09-10: actual marked rank realization and semantic cut closure

RankMarkedRealization.lean assembles genuine rank-domain elementary embeddings,
finite increasing cardinal ordinals, critical points at row minima, full step
edges and actual mark traces carrying precisely natural-cutoff weak agreement.
The predicate also requires the already identified syntactic invariants and Sat.
It is a definition of the row/mark realization component, not an assertion of
existence or a substitute for the standard first-triple linedness family.
rankMarkedRealization_cut proves this entire component survives actual cut with
the same lambda, theta and embeddings. Mark words and their Delta are unchanged;
trace transfer uses their earlier-row bounds. No semantic edge filter was added.
Verified: build 1109 jobs; audit 525 local declarations, no sorryAx.
Standard root witnesses, full finite linedness family, E/M_star semantic closure,
rank application, packet geometry and final well-order remain open.


## 2026-09-10: finite realized mark cutoff bounds

RankCutoffBounds.lean proves theta(y) < Delta <= theta(y+1) directly from an
actual RankMarkedRealization and Trace, using only column indices bounded by
the finite pattern. It does not require theta to be monotone on all naturals
or add cutoff bounds as realization assumptions. rankRealization_mark_certificate
packages the exact MarkTrace, computed natural cutoff, derived interval bounds
and the existing weak rank agreement for every actual mark.
Verified: build 1110 jobs; audit 527 local declarations, no sorryAx.
Existence of standard realizations/linedness and E/M_star semantic closure,
rank application, interval packets and final well-order remain open.


## 2026-09-10: genuine word embeddings and marked critical points

RankWordEmbedding.lean composes the actual elementary embeddings and proves
agreement with the displayed-word evaluator on both sets and ordinal actions.
For each mark in a RankMarkedRealization, the word embedding's critical point
is proved to be the owner's minimum cardinal column. Visibility follows from
that column being <= the marked target and the derived strict Delta bound;
weak membership agreement transfers the actual critical point. No independent
word-critical-point assumption is introduced.
Verified: build 1111 jobs; audit 530 local declarations, no sorryAx.
I2/root and linedness witnesses, rank application, interval/packet closure,
E/M_star semantic preservation and final well-order remain open.


## 2026-09-10: factor critical-point bounds become literal column bounds

RankWordFactors.lean proves a word cannot undo ordinal movement of any member
factor, using genuine induced-action monotonicity and inflationarity. Hence a
word critical point is no greater than each factor's critical point. Applied
to actual marked realizations and the proved owner-word critical equality,
every factor row minimum is at least the marked owner's minimum column.
This is a derived semantic constraint, not a new syntactic edge filter.
Verified: build 1112 jobs; audit 533 local declarations, no sorryAx.
Main I2/root, application, interval/packet and semantic operation closure, and
final well-ordering obligations remain open.


## 2026-09-10: attainment of marked factor minimum

RankWordMinimum.lean proves that if a word moves an ordinal then some factor
moves it, and that every actual nonterminal trace factor has a row. Applying
these facts to the marked word's genuine critical point produces a factor row
whose minimum column equals the owner's minimum. Together with the previous
factor lower bound this establishes attainment, not just a lower estimate.
Verified: build 1113 jobs; audit 537 local declarations, no sorryAx.
I2/root, application, interval/packet and semantic operation closure, and the
final well-order remain unproved.


## 2026-09-10: nonempty native has minimum strictly below p

NativeMinimum.lean proves that a valid ordinary row with p equal to its head
must have exactly core [minimum, owner] and step 1. Its actual native operation
is the identity with empty sources. Consequently any nonempty successful native
has minimum < p at its input. This is a prerequisite for the manuscript's
exclusion of a nonempty completion at a mark whose source is the owner's minimum.
Transport to the current recorded terminal row is not yet proved, and that
exclusion is not claimed complete.
Verified: build 1114 jobs; audit 540 local declarations, no sorryAx.
Main root/I2, application, packet/interval closure and final well-order remain open.


## 2026-09-10: recorded minimum transport and minimum-source exclusion

NativeRecordedMinimum.lean proves the bottom output row of a nonempty native
has minimum < p, using its endpoint below the old owner. Scan-prefix persistence
transports this to every nonempty recorded terminal row. Combining it with the
actual marked-word factor minimum bound proves
realized_completion_source_above_minimum: a successful completion's source is
strictly above its owner's minimum. Thus a minimum-source mark is excluded.
Scope: this theorem requires current RankMarkedRealization and the existing
historyValid premise. It does not prove those assumptions through completion
or yet cover arbitrary intermediate frozen-owner edits without realization.
Verified: build 1115 jobs; audit 544 local declarations, no sorryAx.
Full history closure, packet/interval geometry, root/I2, application and final
well-order remain open.


## 2026-09-10: derive completion targets above e

CompletionTargetBound.lean proves that an ordinary step-target with source
strictly above the minimum has e <= target. The finite index proof covers
all ordinary shape alternatives, including long rows. Combined with the
recorded minimum exclusion, realized_completion_e_le_mark derives e <= y
for actual successful completion under current realization and historyValid.
Thus new targets y+1,... lie strictly above e. Source-gap/disjointness and
sources below p, plus realization/history closure, are still open; the existing
conditional completion Sat theorem is not yet unconditional.
Verified: build 1116 jobs; audit 546 local declarations, no sorryAx.
Main root/I2, application, packet closure and final well-order remain open.

## 2026-09-10: realized source-gap reflection

RealizedInterval.lean proves that an actual image lying strictly between two
consecutive step targets forces its source strictly between the corresponding
consecutive source columns. Bounding image equations come from literal full-row
edges; strict order reflection comes from genuine rank elementary embeddings.
It also proves exclusion of the source from the old core by adjacency.
Scope: the new image equation and target-gap inequalities remain explicit
premises. This does not yet construct the endpoint packet or prove these
premises for actual completion records, nor remove historyValid.
Verified: build 1117 jobs; audit 549 local declarations, no sorryAx.
Main root/I2, application, packet closure and final well-order remain open.

## 2026-09-10: weak rank agreement reads ordinal edges

RankAgreementEdges.lean derives equality of induced ordinal images from actual
weak rank agreement of elementary embeddings. Only the input and known output
must lie below delta (with delta <= lambda); no bound on the unknown output is
assumed. This supplies edge transfer needed before source-gap reflection.
The endpoint packet must still establish the known image equation and both
cutoff inequalities for actual completion records. No packet construction or
semantic history closure is claimed here.
Verified: build 1118 jobs; audit 550 local declarations, no sorryAx.
Root/I2, application, packet closure and final well-order remain open.

## 2026-09-10: target coverage suffices for weak packet transfer

RankPacketTransfer.lean removes separate source visibility from edge transfer:
the elementary ordinal action is inflationary, so a known image below the
cutoff forces its source below it. It then transfers every edge of a list
packet under a single weak agreement and target coverage hypothesis.
This matches the manuscript's historical Delta reading step; it does not
construct the actual packet from Sat_rec/current +1 or establish its target
coverage. Those are still independent, open event-induction obligations.
Verified: build 1119 jobs; audit 552 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: natural cutoff comparison under factor reindexing

CutoffReindex.lean proves by recursion on the actual factor word that preserved
factor actions and lowered successor columns imply a lowered natural cutoff.
Only factors occurring in this word require action equality and successor
comparison. Monotonicity transports the suffix comparison at each step.
This is a prerequisite for native old-mark certificate preservation; actual
native reindexing, successor-column inequalities and changed-word agreement
must still be supplied. No native semantic closure is claimed.
Verified: build 1120 jobs; audit 553 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: historical weak certificate reindexing

RankCertificateReindex.lean proves equality of the actual set-valued word
functions under reindexing of preserved factors. Combined with natural cutoff
comparison, it transfers an old rank weak certificate to the reindexed word
at its new natural cutoff. Owner and ambient rank domain remain the same.
This discharges certificate transport once factor preservation and successor
column inequalities are proved; those hypotheses are not yet established for
actual native, so native semantic closure remains open.
Verified: build 1121 jobs; audit 555 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: native shift successor bounds and certificate specialization

NativeCertificateShift.lean proves shiftAfter r t v + 1 <= shiftAfter r t (v+1).
Finite monotonicity of the new columns and preservation of the shifted old
columns therefore imply the successor comparisons required by cutoff transport.
The rank weak certificate theorem is specialized to this literal native map.
It still assumes factor embedding preservation, old-column preservation and
finite monotonicity of the new realization; constructing these data from an
actual native event remains open. No full native realization is asserted.
Verified: build 1122 jobs; audit 558 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: concrete native insertion values preserve old certificates

NativeColumnValues.lean defines the literal insertion of t new values after r
and proves shifted old values and new slots compute correctly. For old-word
successor comparison, only fresh 0 <= old (r+1) is necessary when t>0; all
other successor columns are exactly preserved. Applying the same construction
to embeddings automatically preserves every shifted old factor. The resulting
rankCertificate_native_values theorem no longer assumes factor preservation,
old-column preservation or full new-column monotonicity separately.
Fresh values/embeddings are still parameters: their actual native row edge,
critical-point and new mark realization, cardinality and strict order must be
constructed. This is old-certificate transport, not complete native closure.
Verified: build 1123 jobs; audit 562 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: actual native source images lie in the insertion gap

NativeImageGap.lean derives theta r < j_r(theta x) < theta (r+1) for every
source x emitted by actual nativeSources. Source bounds are obtained from the
successful source computation, and both image endpoints from the owner's
literal p/e step edges in RankMarkedRealization. These bounds are not assumed.
Thus owner images provide candidates with the required insertion-gap bounds.
Their cardinality, ordered enumeration and the full new embedding/row/mark
construction remain to be proved; full native closure is not claimed.
Verified: build 1124 jobs; audit 563 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: ordered concrete native image list

NativeImageColumns.lean constructs the candidate new columns by applying the
old owner to the increasing canonical source enumeration. For actual successful
nativeSources, the list has exactly sources.length entries, is strictly
increasing, and every entry lies strictly between theta r and theta (r+1).
Thus no arbitrary fresh-column order or gap bounds are postulated here.
Cardinality of these images and construction of the new row embeddings with
all edges and marks remain open, as does complete native semantic closure.
Verified: build 1125 jobs; audit 566 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: actual source images supply old-certificate transport

NativeFreshCertificate.lean indexes the ordered concrete native image list,
using the owner column only outside its range. Every indexed value is below
the old successor. For an actual successful nativeSources and an old weak word
certificate, the new natural cutoff exists and the certificate transports to
the shifted word with the concrete inserted source images. The first-column
bound and existence of the new cutoff are now proved, not premises.
Fresh row embeddings remain parameters: their edges, critical points and new
marks, and cardinality of inserted images, still need semantic construction.
This theorem alone does not establish all output MarkTrace obligations.
Verified: build 1126 jobs; audit 568 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: in-range fresh values are genuine ordered source images

NativeFreshOrder.lean proves every k < sources.length reads the actual kth
image, so the total-indexing fallback is absent from the inserted block.
These indexed values are strictly increasing and strictly above theta r;
the previously proved upper bound puts all of them in the insertion interval.
All conclusions use actual successful nativeSources and the input realization.
Full combined-column strict order, cardinality and new embedding realization
remain to be established; this is not complete native closure.
Verified: build 1127 jobs; audit 571 local declarations, no sorryAx.
Root/I2, application, packet construction, history closure and final well-order
remain open.

## 2026-09-10: full finite native column sequence is strictly increasing

NativeColumnOrder.lean proves insertion preserves finite strict order when the
fresh block is strictly increasing inside the old adjacent gap. It then applies
this to concrete native source images, deriving strict increase through every
column up to a.length+1+sources.length from the actual input realization and
nativeSources success. Comparisons across both block boundaries are included.
No new-column monotonicity is assumed in this concrete theorem.
Cardinality of inserted images and new row embedding/edge/mark realization
remain open, as do packet construction, I2/root, application and final well-order.
Verified: build 1128 jobs; audit 573 local declarations, no sorryAx.

## 2026-09-10: actual native suffix rows preserve all step edges

NativeSuffixEdges.lean proves the full shifted suffix row (including implicit
endpoint) is precisely the mapped old full row. With concrete inserted column
and embedding interpretations, every step edge of each old row i>r is retained.
The theorem includes the actual output rowAt equality from successful native,
so it refers to literal output rows, not only an abstract mapped row.
Fresh values and fresh embeddings are arbitrary here because suffix rows only
reference preserved columns. New block rows, cardinality and full marked
semantic closure remain open, along with I2/root, application and final order.
Verified: build 1129 jobs; audit 576 local declarations, no sorryAx.

## 2026-09-10: actual native suffix marks retain natural weak semantics

NativeSuffixCertificate.lean derives source computation from native success,
then combines actual output MarkTrace transport with concrete source-image
cutoff/certificate transport. Each old suffix mark has an accurate output trace,
a defined natural cutoff, and weak agreement with its actual shifted owner
embedding. The nonterminal word is reconciled via map/dropLast equality.
Fresh block embeddings remain arbitrary parameters because suffix words only
use preserved old factors. New block realization, new marks, cardinality,
I2/root, application, packet/history closure and final order remain open.
Verified: build 1130 jobs; audit 578 local declarations, no sorryAx.

## 2026-09-10: actual native suffix critical ordinals are preserved

NativeSuffixCritical.lean identifies any minimum of a shifted suffix row as
the shifted original minimum and proves that its interpreted ordinal remains
the critical point of the output owner embedding. The actual rowAt output
equality is included; both columns and embeddings use concrete insertion.
The proof handles minima on either side of the insertion boundary.
Together with suffix edge and mark lemmas this covers those components for old
suffix rows. New block realization, image cardinality, full semantic closure,
I2/root, application, packet induction and final well-order remain open.
Verified: build 1131 jobs; audit 579 local declarations, no sorryAx.

## 2026-09-10: actual native prefix rows retain all edges

NativePrefixEdges.lean bounds every full-row entry by its implicit endpoint,
then proves actual rows strictly before the native owner retain every step edge
under the concrete insertion interpretations. This includes the adjacent
prefix row whose implicit endpoint is the native owner column. Fresh block
values and embeddings need no assumptions for these prefix edges.
New block rows, complete marked closure, image cardinality, I2/root, application,
packet induction and final well-order remain open.
Verified: build 1132 jobs; audit 582 local declarations, no sorryAx.

## 2026-09-10: actual native prefix marks retain natural certificates

NativePrefixCertificate.lean proves prefix marked traces use only fixed columns,
so their entire trace lists are unchanged by native shift. It combines actual
prefix trace preservation with concrete inserted-image certificate transport:
each prefix mark has an accurate output MarkTrace, a defined natural cutoff
and weak agreement with its unchanged owner embedding. New block embeddings
remain parameters. This does not prove new block or newly born mark realization.
Image cardinality, I2/root, application, packet/history closure and final order
remain open.
Verified: build 1133 jobs; audit 583 local declarations, no sorryAx.

## 2026-09-10: actual native prefix critical ordinals are preserved

NativePrefixCritical.lean proves that each actual prefix row keeps the same
critical ordinal at its minimum under concrete column/embedding insertion.
The minimum bound is derived from CoreValid, not separately assumed.
Prefix and suffix edge, marked-certificate and critical-point preservation
are now available separately. The native block itself and inserted image
cardinality remain unproved, so complete realization closure is not claimed.
I2/root, application, packet/history induction and final well-order remain open.
Verified: build 1134 jobs; audit 584 local declarations, no sorryAx.

## 2026-09-10: source-rank targets realize concrete inserted pairs

NativeInsertedPairs.lean identifies the fresh value at a source's insertion
rank with the owner's image of that source. It then proves the retained owner
embedding sends the concretely interpreted source column to the newly inserted
column r+1+rank(source), for every actual successful native source.
The source rank is computed from the literal sources list; no image equation
or enumeration matching is assumed. This does not yet identify all resulting
block row step edges or construct the additional block embeddings.
Image cardinality, new block/mark realization, I2/root, application, packet/history
closure and final well-order remain open.
Verified: build 1135 jobs; audit 586 local declarations, no sorryAx.

## 2026-09-10: actual bottom native endpoint image

NativeBottomEndpointRealization.lean proves the actual bottom output row's
e-to-owner+1 edge under concrete source-image columns. The last descending
source is least, so its insertion rank is zero; native_bottom_sat_witness
identifies it with the literal bottom e entry. No bottom realization is assumed.
Removed duplicate native_success_sources and reused native_sources_of_success
in prefix/suffix certificates. The theorem count is unchanged after this cleanup.
Remaining block edges/embeddings, cardinality, new marks, I2/root, application,
packet/history closure and final well-order are still open.
Verified: build 1136 jobs; audit 586 local declarations, no sorryAx.

## 2026-09-10: strengthen bottom endpoint theorem to both distinguished edges

The existing rankRealization_native_bottom_endpoint now returns one actual
bottom row with its p/e identities and both realized p-to-owner and
e-to-owner+1 equations. The p bound is derived from the input valid core,
and its image from the old owner's actual full step edges. This strengthens
an existing theorem rather than adding a redundant wrapper.
All other bottom/block edges and new embeddings, cardinality, new marks,
I2/root, application, packet/history closure and final order remain open.
Verified: build 1136 jobs; audit 586 local declarations, no sorryAx.

## 2026-09-10: concrete candidate native block embeddings

NativeEmbeddingValues.lean defines all block embeddings by repeating the old
owner while preserving shifted old embeddings. Every entry is a genuine rank
elementary embedding by construction. Block singleton-factor weak agreement
holds at every cutoff by equality. This removes arbitrary fresh-embedding
parameters from the available candidate construction, but does NOT prove it
realizes every block row. Full top/lower step-edge alignment, actual direct
MarkTrace identification, inherited block marks and minima remain obligations.
Image cardinality, I2/root, application, packet/history closure and final order
remain open.
Verified: build 1137 jobs; audit 589 local declarations, no sorryAx.

## 2026-09-10: actual native top direct marks have natural certificates

NativeTopDirectCertificate.lean combines actual native_top_new_marks_have_trace
with the concrete repeated-owner embedding interpretation. Every new top mark
r+j (j<sources.length) has a literal two-node MarkTrace, its singleton-word
natural cutoff, and weak agreement with the top owner at that cutoff.
This includes the direct mark at r, and assumes no top-row realization.
Full block edges, inherited block marks, critical minima and image cardinality,
I2/root, application, packet/history closure and final order remain open.
Verified: build 1138 jobs; audit 590 local declarations, no sorryAx.

## 2026-09-10: native top inherited marks have concrete weak certificates

NativeTopOldCertificate.lean retains each inherited top mark's literal trace
and supplies its new natural cutoff and weak agreement under the repeated-owner
candidate embeddings and actual source-image columns. The old trace lies below
r, hence reindexing fixes every factor; actual top MarkTrace preservation is
used, not assumed as a semantic premise. Requires nonempty native sources.
Together with the direct-mark result both top mark origins are covered.
Full block edges, descendant mark transport, critical minima, image cardinality,
I2/root, application, packet/history closure and final order remain open.
Verified: build 1139 jobs; audit 591 local declarations, no sorryAx.

## 2026-09-10: native lowering preserves literal natural certificates

NativeLowerCertificate.lean defines row-local HasRankCertificates with explicit
source positions, actual Trace, natural cutoff and rank weak agreement. Both
medium and short nativeLower preserve it in a fixed ambient interpretation
with the same owner embedding. The existing pair-alignment lemmas transport
the literal source indices; trace, cutoff and weak certificate are retained.
Requires the established shape/proper/valid premises at that lowering step.
Full block induction and top packaging remain to be joined. Full block edges,
critical minima, cardinality, I2/root, application, packet/history closure and
final well-order remain open.
Verified: build 1140 jobs; audit 593 local declarations, no sorryAx.

## 2026-09-10: full native descent transports natural certificates

NativeBlockCertificate.lean lifts row-local certificate preservation through
all nativeBlockDown steps for both short and initial-medium shapes. It produces
a successful actual block with HasRankCertificates at every indexed row. The
induction proves lower validity/properness/shape and retains source positions,
traces, natural cutoffs and weak agreement; it does not assume intermediate
certificates. Top certificates and shape/target premises remain inputs.
Next integration is actual nativeTop packaging and shape discharge. Full block
edges/minima, image cardinality, I2/root, application, packet/history closure
and final well-order remain open.
Verified: build 1141 jobs; audit 595 local declarations, no sorryAx.

## 2026-09-10: actual native top supplies the full row certificate premise

NativeTopCertificates.lean proves the equivalence between literal row-local
HasRankCertificates and exact MarkTrace/cutoff/weak witnesses at rowAt. It then
classifies every actual nativeTop mark as inherited or direct and proves the
full row certificate premise for concrete source-image columns and repeated
owner embeddings. No semantic top-certificate hypothesis remains.
The next actual-block integration must discharge shape/target premises and
identify the block produced by descent with native's block.
Full edges/minima, cardinality, I2/root, application, packet/history closure and
final well-order remain open.
Verified: build 1142 jobs; audit 597 local declarations, no sorryAx.

## 2026-09-10: actual nonempty native block certificates

NativeActualBlockCertificates.lean supplies the actual nonempty nativeBlock
with HasRankCertificates at every row, using concrete source images and repeated
owner embeddings. Top certificates, validity/properness, ordinary shape and
all target-preservation premises are derived from the input realization and
native success. No intermediate certificate or shape premise is added.
Output rowAt packaging and empty-native integration remain, along with full
block edges/minima, cardinality, I2/root, application, packet/history closure
and final well-order.
Verified: build 1143 jobs; audit 598 #print axioms declarations, no sorryAx.
Audit output has 600 lines due to one multiline axiom list; declarations were
counted from Audit.lean rather than output line count.

## 2026-09-10: replacement certificates at actual output row indices

NativeReplacementCertificates.lean identifies the certificate-bearing block
with the exact block returned by successful native, then transfers certificates
to every actual rowAt b i in r <= i <= r+sources.length. Weak agreement now
uses the concrete embedding at i, proved equal to the old owner on the block.
Nonempty sources are still required; empty-case/all-output-row integration
remains. Full row edges/minima, cardinality, I2/root, application, packet/history
closure and final well-order are not yet proved.
Verified: build 1144 jobs; audit 599 declarations (counted from Audit.lean), no sorryAx.

## 2026-09-10: all actual native output rows have natural mark certificates

NativeAllCertificates.lean unifies empty insertion, prefix, replacement block
and suffix cases. Given input RankMarkedRealization and native success, every
actual output row has HasRankCertificates under concrete source-image columns
and repeated-owner nativeEmbeddingValues. All p/e witnesses are derived from
the input row; no nonempty, intermediate certificate or row-shape hypotheses
are exposed. Empty insertion reduces exactly to the original interpretation.
This completes the native marked-certificate component under these candidates,
not full RankMarkedRealization: block edges/minima and image cardinality remain.
I2/root, application/copy semantic closure, completion packet/history closure
and the final well-order also remain open.
Verified: build 1145 jobs; audit 601 declarations, no sorryAx.

## 2026-09-10: actual native top minimum and critical point

NativeTopCritical.lean proves nativeTop retains the original minimum column,
deriving minimum<=p from the valid input row and using actual low-entry
preservation. The actual nonempty top output row therefore has the correct
critical point under the concrete repeated-owner embedding and inserted columns.
No top minimum or critical-point preservation is assumed.
Descent of minima through the full block, all block edges, cardinality,
I2/root, application, packet/history closure and final order remain open.
Verified: build 1146 jobs; audit 603 declarations, no sorryAx.

## 2026-09-10: every valid nativeLower preserves the minimum

NativeLowerMinimum.lean proves both branches of actual nativeLower preserve
core.head? using the existing low-entry preservation theorem and step<length
from CoreValid. No separate medium/short shape, e-bound or minimum inequality
is assumed. This provides the common minimum invariant for block descent.
Full block minimum integration and critical points, full edges, image
cardinality, I2/root, application, packet/history closure and final order remain open.
Verified: build 1147 jobs; audit 604 declarations, no sorryAx.

## 2026-09-10: every row of the actual native block retains the original minimum

NativeBlockMinimum.lean propagates the common minimum through short and
initial-medium block descent. NativeActualBlockMinimum.lean discharges actual
shape, target, validity and properness premises from input realization and
successful nonempty native. The resulting literal nativeBlock has the original
minimum at every index; intermediate minimum preservation is not assumed.
Output rowAt critical-point packaging remains. Full block edges, image
cardinality, I2/root, application, packet/history closure and final order remain open.
Verified: build 1149 jobs; audit 607 declarations, no sorryAx.

## 2026-09-10: actual replacement row critical points

NativeReplacementCritical.lean identifies each actual output row in the
nonempty native replacement interval with the corresponding block member,
proves its minimum is the old minimum, and derives its critical-point condition
under the concrete embedding at that output index. Block embedding equality
and preservation of the minimum's column value discharge the semantic step.
All-output/empty critical integration, complete block edges, image cardinality,
I2/root, application, packet/history closure and final well-order remain open.
Verified: build 1150 jobs; audit 608 declarations, no sorryAx.

## 2026-09-10: all actual native output critical points

NativeAllCritical.lean unifies empty native, prefix, replacement and suffix:
every actual output row minimum denotes the critical point of its concrete
nativeEmbeddingValues entry. The old block minimum is obtained from CoreValid,
so no minimum witness or nonempty premise is exposed in the final theorem.
Native marked certificates and critical-point components are now both proved
for all output rows. Complete block step edges and inserted image cardinality
remain before full realization closure, as do I2/root, application/copy,
completion packet/history closure and the final well-order.
Verified: build 1151 jobs; audit 609 declarations, no sorryAx.

## 2026-09-10: medium native descent preserves every step edge

NativeMediumEdges.lean proves the full lower row after medium descent is exactly
the original core (including restoration of its owner as the lower implicit
endpoint). Step is unchanged, so every lower edge is an original literal edge.
The edge theorem uses only input CoreValid, positive owner, nativeLower success
and original edge realization, with the same action and column interpretation.
Short descent and actual top edge realization remain before full native edges.
Image cardinality, I2/root, application, completion packet/history closure and
final well-order also remain open.
Verified: build 1152 jobs; audit 611 declarations, no sorryAx.

## 2026-09-10: short descent full-row identity

NativeShortFull.lean proves the full lower row equals the original core with
e erased when nativeLower false succeeds on a valid row of step>1 and positive
owner. The old owner is restored as the new implicit endpoint; e<owner is
derived from sortedness/step. This isolates the single deletion whose index
shift must be reconciled with the reduced step in short edge preservation.
Short full-edge transport and actual top edges remain, along with cardinality,
I2/root, application, packet/history closure and final well-order.
Verified: build 1153 jobs; audit 612 declarations, no sorryAx.

## 2026-09-10: short native descent preserves all step edges

NativeShortEdges.lean proves every lower full step edge is realized by the same
action after short descent. From the lower edge's index bounds and m+1=2L,
the source is before e and the old target after e. Deletion preserves the
source index and subtracts one from the target index, matching step L-1.
Both medium and short lowering now preserve all edges under their row premises.
Actual top edge realization and full block integration remain, along with
image cardinality, I2/root, application, packet/history closure and final order.
Verified: build 1154 jobs; audit 613 declarations, no sorryAx.

## 2026-09-10: full native descent preserves all realized edges

NativeBlockEdges.lean propagates full Row.RealizesEdges through short and
initial-medium nativeBlockDown. The output BlockEdges uses the actual base+i
owner at each position; lower validity, shape and target prerequisites are
proved inductively. The action and column interpretation stay fixed.
Top edge realization remains a premise and must still be proved for nativeTop
with concrete source images; this is not yet actual native edge closure.
Image cardinality, I2/root, application, completion packet/history closure and
final well-order remain open.
Verified: build 1155 jobs; audit 615 declarations, no sorryAx.

## 2026-09-10: old top edge index alignment

NativeTopOldEdgeIndices.lean proves every old core entry at/above e shifts by
sources.length in nativeTop, using actual source interval bounds and exact
canonical insertion ranks. Combined with low-entry preservation, old pairs
with source<=p and target>=e align with the new step L+sources.length.
The interval conditions still appear in the pair theorem; exhaustive top-edge
classification, implicit endpoint and inserted source/target index alignment
remain to be assembled before full top realization.
Image cardinality, I2/root, application, completion packet/history closure and
final well-order remain open.
Verified: build 1156 jobs; audit 617 declarations, no sorryAx.

## 2026-09-10: derive all old core-edge interval bounds

NativeOldEdgeIntervals.lean derives source<=p and e<=target for every old
core-to-core step edge of an eligible ordinary row. Nonempty actual native
supplies eligibility, so every such old pair has its top indices aligned with
L+sources.length without separate low/high hypotheses. The implicit endpoint
edge and exhaustive classification of all new top source indices remain to join.
Full top edges, image cardinality, I2/root, application, packet/history closure
and final well-order remain open.
Verified: build 1157 jobs; audit 619 declarations, no sorryAx.

## 2026-09-10: concrete native top implicit endpoint edge

NativeTopEndpointRealization.lean proves nativeTop.e is the old e and that the
concrete top embedding sends its column value to the shifted implicit endpoint
r+sources.length+1. The source value is unchanged; the target denotes the old
r+1 column by concrete insertion preservation. The image equation follows from
the input e edge, without assuming any top realization.
Exhaustive top source-index classification and inserted pair alignment remain
before full top/block edge closure. Cardinality, I2/root, application,
completion packet/history closure and final order remain open.
Verified: build 1158 jobs; audit 620 declarations, no sorryAx.

## 2026-09-10: inserted top pairs align with the actual new step

NativeTopInsertedIndices.lean proves that source x occurs at m-L+rank(x), and
its corresponding target r+1+rank(x) occurs exactly L+sources.length later
in the actual nativeTop core. The rank bound comes from actual source membership;
source and target index formulas are reconciled with the new step.
Together with the established inserted image equations this supplies the new
pair case. Exhaustive source-index coverage remains before full top edges.
Image cardinality, I2/root, application, packet/history closure and final order
remain open.
Verified: build 1159 jobs; audit 621 declarations, no sorryAx.

## 2026-09-10: exhaustive top edge source classification

NativeTopSourceCases.lean proves actual source ranks cover all insertion positions,
and every full top step edge has a source index in exactly the required ranges:
old low source, inserted source rank, or final e source position. This removes
the outstanding coverage premise for assembling the three top edge cases.
Full top realization still requires joining their index and image equations.
Image cardinality, I2/root, application, completion packet/history closure and
final well-order remain open.
Verified: build 1160 jobs; audit 623 declarations, no sorryAx.

## 2026-09-10: complete concrete native top edge realization

NativeTopEdges.lean proves rankRealization_native_top_edges for nonempty actual
native sources. It joins the exhaustive source classification with old core
edges, insertion-rank image equations, and the implicit endpoint equation.
The embedding is the retained old owner and columns are the concrete source
images; no top edge realization is assumed. This closes the top-edge gap.
Next: propagate through the actual replacement block and all output rows.
Image cardinality, I2/root, application, completion packet/history closure and
final well-order remain open.
Verified: build 1161 jobs; audit 624 declarations, no sorryAx.

## 2026-09-10: actual native replacement block edges

NativeActualBlockEdges.lean derives edge realization for every row of the actual
nonempty native block from the concrete top theorem, discharging both medium
and short descent shape/target conditions. NativeReplacementEdges.lean transports
this result to each actual output row with r <= i <= r + sources.length and
the concrete nativeEmbeddingValues at i. No block edge premise remains.
Next: combine prefix, replacement, suffix and empty-source cases.
Image cardinality, I2/root, application, completion packet/history closure and
final well-order remain open.
Verified: build 1163 jobs; audit 626 declarations, no sorryAx.

## 2026-09-10: all native output edges

NativeAllEdges.lean proves rankRealization_native_all_edges for every successful
native operation, including empty sources and every prefix/replacement/suffix
row. Concrete native column values and embedding values are used throughout.
The complete edge component is now closed alongside all marked certificates
and critical points. This is not yet full realization: image cardinality and
any remaining global invariant assembly still require proof.
I2/root, application, completion packet/history closure and final well-order
remain open.
Verified: build 1164 jobs; audit 627 declarations, no sorryAx.

## 2026-09-10: exact native cardinal obligation

NativeCardinalObligation.lean proves an equivalence: all concrete output columns
are cardinal ordinals iff each actual native source image under the old owner
embedding is a cardinal ordinal. Old prefix/suffix columns need no additional
hypotheses; insertion ranks cover every new column. The source-image cardinal
statement itself remains unproved and is not added as an axiom.
Next: prove the needed cardinal preservation from actual rank elementarity,
checking rank-domain closure/absoluteness requirements.
I2/root, application, completion packet/history closure and final well-order
remain open.
Verified: build 1165 jobs; audit 628 declarations, no sorryAx.

## 2026-09-10: function graph closure at limit rank height

RankGraphClosure.lean proves every subset of x times y has rank below lambda
when x and y do and lambda is a successor-limit ordinal. In particular every
ZFSet.IsFunc graph stays in the rank domain. The proof bounds graphs by the
double powerset of x union y. This supplies witness closure for eventual
bijection absoluteness; no cardinal preservation theorem is claimed yet.
The limit-height hypothesis is explicit and must be supplied from the intended
I2 ambient construction. Formula coding, bijection absoluteness, source-image
cardinality, I2/root, application, packet/history closure and final order remain.
Verified: build 1166 jobs; audit 630 declarations, no sorryAx.

## 2026-09-10: ordered pairs inside limit rank domains

RankOrderedPair.lean defines the actual Kuratowski pair as a RankDomain element,
proves its rank bound at successor-limit height and component injectivity,
and identifies graph membership with the external ZFSet pair. This supplies
the internal objects needed for function/bijection formula semantics.
First-order pair/function/bijection definability and absoluteness are still
required before cardinal preservation; no such result is assumed here.
I2/root, application, completion packet/history closure and final order remain.
Verified: build 1167 jobs; audit 633 declarations, no sorryAx.

## 2026-09-10: pair predicate absoluteness

RankPairAbsoluteness.lean proves the domain-quantified unordered pair predicate
is equivalent to the external ZFSet unordered pair, and the existential
Kuratowski ordered-pair predicate is equivalent to the external ordered pair
at limit height. Witnesses are actual rank-domain sets. These are semantic
predicate equivalences; syntactic first-order formula coding remains to do.
Function/bijection absoluteness and cardinal preservation remain unproved.
I2/root, application, packet/history closure and final order remain open.
Verified: build 1168 jobs; audit 635 declarations, no sorryAx.

## 2026-09-10: unordered pair formula and elementary preservation

RankPairFormula.lean gives a literal membership-language formula for unordered
pairs, proves its realization equivalence, and derives unordered-pair
preservation/reflection directly from j.map_formula. This closes the syntactic
coding step for unordered pairs. Ordered pair composition and function/bijection
formulas remain before cardinal preservation.
I2/root, application, completion packet/history closure and final order remain.
Verified: build 1169 jobs; audit 637 declarations, no sorryAx.

## 2026-09-10: elementary ordered pair and graph membership preservation

RankPairPreservation.lean derives commutation of genuine elementary embeddings
with unordered and Kuratowski ordered pairs at limit rank height. It proves
pair(j x,j y) belongs to j f iff pair(x,y) belongs to f. This is pointwise graph
membership preservation only, not totality or surjectivity of the image graph;
those require quantified function/bijection formula semantics.
Cardinal preservation, I2/root, application, completion packet/history closure
and final order remain open.
Verified: build 1170 jobs; audit 640 declarations, no sorryAx.

## 2026-09-10: full function predicate absoluteness

RankGraphAbsoluteness.lean proves domain-quantified graph containment and
application equivalent to external product containment and ordered-pair
membership. It then proves rankIsFunction iff ZFSet.IsFunc, including totality
and uniqueness; external witnesses are lifted using graph containment.
These are semantic predicate equivalences, not yet first-order function
formula coding or image-function preservation. Bijection and cardinal
preservation, I2/root, application, packet/history closure and order remain.
Verified: build 1171 jobs; audit 643 declarations, no sorryAx.

## 2026-09-10: injectivity and surjectivity predicate absoluteness

RankBijectionConditions.lean proves domain-quantified onto and one-to-one graph
conditions equivalent to the corresponding external set conditions. The latter
uses graph containment to place the shared output in the rank domain. Together
with rankIsFunction_iff this supplies the component semantic equivalences for
bijections, but formula coding and the bridge to Cardinal remain open.
I2/root, application, packet/history closure and final order remain open.
Verified: build 1172 jobs; audit 645 declarations, no sorryAx.

## 2026-09-10: set graph to genuine cardinal equality

GraphCardinalBridge.lean constructs a bijective Lean function between the
member types from an external ZFSet function graph with onto and one-to-one
conditions, then proves equality of ZFSet.card via Cardinal.mk_congr and lift
injectivity. This supplies the graph-to-cardinal direction; the converse graph
construction and quantified formula preservation remain before source-image
cardinality. I2/root, application, packet/history closure and order remain.
Verified: build 1173 jobs; audit 647 declarations, no sorryAx.

## 2026-09-10: actual function graph construction

FunctionGraphConstruction.lean constructs a ZFSet graph from any function
between member types using ZFSet.range. It proves exact pair membership,
ZFSet.IsFunc, and transfer of injectivity/surjectivity to external graph
conditions. Together with GraphCardinalBridge this provides both construction
directions needed to relate graph bijections to member-type bijections.
Quantified formula coding and cardinal preservation remain open, as do
I2/root, application, packet/history closure and final order.
Verified: build 1174 jobs; audit 651 declarations, no sorryAx.

## 2026-09-10: internal bijection existence iff external cardinal equality

RankBijectionCardinal.lean combines all three internal graph predicates into
rankIsBijection and proves existence of such a graph in a limit rank domain
iff the two external ZFSet.card values are equal. The reverse direction
constructs the graph and discharges its rank bound; no internal witness is
assumed. Formula coding/preservation and ordinal initiality still remain for
source-image cardinality. I2/root, application, packet/history closure and
final order remain open.
Verified: build 1175 jobs; audit 653 declarations, no sorryAx.

## 2026-09-10: initial ordinal characterized by internal bijections

RankCardinalCharacterization.lean proves an ordinal is a cardinal ordinal iff
no smaller ordinal has the same cardinal, then translates this at limit rank
height into absence of internal bijection graphs from any smaller ordinal.
This closes the ordinal-initiality semantic bridge. The remaining formula
coding must quantify over all smaller ordinal-domain elements, not just images
of old elements; pointwise embedding preservation is insufficient.
Cardinal preservation, I2/root, application, packet/history closure and final
order remain open.
Verified: build 1176 jobs; audit 655 declarations, no sorryAx.

## 2026-09-10: ordered pair first-order formula

RankOrderedPairFormula.lean proves arbitrary-context relabeling semantics for
the unordered-pair formula and constructs the literal existential ordered-pair
formula with verified realization. This enables nested graph/function/bijection
formulas without assuming their definability. Those remaining formulas and
cardinal preservation are still open, as are I2/root, application,
packet/history closure and final order.
Verified: build 1177 jobs; audit 657 declarations, no sorryAx.

## 2026-09-10: graph application first-order formula

RankGraphFormula.lean supplies arbitrary-context membership and ordered-pair
formula interpretation, then constructs the existential graph application
formula with verified semantics. Nested bound-variable casts are proved to
preserve the original assignment. Function/bijection/cardinal formulas and
cardinal preservation remain open, along with I2/root, application,
packet/history closure and final order.
Verified: build 1178 jobs; audit 660 declarations, no sorryAx.

## 2026-09-10: quantified graph containment formula preservation

RankGraphBetweenFormula.lean codes graph containment in the membership
language, proves realization, and derives full preservation/reflection by
j.map_formula. Unlike pointwise pair preservation, this quantifies over all
members of the image graph and obtains witnesses in the image domain/codomain.
Totality/uniqueness and bijection formulas, cardinal preservation, I2/root,
application, packet/history closure and final order remain open.
Verified: build 1179 jobs; audit 662 declarations, no sorryAx.

## 2026-09-10: complete function formula and elementary preservation

RankFunctionFormula.lean provides arbitrary-context graph application, the
full totality/uniqueness formula, and its conjunction with graph containment.
Its realization is rankIsFunction; j.map_formula proves function preservation
and reflection over all domain elements. Bijection/cardinal formula assembly,
cardinal preservation, I2/root, application, packet/history closure and final
order remain open.
Verified: build 1180 jobs; audit 665 declarations, no sorryAx.

## 2026-09-10: onto formula and elementary preservation

RankOntoFormula.lean constructs the full codomain-quantified onto formula,
proves its realization, and derives preservation/reflection via j.map_formula.
The image-side property includes every member of j(y). Injectivity formula,
bijection existence formula and cardinal formula remain before cardinal
preservation. I2/root, application, packet/history closure and order remain.
Verified: build 1181 jobs; audit 667 declarations, no sorryAx.

## 2026-09-10: complete bijection formula and preservation

RankBijectionFormula.lean codes one-to-one graphs and combines function,
onto and one-to-one formulas into the full bijection formula. Realization
and preservation/reflection for an actual graph under j are proved.
Existential quantification over all graph witnesses remains necessary for
cardinal formula preservation; image-graph preservation alone is insufficient.
I2/root, application, packet/history closure and final order remain open.
Verified: build 1182 jobs; audit 670 declarations, no sorryAx.

## 2026-09-10: equinumerosity formula and external cardinal equality preservation

RankEquinumerousFormula.lean verifies arbitrary-context bijection formula
relabeling and existential graph quantification. At limit height it proves
card(j x)=card(j y) iff card(x)=card(y), using all internal graph witnesses.
This is preservation of equinumerosity, not yet preservation of being an
initial ordinal: the latter still needs a formula quantifying smaller ordinals.
I2/root, application, packet/history closure and final order remain open.
Verified: build 1183 jobs; audit 673 declarations, no sorryAx.

## 2026-09-10: no-member-bijection formula preservation

RankInitialFormula.lean codes the absence of bijections from any member to the
set itself, with full member and graph quantification. Formula interpretation
and elementary preservation/reflection are proved. The remaining ordinal
bridge must identify all members of ordinalDomainElement with smaller ordinal
domain elements, then transfer along rankOrdinalAction compatibility.
I2/root, application, packet/history closure and final order remain open.
Verified: build 1184 jobs; audit 676 declarations, no sorryAx.

## 2026-09-10: actual cardinal ordinal preservation and native columns

RankCardinalPreservation.lean identifies ordinal members with smaller ordinal
domain elements, proves rankOrdinalAction_cardinal_iff at successor-limit
height from literal first-order elementarity, and discharges all actual native
source-image and output-column cardinal obligations. No cardinal preservation
axiom or premise is used; limit height remains explicit and must come from the
intended I2 ambient construction. Native full realization assembly/global Sat
conditions need inspection next. I2/root, application, packet/history closure
and final order remain open.
Verified: build 1185 jobs; audit 680 declarations, no sorryAx.

## 2026-09-10: assembled native RankMarkedRealization closure

NativeRankRealization.lean proves rankMarkedRealization_native at limit height,
assembling all eight fields: core validity, marks, Sat, increasing columns,
cardinals, edges, critical points and marked certificates. Uses the actual
native result and concrete columns/embeddings. The input is a full
RankMarkedRealization (including Sat); this does not establish realizations
for intermediate completion scan states lacking that input. Standard linedness
is outside this structure and remains open, as do I2/root, application,
completion packet/history closure and final well-order.
Verified: build 1186 jobs; audit 681 declarations, no sorryAx.

## 2026-09-10: scope correction and unsaturated row semantics

Inspection of sat_nativeSources_empty shows a full RankMarkedRealization
forces native sources empty. Thus the assembled native theorem cannot by
itself cover productive scan steps. RankRowRealization.lean now separates all
seven row-semantic fields from Sat and proves conversion from the full
structure and reconstruction with Sat. Next required work is generalizing the
native semantic dependency chain to this unsaturated structure (not yet done).
The previously proved nonempty case lemmas retain overly strong input types
until this generalization. Cardinal preservation itself is unaffected.
I2/root, application, completion history and final well-order remain open.
Verified: build 1187 jobs; audit 683 declarations, no sorryAx.

## 2026-09-10: verified unsaturated native semantic closure

Generalized the complete native semantic dependency chain, including cutoff
bounds, word embeddings, intervals, marks, critical points, edges and source
cardinals, from RankMarkedRealization to RankRowRealization. The row structure
and conversions now live in RankMarkedRealization.lean to avoid import cycles.
rankRowRealization_native is fully built without Sat on the input or output;
thus its statement no longer forces sources empty. NativeSaturatedRealization
restores the original full theorem as a wrapper. RankRowCut adds cut closure
and trace extraction without Sat. Completion semantics/history, I2/root,
linedness, application and final well-order remain open.
Verified: build 1189 jobs; audit 686 declarations, no sorryAx.

## 2026-09-10: completion old marked semantic certificate transport

CompletionOldCertificate.lean lifts the existing explicit interval-case
trace preservation theorem to actual natural-cutoff and weak-agreement
certificates under unsaturated row semantics. The original word and cutoff
are retained. Source disjointness, target exclusion and interval cases are
still explicit premises; they must be derived from actual scan history.
New endpoint packet semantics, completion closure, I2/root, linedness,
application and final well-order remain open.
Verified: build 1190 jobs; audit 687 declarations, no sorryAx.

## 2026-09-10: certificates outside the completed row

CompletionOtherCertificate.lean proves semantic certificate transport for all
other rows whenever the replacement preserves predecessor p. The completion
specialization derives this from the existing explicit gap/disjointness bounds.
The natural cutoff and weak agreement remain the identical old witnesses.
Actual-history discharge of these bounds and new endpoint packet semantics
remain open, as do I2/root, linedness, application and final well-order.
Verified: build 1191 jobs; audit 689 declarations, no sorryAx.

## 2026-09-10: completion minimum preservation

CompletionMinimum.lean proves the completed core has the same minimum whenever
the completion mark and every source are at/above the old minimum. This needs
neither disjointness nor target exclusion. Actual history discharge and critical
point assembly remain; source/core disjointness, target gaps and the new packet
semantics remain the central completion obligations. I2/root, linedness,
application and final order remain open.
Verified: build 1192 jobs; audit 690 declarations, no sorryAx.

## 2026-09-10: actual completion minimum and critical point

CompletionActualCritical.lean derives minimum preservation from an actual
successful completionRecord and ScanReach using completion_sources_between.
It retains the old embedding critical point, without separate minimum bounds.
The global historyValid premise remains explicit and unproved; this is not
unconditional scan closure. Packet geometry/semantics, I2/root, linedness,
application and final order remain open.
Verified: build 1193 jobs; audit 692 declarations, no sorryAx.

## 2026-09-10: current successor column realizes the endpoint

CurrentSuccessorEdge.lean proves p+1 in a valid core forces e=p+1, since p and e
are adjacent core entries. Consequently its actual embedding sends theta(p+1)
to theta(r+1). This supplies the local semantic step needed to sharpen natural
cutoff bounds under currentPlusOne. Whole-word exact cutoff, packet geometry,
completion/history closure, I2/root, linedness, application and final order
remain open.
Verified: build 1194 jobs; audit 694 declarations, no sorryAx.

## 2026-09-10: exact natural cutoff under currentPlusOne

CurrentExactCutoff.lean proves that for any realized trace satisfying the
actual currentPlusOne boolean guard, its defined natural cutoff is exactly
theta(y+1). Induction uses only internal adjacent factors, as required by the
implementation. This sharpens the previous upper bound; it does not extend
weak agreement beyond that endpoint or prove the new packet targets covered.
Packet semantics/history closure, I2/root, linedness, application and order
remain open.
Verified: build 1195 jobs; audit 695 declarations, no sorryAx.

## 2026-09-10: actual completion record exact certificate

CompletionExactCertificate.lean extracts the computed trace and terminal
record together with a natural cutoff exactly theta(y+1) and the owner's weak
agreement there. It uses the successful completionRecord guard and unsaturated
row semantics, without historyValid. It does not prove agreement beyond this
cutoff or visibility of newly inserted packet targets. Packet geometry and
semantics, history closure, I2/root, linedness, application and order remain.
Verified: build 1196 jobs; audit 696 declarations, no sorryAx.

## 2026-09-10: original historical cutoff survives native reindexing

Rechecked manuscript lines 132-135: packet coverage uses saved entrance Delta,
not the current lowered natural cutoff. NativeHistoricalAgreement.lean proves
actual native embedding reindexing preserves the original weak agreement at
exactly that Delta, for both owner and word. No cutoff lowering or successor
column premise is required. Historical invariant propagation through completion
and packet target coverage remain open, as do I2/root, linedness, application
and final order.
Verified: build 1197 jobs; audit 697 declarations, no sorryAx.

## 2026-09-10: historical target coverage through native insertion

NativeHistoricalCoverage.lean proves every concrete inserted target lies
strictly below any historical cutoff at/above the old successor column, and
that shifted old targets keep their strict coverage. The former derives the
strict inequality from actual source-image bounds. The historical cutoff
premise must still be maintained for the intended packet through scan events;
this is not whole-packet/history closure. I2/root, linedness, application,
completion semantics and final order remain open.
Verified: build 1198 jobs; audit 699 declarations, no sorryAx.

## 2026-09-10: historical successor upper bound retained

NativeHistoricalSuccessor.lean proves the current successor of every shifted
old column remains at/below its historical cutoff whenever the old successor
was. The fresh-value premise is discharged from actual native image geometry.
This is a one-step bound, not a full scan invariant or packet theorem.
Completion/history closure, I2/root, linedness, application and final order
remain open.
Verified: build 1199 jobs; audit 700 declarations, no sorryAx.

## 2026-09-10: actual inserted edge transfer at historical cutoff

NativeHistoricalEdgeTransfer.lean derives every actual native insertion-rank
edge for another elementary embedding from historical weak agreement with the
native owner. Known source-image equations and strict target coverage are
discharged by the concrete native geometry. Agreement and the historical
successor upper bound remain explicit; no full completion packet is claimed.
Whole trace-word packet propagation, completion/history closure, I2/root,
linedness, application and final order remain open.
Verified: build 1200 jobs; audit 701 declarations, no sorryAx.

## 2026-09-10: whole-word terminal packet target coverage

WordPacketCoverage.lean proves strict monotonicity of actual word ordinal
actions and that prefix images of targets below the terminal successor lie
strictly below the natural cutoff of prefix ++ [terminal]. Concrete native
source images satisfy the required strict input bound. Identifying these
semantic values with actual completion target columns through scan history
remains open; this is not the full packet theorem. I2/root, linedness,
application, completion closure and final order remain open.
Verified: build 1201 jobs; audit 704 declarations, no sorryAx.

## 2026-09-10: terminal source-image edge read through whole word

WordPacketEdgeTransfer.lean derives owner(theta x) equal to the prefix-word
image of the actual terminal native source image from weak agreement with the
whole word at its natural cutoff. Known edges and strict coverage are derived,
not assumed separately. Still needed: identify these semantic targets with
actual completion columns using prior scan events and retained historical
certificates. Completion/history closure, I2/root, linedness, application and
final order remain open.
Verified: build 1202 jobs; audit 705 declarations, no sorryAx.

## 2026-09-10: actual direct packet target-row edge equations

DirectPacketRealizedEdges.lean derives actual source-to-target image equations
from the direct packet traces retained in ScanReach. Each equation uses the
embedding of its target row. Equality/appropriate agreement of these embeddings
with the recorded terminal owner still needs a semantic history invariant;
no such identification is assumed here. historyValid remains a premise.
Completion/history closure, I2/root, linedness, application and order remain.
Verified: build 1203 jobs; audit 707 declarations, no sorryAx.

## 2026-09-10: recorded block embedding invariant step

RecordedEmbeddingInvariant.lean defines common embeddings across each recorded
block and proves initialization plus preservation when appending a native
record to the right of all older blocks. The new block equality follows from
the concrete native interpretation; old block equality follows from prefix
preservation. Integration with actual ScanReach and the semantic evolution
through completion remains required. I2/root, linedness, application,
completion/history closure and final order remain open.
Verified: build 1204 jobs; audit 709 declarations, no sorryAx.

## 2026-09-10: actual scan embedding evolution and direct owner edges

RecordedEmbeddingScanStep handles the actual empty-source record update.
ScanEmbeddingReach tracks literal successful scan steps with concrete native
embedding updates. Every ScanReach lifts to this relation; forgetting it recovers
ScanReach. Recorded block embedding equality is proved for every such history.
ScanDirectOwnerEdges uses that derived invariant to identify target-row embeddings
with the recorded terminal embedding in actual direct completion packet edges.
This closes the embedding-identification gap for direct packets, but retains
historyValid and RankRowRealization premises. It does not yet prove completion
realization preservation, retained historical cutoff agreement for all words,
I2/root, linedness, copy/application, or the final order theorem.
Verified: complete build 1207 jobs; audit 714 theorem declarations, no sorryAx.

## 2026-09-10: retained record packets under arbitrary words

ScanRecordedWordPacket derives actual terminal-owner source/target equations
for every retained record, without requiring a current direct-mark lookup.
These equations propagate through arbitrary prefix words using the actual
composite elementary embedding. A transfer theorem reads the resulting packet
through a supplied historical weak agreement and strict target coverage.
ScanDirectOwnerEdges now specializes this general result instead of duplicating
its proof. The new theorems retain historyValid and current realization;
historical agreement/coverage and identification of word images with actual
completion columns are still open, as are I2/root, linedness, copy/application,
completion closure and the final well-order.
Verified: complete build 1208 jobs; audit 717 declarations, no sorryAx.

## 2026-09-10: concrete column history and retained birth cutoff

ScanRankReach tracks both concrete nativeFreshValues column insertion and
native row-embedding updates along literal successful scan steps. Every
ScanReach admits such a lift, which forgets to ScanEmbeddingReach.
Every retained record has a witnessed native birth event; its present target
values equal the concrete fresh values at that event, and the terminal
embedding equals its birth embedding. This historical identification uses no
historyValid or realization premise.
ScanRecordHistoricalCoverage derives strict coverage of all retained terminal
targets by that witnessed birth successor, assuming realization at native
entrances. That entrance invariant remains unproved; this does not close
completion validity or whole-word historical agreement and target identification.
I2/root, linedness, copy/application and final well-order remain open.
Verified: complete build 1210 jobs; audit 721 declarations, no sorryAx.

## 2026-09-10: record edges from concrete births with reduced assumptions

Strengthened scanRankReach_record_birth to preserve every column at or below
the terminal, not only the inserted target columns and owner embedding.
ScanBirthPacketEdges now derives retained terminal edges and arbitrary word
images directly from the native birth assignment plus source-index bounds.
These equations require neither current RankRowRealization nor historyValid.
Source bounds follow from core validity at native entrances, separately proved.
Adjusted historical coverage to the stronger birth witness. Entrance validity,
completion target identification, historical word agreement, I2/root, linedness,
copy/application and the final well-order remain open.
Verified: complete build 1211 jobs; audit 724 declarations, no sorryAx.

## 2026-09-10: strictly prior entrance scope and whole-word birth bound

Restricted entrance assumptions in scanRankReach_record_source_bounds and
scanRankReach_record_historical_coverage to owners strictly before the current
cursor. The proof obtains this strict inequality from actual record history;
no current/future entrance is used by these lemmas.
ScanWordBirthPacket combines actual record-word edge equations with strict
coverage by the current prefix-word image of the witnessed birth successor.
This bound is not yet identified with a saved entrance natural cutoff, and no
weak agreement at that bound is claimed. Actual completion-column identification,
entrance realization induction, I2/root, linedness, copy/application and the
final well-order remain open.
Verified: complete build 1212 jobs; audit 725 declarations, no sorryAx.

## 2026-09-10: original tail semantics and located birth successors

ScanOriginalTail proves that every concrete scan history has an original-row
cursor determined by initial/current lengths; all unscanned tail column values
and embeddings equal their original assignments. No validity premise is used.
For each record it identifies the birth successor with initialTheta(original+1)
and its owner embedding with initialEmbedding(original).
ScanOriginalCoverage locates a strict terminal packet upper bound in the original
sequence, assuming realization only at strictly earlier native entrances.
Whole-word factor reindexing, identification with the saved weak certificate,
actual completion targets, entrance closure, I2/root, linedness, copy/application
and final order remain open.
Verified: complete build 1214 jobs; audit 728 declarations, no sorryAx.

## 2026-09-10: coherent original map and entry certificate transport

ScanOriginalMap constructs one strictly increasing map fixing zero through all
actual native insertions of a ScanRankReach history. It preserves all original
ordinal column values and owner embeddings simultaneously. Under that same map,
every entry weak certificate transfers at its unchanged historical cutoff.
These theorems require no realization or historyValid premise. They do not yet
identify current computed traces or newly created completion marks with mapped
entry words; that identification and the geometric completion closure remain.
I2/root, linedness, copy/application and final order also remain open.
Verified: complete build 1215 jobs; audit 730 declarations, no sorryAx.

## 2026-09-10: one origin map aligns records and entry certificates

ScanOriginAlignment strengthens the whole-scan invariant: one increasing map
fixing zero preserves all original semantic assignments, aligns the original
cursor with the entire unscanned tail, and represents every recorded terminal
as a strictly earlier original row. No validity assumption is used.
Original-map and original-tail theorems now specialize this common proof.
Strengthened entry certificate transport to include recorded-terminal alignment
under the very same map, avoiding unrelated existential witnesses.
Current computed trace identification, packet/completion geometry, entrance
closure, I2/root, linedness, copy/application and final order remain open.
Verified: complete build 1216 jobs; audit 731 declarations, no sorryAx.

## 2026-09-10: exact record gaps and original natural-cutoff packet transfer

Strengthened origin alignment: every record at terminal is phi(i), and the
next original column is exactly phi(i+1)=terminal+sources.length+1. The proof
tracks block boundaries through later native insertions without validity.
ScanEntryPacketCoverage uses these exact gaps and current increasing columns
to prove strict coverage of every mapped-prefix packet target by the ORIGINAL
entry natural cutoff. It no longer assumes historical entrance realizations.
ScanEntryPacketTransfer combines this coverage, concrete birth edges and entry
weak agreement to read all packet edges for the mapped owner. Its remaining
premises are current monotonicity, the entry certificate, and source-index bounds.
It does not identify current computed traces with mapped entry words or the
word-image targets with actual completion columns. Those geometric obligations,
entrance closure, I2/root, linedness, copy/application and final order remain.
Verified: complete build 1218 jobs; audit 733 declarations, no sorryAx.

## 2026-09-10: predecessor transport within the same origin map

ScanPriorGeometry names the still-open local obligations: strictly prior
frozen completions preserve predecessors and have core-valid native entrances.
The origin alignment induction now proves predecessor transport conditionally
on these obligations, under its SAME map as semantic and record-gap alignment.
ScanEntryTraceIdentification derives exact transported Trace and uniqueness of
successful traceFuel output at mapped source/head endpoints. This does not yet
show actual marked source positions are those mapped endpoints, nor discharge
ScanPriorGeometry; completion interval geometry remains the central obligation.
Updated all consumers and rebuilt. I2/root, linedness, copy/application,
completion closure and final order remain open.
Verified: complete build 1220 jobs; audit 735 declarations, no sorryAx.

## 2026-09-10: semantic packet edges imply completion core and p closure

CompletionSemanticPosition proves full-row sorting, target-position >= p, and
that an actual edge landing below the owner has source strictly below p.
CompletionSemanticCore combines actual packet edge equations in one adjacent
old target gap with strict-before-owner bounds. It derives source gaps, source
and target disjointness, completed CoreValid and unchanged p; those facts are
no longer separate assumptions in this local theorem. Source index bounds,
nodup, actual target-gap positioning and packet image equations remain explicit.
Connecting those hypotheses to actual scan events, complete old-edge/mark
closure, I2/root, linedness, copy/application and final well-order remain open.
Verified: complete build 1222 jobs; audit 739 declarations, no sorryAx.

## 2026-09-10: semantic old-edge intervals and endpoint positions

CompletionSemanticIntervals derives the earlier/later insertion interval cases
for every old core-to-core edge from actual packet images, column monotonicity,
p<=y, source bounds and target-gap exclusion. These cases yield exact positions
for both endpoints separated by the new step. The implicit final edge is also
retained by a separate exact-index theorem under e<=y and sources<e.
These results prove old-edge retention; a classification exhausting every new
full-row edge is still required. Actual event gap/image hypotheses and complete
mark/realization closure remain open, together with I2/root, linedness,
copy/application and final well-order.
Verified: complete build 1223 jobs; audit 742 declarations, no sorryAx.

## 2026-09-10: complete local full-row edge realization

FullRowEdgeSources proves all edge sources lie in the core at/below e, and
conversely every core value at/below e is an old full-edge source.
CompletionEdgeExhaustion proves retained old pairs plus inserted source pairs
exhaust ALL completed full-row edges, including the implicit endpoint.
CompletionAllRealizedEdges instantiates this classification using the semantic
interval proofs, exact old-pair positions and inserted-pair geometry. Its final
conclusion is actual RealizesEdges for the entire completed row. Required local
hypotheses remain current realization, e<=y, a genuine adjacent old target gap,
nodup/source bounds and actual packet equations at the completion targets.
Deriving those from actual scan events, complete mark certificates/properness,
I2/root, linedness, copy/application and final well-order remain open.
Verified: complete build 1226 jobs; audit 746 declarations, no sorryAx.

## 2026-09-10: local proper marks, critical point and all old certificates

CompletionPacketGeometry extracts the shared source-gap, disjointness, target
exclusion and source-below-p consequences from actual packet edges. Refactored
core/p closure and all-edge realization to reuse this proof.
CompletionSemanticMarks derives ProperMarks, preservation of the original
minimum/critical point, and every old marked certificate with its exact word
and natural cutoff under the same local packet/gap hypotheses, without
historyValid. Semantic interval cases for old certificates are now discharged.
New marks' actual parallel traces and natural weak certificates remain open,
as do derivation of event packet/gap hypotheses, I2/root, linedness,
copy/application and final well-order.
Verified: complete build 1228 jobs; audit 749 declarations, no sorryAx.

## 2026-09-10: parallel factor bounds and natural certificates

ScanParallelCertificates uses the SAME origin map and exact record-block gaps
to derive factor-embedding equality and successor-column upper bounds at any
recorded offset. A parallel word whose every factor has the required block
incidence inherits the entry weak certificate at its own defined natural
cutoff, with newDelta<=entryDelta. Current column monotonicity is used;
historyValid and entrance realization are not assumed.
Actual new traces having these block incidences and the indicated parallel
word remain obligations of the concrete packet theorem. Actual event target
gaps/images, scan closure, I2/root, linedness, copy/application and final
well-order remain open.
Verified: complete build 1229 jobs; audit 751 declarations, no sorryAx.

## 2026-09-10: concrete packet probe and short-block target B chain

CheckParallelPackets inspects literal frozen-mark events, verifies required
factor record lengths and exact offset parallel traces whenever completion
fires. Depth 14 with E(1), E(2), cut and M_star finished: 9619 distinct states,
1850 direct events, ZERO longer-word events. Thus the passing probe provides
NO validation of the general longer-word incidence hypothesis. Full proof
scope is unchanged. The complete output is parallel-packet-check.txt.
NativeTargetBChain proves every short-descent block row retains its initial
consecutive target segment; positive-index rows consequently have literal
B=previous target. This is groundwork for deriving block incidences rather
than assuming them. Medium-first descent and whole-scan B persistence remain.
General packet/event closure, I2/root, linedness, copy/application and final
well-order remain open.
Verified: complete build 1230 jobs; audit 753 declarations, no sorryAx.

## 2026-09-10: actual recorded target B chains through the whole scan

NativeMediumTargetBChain handles medium-first descent and derives its target
segment/B equations. NativeActualTargetBChain discharges the branch hypotheses
for actual native blocks. NativeOutputTargetB places these B equations in the
literal output pattern. ScanRecordedTargetB proves every retained record keeps
B(terminal+k)=terminal+k-1 for all 0<k<=sources.length through subsequent scan
steps. Its validity premise is restricted to strictly prior native entrances.
These are actual combinatorial chains, groundwork for deriving general packet
incidence from source walks; that derivation is not yet complete. Event closure,
I2/root, linedness, copy/application and final well-order remain open.
Verified: complete build 1234 jobs; audit 758 declarations, no sorryAx.

## 2026-09-10: B-walk closure and recorded target-segment inclusion

NativeWalkTargetSegment proves successful walks are closed under every emitted
source's above-threshold B successor. Once a walk emits base+top in a consecutive
B block and its threshold is <=base, it contains all base+k for 0<k<=top and
has length at least top. The result is specialized to actual retained records
using scanReach_record_target_b, with strictly prior entrance validity only.
Proving that the relevant walk enters the required segment, and its exact
source ranks, remains necessary for general parallel packet incidence. Event
closure, I2/root, linedness, copy/application and final well-order remain open.
Verified: complete build 1235 jobs; audit 763 declarations, no sorryAx.

### 2026-09-10: exact target ranks and actual native parallel edges
- Added NativeTargetSourceRank: successful sources are above the threshold; a complete lowest consecutive segment has rank k - 1; entering a consecutive B segment at threshold base establishes this exact rank.
- Added NativeTargetParallelEdge: for an actual successful native operation whose predecessor is base, entering base + top in the sources and a consecutive B chain imply predecessor(output, r + k) = base + k for every positive k <= top. The corresponding literal two-point Trace is proved.
- These are conditional local geometry results. Actual-event entry/threshold alignment and the complete parallel-word/new-certificate closure remain open; no claim of the main well-order theorem.
- Verification: lake build passed (1237 jobs); Audit.lean passed (768 theorem declarations), no sorryAx or errors.

### 2026-09-10: recorded target blocks at actual scan entrances
- Added ScanRecordParallelEdge. The retained record supplies the consecutive B-chain after completeFrozenMarks: every recorded target lies strictly before the cursor, so completion preserves its row.
- scan_step_record_parallel_predecessor and scan_step_record_parallel_trace specialize the native parallel result to actual scan steps without an independent B-chain hypothesis.
- Remaining hypotheses are explicit: prior/current entrance core validity, current predecessor equal to the record terminal, and entry into a bounded positive target segment. Establishing these for all required actual events and composing the full parallel word remain open.
- Verification: full lake build passed (1238 jobs); 770 theorem declarations audited with no sorryAx or errors. Main goal remains open.

### 2026-09-10: target entry from the B-walk starting point
- NativeTargetEntry proves entry from an actual starting B edge, rather than assumed source membership.
- A successful walk with threshold base starting at base + top + 1 over a consecutive B segment has exactly top sources. The upper bound uses actual native walk bounds and distinctness; the lower bound uses forced entry and segment closure. The zero-length case is included.
- Scope: this does not yet prove that every required actual scan event has the specified starting point or threshold. Full parallel-word and new-certificate obligations remain open.
- Validation: lake build passed (1239 jobs); 772 theorem declarations audited, no sorryAx or errors.

### 2026-09-10: actual native endpoint packet
- Added NativeEndpointPacket: extract actual sources from successful native; derive a fuel walk from eligibility and p/e without assuming sources nonempty.
- native_endpoint_parallel_packet proves exact source length and every offset predecessor/two-point trace from p = base, e = base + top + 1 and consecutive B geometry. This removes assumed entry/source membership from this local packet interface, including the top = 0 case.
- Rechecked manuscript section 3: the outstanding general obligation remains deriving the relevant historical endpoint geometry from Sat_rec and prior verified events, then full parallel-word identification and new certificates. This conditional endpoint packet is not the full manuscript packet theorem.
- Verification: 1240 build jobs passed; 775 theorem declarations audited, no sorryAx or errors. Main well-order goal remains open.

### 2026-09-10: widened parallel-packet exploration (running)
- Rechecked Sat definition and copied endpoint witnesses. Sat provides B(e) <= p; it does not directly establish the consecutive endpoint hypotheses of NativeEndpointPacket. Deriving the actual historical geometry remains essential.
- Added CheckParallelPacketsWide.lean exploring cut, E(1)..E(4), and M_star to depth 10, to seek longer-word completion events absent in the previous E(1)/E(2) bounded exploration.
- Started the finite probe; unified execution session 90176 remains live at the last poll, with no output delivered yet. Resume this same session; do not restart based on an observation timeout. Output destination: parallel-packet-wide-check.txt.
- No new theorem/build claim this turn. Last verified baseline remains 1240 build jobs and 775 audited declarations. The finite probe is diagnostic, not a general proof.

### 2026-09-10: prior-only recorded source predecessors
- Added ScanRecordedPredecessorPrior: retained source p edges are proved using core validity only at entrances strictly before the current cursor. No validity of the current or future completion is assumed.
- This removes the unbounded historyValid requirement for this edge interface and makes it suitable for the manuscript's prior-event induction.
- Build passed (1241 jobs); 776 theorem declarations audited with no sorryAx or errors.
- Wider finite probe session 90176 was polled again and remains live, without output yet; process inspection confirmed a live Lean process consuming CPU. Continue the same handle. General packet geometry and the main theorem remain open.

### 2026-09-10: prior-only source bounds and literal record traces
- Extended ScanRecordedPredecessorPrior with scanReach_record_sources_below_prior and scanReach_record_trace_prior. Both use only entrance validity strictly before the current cursor; the trace proof does not assume current pattern validity.
- Removed redundant native_success_sources from NativeEndpointPacket and reused existing native_sources_of_success.
- Full build passed (1241 jobs); audit passed (777 declarations), no sorryAx or errors.
- Wide diagnostic session 90176 remains live at this turn's poll, with no output delivered. Resume the same process. Actual general packet closure and main well-order proof remain open.

### 2026-09-10: reduced hypotheses integrated into semantic packet transfer
- Updated the existing scan_record_owner_edges, scan_record_word_edges, and scan_record_word_packet_transfer to require validity only at entrances strictly before r. Their proofs now use scanReach_record_trace_prior.
- Adapted the existing direct-owner caller to the weaker interface; no duplicate semantic theorem was added. Birth-based ScanRankReach interfaces remain available and require no current realization.
- Full build passed (1241 jobs). Existing 777-declaration audit passed with no sorryAx or errors.
- Wide exploration session 90176 remains live at the last poll, no returned output. Resume that handle. General actual parallel-word geometry and final main theorem remain open.

### 2026-09-10: direct completion packet from birth semantics
- scan_completion_direct_owner_edges now takes only strictly prior entrance validity.
- Added scanRankReach_completion_direct_edges: actual direct completion record supplies semantic edges from recorded birth values, deriving source bounds from strictly prior entrances. It assumes no current RankRowRealization.
- This addresses the direct packet's semantic edge obligation; local geometry, newly marked certificates, and general longer words remain separate open obligations.
- Build passed (1241 jobs); audit passed (778 declarations), no sorryAx or errors.
- Wide diagnostic session 90176 is still live at the last poll; Lean PID 17964 CPU increased to 399.25 seconds. No output delivered yet; do not restart on that basis.

### 2026-09-10: frozen-prefix recorded traces and completed wide probe
- Added scanReach_record_trace_frozen_prefix: every retained direct source trace remains literal during any prefix of the current completion fold. It uses strictly prior entrance validity, not current completion correctness.
- Build passed (1241 jobs); 779 theorem declarations audited, no sorryAx or errors.
- Wide probe session 90176 COMPLETED with exit 0: depth 10, E(1)..E(4), cut and M_star, 14250 states, 683 direct completion events, 0 longer events. All inspected packet-shape checks passed. Output: parallel-packet-wide-check.txt. No live probe remains; do not poll/restart the completed handle.
- The wide sample still provides no longer-word evidence. Main general parallel geometry/new certificates and well-order goal remain open.

### 2026-09-10: semantic geometry yields new marked source positions
- Added rankRealization_completion_new_markTrace in CompletionSemanticMarks. From the same semantic packet/gap assumptions used for all-edge preservation, derive source-gap geometry and obtain each new actual MarkTrace from its parallel Trace.
- No independent inserted source-position or source-gap hypothesis is required. The general parallel Trace itself remains an explicit open input; this does not finish new natural-cutoff certificates.
- Full build passed (1241 jobs); 780 theorem declarations audited with no sorryAx or errors. No live diagnostic process remains. Main goal remains open.

### 2026-09-10: actual direct completion new marked traces
- Added ScanDirectNewMarkTrace. From successful actual direct completion, derive recorded parallel two-point Trace, source distinctness, source bounds, and target-before-owner bound; then apply semantic geometry to identify the actual new MarkTrace.
- Remaining explicit hypotheses include current row realization, current owner packet edges, and the next-target gap. These are not silently assumed discharged; natural-cutoff certificates and general longer-word closure remain open.
- Full build passed (1242 jobs); 781 theorem declarations audited, no sorryAx or errors. No running process. Main goal remains open.

### 2026-09-10: direct recorded factor natural cutoff
- Added scan_record_direct_natural_certificate in ScanDirectOwnerEdges. Actual record embedding agreement supplies the shifted direct factor; saved weak agreement restricts to its exact natural cutoff theta(y + offset + 1).
- Explicit remaining inputs are saved agreement and coverage of this successor by the saved delta. No current-cutoff coverage or current realization is assumed. This local certificate still needs integration with the direct new MarkTrace and historical coverage for actual events.
- Full build passed (1242 jobs); 782 theorem declarations audited, no sorryAx or errors. Main well-order goal remains open.

### 2026-09-10: direct new certificate assembled
- Added ScanDirectNewCertificate: actual direct completion yields an existential marked certificate containing the literal two-point MarkTrace, its exact natural cutoff, cutoff <= saved delta, and weak agreement there.
- Combined actual-record trace geometry with recorded-factor natural-cutoff restriction. Explicit local inputs remain current realization, owner packet, next-target gap, saved agreement, and successor coverage. General event closure is not claimed.
- Full build passed (1243 jobs); 783 theorem declarations audited, no sorryAx or errors. No live processes. Main goal remains open.

### 2026-09-10: direct certificate derives owner packet
- Strengthened scan_completion_direct_new_certificate by removing its standalone owner packet assumption. Recorded direct owner edges transfer through saved weak agreement; monotonicity and coverage of every target successor provide strict target visibility.
- The interface now explicitly requires delta <= lambda and successor coverage for all sources (needed to derive the whole packet geometry). Current realization, next-target gap, saved agreement, and historical coverage remain inputs.
- Full build passed (1243 jobs); unchanged 783-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: direct certificate coverage reduced to one endpoint
- scan_completion_direct_new_certificate now requires only theta(y + sources.length + 1) <= saved delta, replacing the per-source successor coverage family.
- Record target bounds and current increasing columns prove every source-ranked target successor lies below this endpoint; equality at the maximum rank is handled explicitly. The owner packet transfer and resulting new natural certificate use the derived family.
- Historical identification of this endpoint and saved agreement remain to be integrated; this change does not assert general event closure.
- Full build passed (1243 jobs); existing 783-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: coherent direct historical inputs
- Added ScanDirectHistoricalInputs. One origin map identifies every recorded endpoint successor's theta with its original successor theta, while transporting direct saved weak agreement using the same original index and owner map.
- Endpoint coverage and saved agreement are returned together from original certificate inputs, without current realization assumptions.
- Actual current owner/marked position alignment still needs to connect this origin witness to the direct completion theorem. General longer-word geometry and main well-order theorem remain open.
- Full build passed (1244 jobs); 784 theorem declarations audited, no sorryAx or errors.

### 2026-09-10: current owner aligned with direct historical records
- Added scanRankReach_current_direct_history: one original cursor witnesses the current embedding, and every record has an earlier original index identifying both its embedding and endpoint successor theta.
- A direct entry agreement at that original natural cutoff transports to the actual current owner and record terminal. No separately chosen owner map is needed.
- The actual marked-position/entry-certificate identification remains open; this theorem does not assert that all current marks have such an original direct certificate.
- Build passed (1244 jobs); 785 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: future marked traces across actual scan steps
- Added ScanFutureMarkTrace. Frozen completion preserves a different owner's marked source positions and trace under predecessor preservation; the subsequent actual native step transports the whole future MarkTrace by its insertion map.
- This covers marked source positions as well as bare trace endpoints, a necessary ingredient for coherent original-mark identification over the scan. The completion predecessor and entrance-validity hypotheses remain explicit.
- Full build passed (1245 jobs); 787 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: whole-scan forward marked origin transport
- Added ScanFutureMarkedOrigins. Induction over actual ScanRankReach constructs one strictly increasing semantic map, tracks the original cursor by length balance and the unscanned tail, and transports every entry MarkTrace whose owner is still unscanned.
- MarkTrace transport includes marked core/source positions and complete words, using only ScanPriorGeometry at prior events. This is forward transport, not a converse proving every current mark originates from a given entry mark.
- Full build passed (1246 jobs); 788 theorem declarations audited, no sorryAx or errors. General closure and main well-order goal remain open.

### 2026-09-10: exact future row structure in the marked origin map
- Strengthened scanRankReach_future_markTraces: the same phi now maps every unscanned original row's core and marks exactly, preserving step. This row-structure conjunct is unconditional; only trace transport requires prior geometry.
- The actual native suffix lookup and frozen completion's other-row preservation prove the induction step. This supplies the structural basis for recovering current mark membership from entry marks.
- Full build passed (1246 jobs); unchanged 788-declaration audit passed without sorryAx or errors. Reverse certificate identification and main goal remain open.

### 2026-09-10: current unprocessed mark membership recovered
- Added ScanCurrentMarkOrigins. For an actual current row, recover an existing entry row and original cursor, exact mapped row shape, and equivalence of current mark membership with mapped entry mark membership.
- The same phi preserves semantics and transports every entry MarkTrace at this owner under prior geometry. This concerns the current row before its frozen completion fold, not later intermediate marks.
- Build passed (1247 jobs); 789 theorem declarations audited, no sorryAx or errors. Computed word/certificate identification and general closure remain open.

### 2026-09-10: every current entry mark carries its historical certificate
- Added ScanCurrentHistoricalCertificates. Entry row realization plus prior scan geometry and an actual current row yield, for every current mark, an exact mapped MarkTrace and weak agreement at the original natural cutoff.
- One phi is shared across all marks. The certificate word is the mapped original factor word; no claim equates current and historical cutoffs.
- Computing the current word and propagation through intermediate frozen completions remain to be connected.
- Build passed (1248 jobs); 790 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: actual successful computed words identified
- Added computeMarkTrace_identify requiring only owner-core sortedness, not whole-pattern validity. Source index uniqueness and trace uniqueness identify any successful computed word with an existing MarkTrace.
- Strengthened scanRankReach_current_historical_certificates to identify each successful computeMarkTrace output as the mapped entry word. Current owner sortedness is derived from exact mapped entry row structure.
- This identifies successful output; it does not assert totality for every computation or closure through current frozen completions.
- Full build passed (1249 jobs); 791 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: current entry marked trace computation is total
- Added computeMarkTrace_complete_of_length, needing only owner-core sortedness and a length bound on a known MarkTrace.
- Strengthened scanRankReach_current_historical_certificates from conditional output identification to computeMarkTrace = some(mapped entry word). Entry validity bounds original trace length, and the strictly increasing Nat map is extensive, so the mapped word fits the actual y + 1 budget.
- No current whole-pattern validity assumption was added. Prior geometry and entry realization remain explicit; intermediate frozen-event closure is still open.
- Full build passed (1249 jobs); 792 theorem declarations audited without sorryAx or errors. Main goal remains open.

### 2026-09-10: arbitrary historical marked words survive semantic completion
- Added rankRealization_completion_preserves_markTrace. It preserves any supplied old MarkTrace using derived semantic intervals, rather than selecting the word supplied by the current realization's marked field.
- This permits carrying entry historical words unchanged through locally verified completion steps. Full frozen-fold closure still requires establishing those local packet/gap conditions at each event.
- Full build passed (1249 jobs); 793 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: actual completeMark historical trace preservation
- Added CompleteMarkHistoricalTrace. The literal completeMark operation preserves an arbitrary supplied old MarkTrace, handling absent records by identity and successful records through explicit local semantic witnesses.
- The theorem retains current realization and successful-event packet/gap obligations; it does not assume the desired preservation result as an input. Establishing these obligations for the whole frozen sequence remains open.
- Full build passed (1250 jobs); 794 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: frozen historical trace fold composition
- Added FrozenHistoricalTrace with CompletionEventGeometry explicitly grouping current realization and successful-record packet/gap witnesses (no preservation theorem is a field).
- frozen_fold_preserves_historical_trace composes actual completeMark steps over any frozen list, using obligations at precisely its processed-prefix states.
- This is a conditional composition result, not establishment of all event obligations. General packet geometry/new certificates and main well-order remain open.
- Full build passed (1251 jobs); 795 theorem declarations audited, no sorryAx or errors.

### 2026-09-10: frozen predecessor preservation from event geometry
- Added FrozenPredecessorGeometry. CompletionEventGeometry implies all predecessors are unchanged by actual completeMark, including absent-row/absent-record branches.
- Composed this preservation across a frozen list using the precise actual prefix states. This discharges the predecessor component once local event obligations are proved; it does not establish their semantic packet/gap inputs.
- Full build passed (1252 jobs); 797 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: actual frozen completion supplies scan geometry
- Added completionEvent_coreValid and frozen_fold_coreValid using local semantic core preservation and unchanged other rows.
- completeFrozenMarks_event_geometry combines actual output core validity and all-predecessor preservation for the frozen list row.marks. Input initial core validity handles the empty-list case; events supply semantic geometry at each actual processed state.
- These are conditional deductions, not proofs that all required actual events satisfy the local semantic/gap obligations.
- Full build passed (1252 jobs); 800 theorem declarations audited without sorryAx or errors. Main goal remains open.

### 2026-09-10: prior event conditions imply ScanPriorGeometry
- Added ScanPriorEventGeometry. Prior row core validity plus actual frozen-prefix CompletionEventGeometry implies the exact ScanPriorGeometry predicate used by historical word/mark transport.
- The range remains strictly owner < cursor. Absent-owner rows use identity completion. Current/future events are not included.
- Initial build failed on a simplifier-reduced True goal; fixed explicitly and rebuilt successfully (1253 jobs). 801 theorem declarations audited, no sorryAx or errors.
- The event packet/gap hypotheses themselves remain open; the main goal is not complete.

### 2026-09-10: record alignment unified with marked certificate map
- Strengthened scanRankReach_future_markTraces with exact record start/successor alignment under its same phi, proved through the scan induction.
- Propagated this conjunct through ScanCurrentMarkOrigins and ScanCurrentHistoricalCertificates. The map identifying actual computed marked words now also identifies every record's original factor and successor gap.
- This removes the need to select unrelated existential origin maps for packet/certificate alignment. Actual general event geometry remains unproved.
- Full build passed (1253 jobs); existing 801-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: direct actual endpoint agreement derived from entry certificate
- Exposed semantic holds in ScanCurrentHistoricalCertificates alongside its record-aligned map.
- Added scanRankReach_direct_endpoint_agreement. An actual computed two-point word and successful completion record identify an original two-point word; injectivity identifies its factor with the record's original index. Its original natural cutoff equals theta(y + sources.length + 1).
- Therefore saved agreement at that endpoint is derived, without separate saved-agreement/coverage inputs. Assumptions remain entry realization and prior geometry; this concerns the current unprocessed row, not arbitrary intermediate frozen events.
- Full build passed (1254 jobs); 802 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: direct new certificate consumes derived historical agreement
- Added scanRankReach_direct_new_certificate. Actual direct entrance completion uses entry realization and prior geometry to derive saved endpoint agreement, then constructs its new marked certificate without independent saved-agreement or coverage inputs.
- Prior unlabelled ScanReach validity is obtained by lifting to ScanRankReach and applying the same prior geometry. Current realization and next-target gap remain explicit; intermediate frozen states/general words remain open.
- Full build passed (1254 jobs); 803 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: actual current record target gap proved
- Added ScanCurrentRecordGap. Exact mapped core entries and record successor alignment show every later full-row entry is beyond all recorded targets; the owner-successor case follows from record-before-cursor bounds.
- Removed the gap input from scanRankReach_direct_new_certificate, deriving it from adjacent sorted full-row positions. The direct entrance certificate no longer separately assumes packet, saved agreement, coverage, or target gap.
- Entry realization, current realization, prior geometry, actual direct completion and the supplied p/target positions remain. Intermediate frozen events/general words and main well-order remain open.
- Full build passed (1255 jobs); 804 theorem declarations audited without sorryAx or errors.

### 2026-09-10: direct new certificate derives positional witnesses
- Removed p, step-target index, and next-target lookup inputs from scanRankReach_direct_new_certificate. Current core validity and proper marks supply p and the marked position; the full-row successor supplies the next target.
- The resulting entrance theorem needs actual current row/mark, direct computation, successful record/source membership, entry and current realization, and prior geometry. Packet, gap, saved cutoff/coverage, and positional witnesses are all derived.
- Full build passed (1255 jobs); unchanged 804-declaration audit passed without sorryAx or errors. Intermediate frozen events, general words and main goal remain open.

### 2026-09-10: direct owner packet without current realization
- Added ScanDirectOwnerPacket. Actual direct entrance completion yields every current-owner packet edge using birth record edges, entry historical agreement, and increasing current columns.
- No current RankRowRealization is assumed by this packet theorem. Entry realization, prior geometry, current increasing columns, and actual row/mark/computation/record witnesses remain.
- Full build passed (1256 jobs); 805 theorem declarations audited, no sorryAx or errors. General intermediate events and main well-order remain open.

### 2026-09-10: direct entrance event geometry discharged
- Added scanRankReach_direct_event_geometry. For an actual current marked two-point word, derive CompletionEventGeometry from entry/current realization and prior geometry.
- All successful-record witnesses (p and target positions, nodup, source bounds, target gap, target-before-owner, current-owner packet) are derived. No record success need be assumed in the theorem: its event condition handles each successful record.
- Applies at the unprocessed current scan entrance, not arbitrary intermediate frozen states or longer words. Full closure/main well-order remain open.
- Full build passed (1257 jobs); 806 theorem declarations audited, no sorryAx or errors.

### 2026-09-10: actual all-edge preservation and explicit long-row boundary
- Added CompletionEventEdges: actual completeMark preserves all row edges from CompletionEventGeometry plus the successful event's e <= y endpoint witness. Other rows are unchanged.
- Audit of the all-edge interface confirms e <= y is an additional requirement, absent from CompletionEventGeometry. Eligible short/medium rows have eligible_source_le_mark; long rows require the manuscript critical-point/earliest-mark exclusion argument. Do not claim full realization closure from event geometry alone.
- Full build passed (1258 jobs); 807 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: eligible event all-edge endpoint discharged
- Added completionEvent_eligible_all_edges: row core validity supplies e and proper marked position on a short/medium row supplies e <= y. Actual completeMark all-edge preservation then needs no independent endpoint witness in this case.
- Long rows are not covered by the eligibility premise; their earliest-mark/critical-point exclusion remains an explicit open requirement for full closure.
- Full build passed (1258 jobs); 808 theorem declarations audited, no sorryAx or errors. Main goal remains open.

### 2026-09-10: correction and reachable all-row endpoint integration (verification pending)
- Correction to the two previous entries: CompletionTargetBound already proved the long-row endpoint exclusion from critical-point semantics. The missing step was integration and weakening history assumptions, not the mathematical exclusion argument itself.
- Weakened NativeRecordedMinimum and CompletionTargetBound to require validity only for owners strictly before the current cursor. NativeRecordedMinimum passed standalone checking before the dependency rebuild.
- Added completionEvent_reachable_all_edges, deriving endpoint witnesses for every ordinary row from actual ScanReach, current event geometry and strictly prior validity. No short/medium eligibility premise remains.
- Verification pending: the existing full build is still running; an early standalone check encountered an as-yet-unbuilt RankOrderedPair dependency. This is not a successful check of the new theorem. Main goal remains open.

### 2026-09-10: reachable all-row and actual direct edge preservation verified
- completionEvent_reachable_all_edges now derives the endpoint condition for all ordinary rows, including long rows, from actual reachability and strictly prior validity.
- Added scanRankReach_direct_all_edges, obtaining that conclusion at an actual direct scan entrance from entry/current realization and prior geometry; no independent endpoint, packet, positional or eligibility assumptions.
- Full dependency rebuild passed (1258 jobs), including both edited event modules and the weakened historical-minimum chain. Regenerated audit covers 810 theorem declarations and passed with no sorryAx or errors.
- This supersedes the pending verification entry. Complete intermediate frozen-state/longer-word realization closure, root/copy semantics and final well-order remain open.

### 2026-09-10: intermediate frozen endpoint exclusion and all-edge preservation
- Extracted realized_completion_source_above_minimum_of_records: the critical-point argument needs the record-minimum invariant, not reachability of the current state itself. Existing entrance theorem now derives that invariant and applies the shared argument.
- Added scanReach_record_minimum_frozen_prefix. Arbitrary current-owner completion lists leave historical record rows unchanged; their strict minimum-to-predecessor inequality survives without any current event assumptions.
- Added realized_completion_source_above_minimum_frozen_prefix and completionEvent_frozen_prefix_all_edges. At an intermediate state, current realization/event geometry and actual marked membership discharge the long-row endpoint obligation. No artificial ScanReach assumption for the intermediate state is used.
- NativeRecordedMinimum and CompletionEventEdges both passed standalone Lean checks. Full rebuild is running (session 26374); regenerated Audit.lean now lists 814 declarations, but its new audit has not yet run. Main goal remains open; general event geometry and full realization closure are still required.

### 2026-09-10: actual direct owner certificates assembled (pending verification)
- Added source file ScanDirectAllCertificates.lean. The intended theorem quantifies over every mark of the actual completeMark output owner row, splitting retained old marks and inserted target marks. It uses the existing old-certificate theorem and actual direct new-certificate theorem, deriving the inserted source from its target rank.
- This module is NOT yet imported by FullMarkedBLP.lean and is NOT yet verified. The standalone check stopped at an unavailable NativeActualBlockCertificates dependency while the existing rebuild was still running; it did not check the proof body.
- Build session 26374 remains live and advancing (latest observed 1167/1258). Continue that same session, then check the new file, fix any proof errors, add its root import, rebuild and regenerate/run the full audit. Do not count this pending source as a verified theorem.

### 2026-09-10: complete direct entrance realization assembled (pending verification)
- Added ScanDirectRealization.lean source, assembling all RankRowRealization fields after actual direct entrance completion. It uses all-owner-mark certificates, all edges, core validity, proper marks and critical-point preservation; other-row marked traces are transported through predecessor preservation.
- Both ScanDirectAllCertificates and ScanDirectRealization remain unverified and outside the root import. They must be checked and fixed before being counted as results.
- Existing build session 26374 is confirmed live and advancing (latest observed 1205/1258). Do not restart it. After it completes: verify ScanDirectAllCertificates, build its olean, verify ScanDirectRealization, add root imports, build and run regenerated axiom audit. The previous 814-declaration audit is also still pending.

### 2026-09-10: direct entrance full row realization verified
- Fixed the simplified Option equality in ScanDirectAllCertificates; the theorem now builds and covers every mark in the actual completed owner row.
- ScanDirectRealization passed standalone checking and is imported by the root. scanRankReach_direct_realization assembles all RankRowRealization fields after an actual two-point entrance completion, using entry/current realization and strictly prior geometry. It does not assume the output realization or separate packet/endpoint/new-certificate conclusions.
- The preceding frozen-prefix record-minimum and all-edge changes also completed the dependency rebuild successfully. Both formerly pending new modules are now verified.
- Final full build passed (1260 jobs); regenerated 816-declaration axiom audit passed without sorryAx or errors.
- Main goal remains open. The result is one direct event at the unprocessed scan entrance; arbitrary intermediate-event geometry, longer words, global native/copy/root closure and final well-order are not established by it.

### 2026-09-10: frozen original direct mark endpoint agreement verified
- Added ScanFrozenDirectEndpoint. For an original row mark at an intermediate completion prefix, transported historical MarkTrace and the current sorted row identify a successful current two-point computation with its entrance computation. The direct completion-record condition is identical at the two states.
- Consequently scanRankReach_frozen_direct_endpoint_agreement derives saved agreement at theta(y + sources.length + 1), with no supplied historical cutoff or intermediate ScanReach. Assumptions: entry realization, prior scan geometry, geometry of processed events, original mark membership, and successful current direct computation/record; current row sortedness suffices for identification.
- Root import added. Full build passed (1261 jobs); regenerated 817-declaration audit passed without sorryAx or errors.
- General intermediate packet/gap geometry and longer words remain open; main goal remains open.

### 2026-09-10: frozen direct owner packet derived and verified
- Added ScanFrozenDirectPacket. At an original frozen mark with a successful intermediate two-point computation, derive all current-owner packet edges from recorded birth edges and transported endpoint agreement.
- No supplied packet, historical cutoff, or intermediate ScanReach; only original increasing columns and intermediate owner sortedness, entry realization, prior scan geometry, processed event geometry and the actual row/mark/computation/record witnesses remain.
- Full build passed (1262 jobs); regenerated 818-declaration audit passed without sorryAx or errors.
- Next geometric gap: show earlier frozen completions insert no columns above a later original mark, then transfer ScanCurrentRecordGap to the intermediate state. CompletionLaterMark.high_entry preserves original high entries but does not by itself exclude all new high columns. Longer-word and global closure remain open.

### 2026-09-10: high columns and intermediate record gap verified
- Added CompletionHighColumns. completionEvent_high_core_iff excludes all new columns at/above a later existing core column: semantic packet geometry gives sources below the event mark and target exclusion forces the target block below that later column.
- frozen_fold_high_core_iff composes this exact membership equivalence over any earlier processed marks with established event geometry.
- scanRankReach_frozen_record_gap transfers the actual entrance record gap to intermediate full-row entries, using the high-core equivalence and unchanged owner endpoint. No separate intermediate gap assumption.
- Root import added; full build passed (1263 jobs); regenerated 821-declaration axiom audit passed without sorryAx or errors.
- Next: combine intermediate packet + record gap + current realization into frozen direct CompletionEventGeometry, deriving original marked membership and earlier bounds from the actual sorted frozen list as needed. General longer-word and full global closure remain open.

### 2026-09-10: intermediate direct event geometry derived
- Added ScanFrozenDirectGeometry. For an original mark at an earlier-completed prefix, derive CompletionEventGeometry from entry realization, prior scan geometry, processed-event geometry, current realization, earlier-mark bounds and actual direct computation.
- Original core membership and current marked membership are derived from the historical certificate and transported MarkTrace. Packet, next-target gap, source bounds, nodup and positional witnesses are derived; no independent current event geometry is assumed.
- Full build passed (1264 jobs); regenerated 822-declaration axiom audit passed without sorryAx or errors.
- Remaining next steps: intermediate new marked certificates/full realization; discharge earlier bounds from sorted frozen-list decomposition; general longer-word packets and global closure. Main goal remains open.

### 2026-09-10: intermediate direct inserted-mark certificates verified
- Added ScanFrozenDirectCertificate. Every actual source in a successful intermediate direct event receives its new MarkTrace and natural-cutoff weak-agreement certificate.
- Derives the trace from historical recorded traces surviving arbitrary frozen prefixes, the new marked position from derived event geometry, and the cutoff agreement from the transported saved endpoint. Coverage follows from current increasing columns and record-before-owner bounds.
- No supplied packet, trace, saved cutoff, coverage or new-certificate premise. Entry realization, prior geometry, processed-event geometry, earlier bounds, current realization and actual original mark/current computation witnesses remain.
- Full build passed (1265 jobs); regenerated 823-declaration audit passed without sorryAx or errors. Next assemble all marked certificates and full intermediate direct realization. Main goal remains open.

### 2026-09-10: full intermediate direct realization verified
- Added ScanFrozenAllCertificates, covering every actual output owner mark by old/new certificate cases.
- Added ScanFrozenDirectRealization. Combines derived intermediate geometry and all certificates with core validity, all-edge preservation (including long rows), proper marks, critical points and unchanged-predecessor trace transport for other rows.
- No assumed output realization, independent current event geometry, packet, gap, endpoint or certificate. Entry realization, strictly prior scan geometry, processed-event geometry, current realization, earlier bounds and actual original marked/direct witnesses remain.
- Root import added. Full build passed (1267 jobs); regenerated 825-declaration audit passed without sorryAx or errors.
- Next: derive earlier bounds/original membership from sorted frozen decomposition and close the direct frozen fold by induction, without assuming all its event geometries in advance. Longer-word and global closure remain open; main goal remains open.

### 2026-09-10: actual sorted frozen step verified
- Added ScanFrozenDirectStep. Actual decomposition row.marks = processed ++ y :: remaining and pairwise strict sorting derive original mark membership and all earlier-mark bounds.
- Returns both the current direct CompletionEventGeometry and the output RankRowRealization, suitable for an accumulated-prefix induction. Prior processed event geometry still remains an input here; the entire fold has not yet been closed.
- Full build passed (1268 jobs); regenerated 826-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: direct frozen fold closed by accumulated induction
- Added FrozenPrefixInduction: prefix_events_snoc extends previously proved event evidence; frozen_prefix_bootstrap builds state invariants and event evidence together.
- scanRankReach_direct_frozen_fold now proves actual completeFrozenMarks row realization plus all intermediate event geometries from entry/current entrance realization, prior scan geometry and the explicit condition that each actual current marked computation is a two-point word.
- No intermediate realization or full-fold event-geometry assumptions remain. Actual row existence follows from length preservation; sorted earlier bounds come from the original proper marks.
- Full build passed (1269 jobs); regenerated 829-declaration audit passed without sorryAx or errors.
- This is the direct-word case only. The direct-computation hypothesis must not be silently assumed for general generated patterns. Longer-word completion packets and global root/copy/native closure and well-order remain open; main goal remains open.

### 2026-09-10: arbitrary-word frozen historical certificates verified
- Rechecked manuscript lines 129-135: longer-word packets require historical cutoff coverage and actual parallel packet geometry; the current natural cutoff cannot replace saved history.
- Added ScanFrozenHistoricalCertificates. Every original mark, with no word-length restriction, retains its exact mapped MarkTrace, successful computation and original-entry natural cutoff/weak agreement through a processed prefix. The same phi retains semantic holds and exact record endpoint alignment.
- Inputs are prior scan geometry, processed event geometry and current core validity; packet coverage/parallel identification are not claimed.
- Full build passed (1270 jobs); regenerated 830-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: same-map historical word coverage verified
- Found existing ScanEntryPacketCoverage already proves general mapped-front coverage, but chooses its own existential phi. Added ScanFrozenHistoricalCoverage to retain the exact phi used by actual frozen marked certificates.
- For every record this same map identifies its original terminal index and endpoint successor, and proves strict coverage of all record targets propagated through any mapped original front at that front's entry natural cutoff.
- Actual current computed-word/terminal decomposition must still be connected to this covered front, followed by identification with actual completion target columns and parallel traces. No claim of general packet geometry yet.
- Full build passed (1271 jobs); regenerated 831-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: actual general recorded word coverage connected
- Added RecordedWordDecomposition: fromRight_two_decomposition gives the exact final two entries; scanRankReach_frozen_recorded_word_coverage identifies the actual successful computation with its mapped historical word and aligns its terminal record by injectivity.
- Output is an actual front/terminal/final-source decomposition, its recordAt witness, saved owner agreement for front ++ [terminal], and strict historical coverage of every record target propagated through that same front. No word-length restriction.
- Full build passed (1272 jobs); regenerated 833-declaration audit passed without sorryAx or errors.
- Next: apply record birth word edges and saved coverage to obtain owner semantic packet values; identifying those values with actual inserted columns and proving full parallel traces still require the general packet geometry. Main goal remains open.

### 2026-09-10: actual general-word owner semantic edges verified
- Added ScanGeneralOwnerEdges. A successful arbitrary-length original-mark completion at a frozen prefix supplies its exact computed front/terminal/final-source decomposition and owner action on every recorded source.
- Owner image equals the actual front word applied to the corresponding retained terminal record target. Derived from birth word edges, prior source bounds, actual historical decomposition and strict saved cutoff coverage; no owner packet premise supplied.
- This is NOT yet equality with theta(y + 1 + rank), nor a proof of parallel inserted traces. General column/trace identification using copied-region/Sat_rec/+1 geometry remains open.
- Full build passed (1273 jobs); regenerated 834-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: frozen guard and record lookup invariant verified
- Added FrozenGuardInvariant. currentPlusOne depends only on nonterminal factor rows; arbitrary current-owner completion prefixes preserve it when those factors lie below the owner, without semantic event assumptions.
- frozen_completionRecord_eq combines exact word preservation with this structural guard equality. The complete lookup is unchanged, including failure cases, not only successful direct words.
- Full build passed (1274 jobs); regenerated 837-declaration audit passed without sorryAx or errors. Next specialize factor bounds/word preservation to actual original marked certificates, then use entrance copied-region invariants for general parallel packet identification. Main goal remains open.

### 2026-09-10: actual original record decisions and copied factor region
- Added FrozenRecordDecision. realized_frozen_completionRecord_eq derives exact word preservation, all factor bounds and intermediate validity from entrance row realization and processed event geometry. Every original mark retains its full completion decision, without word-length restriction.
- shortCopy_frozen_completion_factor_region transfers actual successful intermediate completions back to the entrance lookup, then transports the copied-region factor bound to the actual intermediate MarkTrace. Parent Sat and legitimate shortCopy remain explicit.
- Full build passed (1275 jobs); regenerated 839-declaration audit passed without sorryAx or errors. Copied-region Sat_rec/endpoint packet identification and final global well-order remain open.

### 2026-09-10: actual copied internal endpoints verified
- Added CopyFrozenEndpoints. Successful arbitrary-word frozen completions have a MarkTrace whose every internal pair has exact p = lower, e = lower + 1; both the factor and source-successor row lie in the copied region, and the successor row supplies b <= lower.
- The guard is identified with the actual preserved MarkTrace by successful computation uniqueness; endpoint facts come from existing currentPlusOne theorems.
- Search found no independently defined Sat_rec predicate. Do not treat the manuscript name as an established invariant: full historical endpoint/block geometry and parallel-column identification remain open.
- Full build passed (1276 jobs); regenerated 840-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: current guarded factors cannot regenerate historical packets
- Added GuardedFactorNative. On every guarded internal trace edge, current nativeSources is empty and current native is identity. Proof uses exact p/e successor geometry and endpoint B bound; covers eligible and long rows.
- This rules out deriving the required nonempty parallel blocks by rerunning native on current factor rows. NativeEndpointPacket must be applied at recorded birth states with historical endpoint data, then transported forward.
- Full build passed (1277 jobs); regenerated 841-declaration audit passed without sorryAx or errors. Need the historical factor-birth block invariant for general packets; main goal remains open.

### 2026-09-10: retained record full birth prefix verified
- Added ScanRecordBirthPrefix. scanReach_record_origin_prefix strengthens actual birth provenance with equality of every row through terminal + sources.length between the current scan and the actual post-native birth state.
- scanReach_record_birth_frozen_prefix preserves the same whole-prefix equality through arbitrary current-owner completion lists. Neither theorem assumes semantic event geometry or current validity.
- These witnesses permit historical block geometry to be transported directly, rather than rerunning current native or proving each retained field separately.
- Full build passed (1278 jobs); regenerated 843-declaration audit passed without sorryAx or errors. Need to establish the relevant historical factor block/endpoint geometry itself and identify parallel columns; main goal remains open.

### 2026-09-10: current record endpoint identifies last birth source
- Added RecordedLastEndpoint. For every retained nonempty record, recover a current bottom row whose e is exactly sources.getLast?, using the actual native birth, prior entrance validity and whole birth-prefix preservation.
- Only strictly prior entrance validity is used. This links current guarded e = child + 1 to the last historical source when a parent factor has a record; existence and adequate size of that parent record remain to be proved.
- Full build passed (1279 jobs); regenerated 844-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: recorded birth threshold recovered
- Added RecordedBirthThreshold. A retained record has an actual native birth whose input predecessor equals the current record predecessor, together with equality of the entire post-birth block prefix. This uses prior validity and native bottom p preservation.
- No separately assumed historical threshold equality. Parent-record existence and sufficient block entry/length remain open for general guarded factor pairs.
- Full build passed (1280 jobs); regenerated 845-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: ordered record birth and historical target chain verified
- Added OrderedRecordBirth. Two current records with lower < upper share an actual upper-birth witness in whose prior history the lower record already occurs; the upper output block prefix remains unchanged.
- scanReach_ordered_birth_target_chain derives every lower-record consecutive B edge at that actual upper native entrance, using strictly prior validity and prefix preservation.
- Assumes both records exist; does not yet derive an upper factor record from the guard, nor prove that its native walk enters the whole lower target segment. Those are the remaining packet-size/entry obligations.
- Full build passed (1281 jobs); regenerated 847-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: retained parallel predecessors from actual record births
- Added RecordedParallelPredecessor. For two retained records with current upper predecessor lower, an entered lower target segment yields predecessor a (upper + k) = some (lower + k).
- Derives actual birth timing, historical threshold equality via native_owner_predecessor, lower B chain, source rank/index bound, and forward prefix transport. No separately supplied birth, chain, threshold equality or upper-block-size premise.
- Still assumes both records and actual source entry lower + top in upperSources, plus top within the lower record length. These crucial entry/existence premises are not proved for general guarded factor pairs.
- Full build passed (1282 jobs); regenerated 848-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: deep packet entry probe clarifies untested long-word boundary
- Added CheckDeepPackets.lean, a deterministic bounded exploration of 120 paths with 80 steps each, E(1/2/3/5), cut and Mstar, parent size cutoff 45 and copied-entry size cutoff 80. Checks factor records, block size, the proposed internal source-entry condition and literal parallel traces on successful events.
- Completed successfully: 9600 state visits (not distinct states), 1283 direct successful events, zero longer successful events. Explicit long-word instrumentation found 2092 long-word observations, all completionRecord = none. Hence long words are present, but the decisive nonempty-record case was not exercised.
- This is finite exploratory evidence, not a proof of no long successful completions, and does not discharge record existence/source-entry assumptions. The formal build/audit baseline remains 1282 jobs / 848 declarations. No running probe remains. Main goal remains open.

### 2026-09-10: active-only and entrance-only direct fold closure
- Added FrozenActiveDirect. Inactive completionRecord=None events preserve state and supply vacuous event geometry regardless of word length; only successful events need a direct word.
- scanRankReach_entry_active_direct_frozen_fold further restricts that check to entrance marks/records only. Actual intermediate record equality and transported traces derive each later successful direct computation during the accumulated induction.
- This removes the overly strong all-marks-direct and all-intermediate-computations premises. It does not prove that all successful entrance words in the full domain are direct; longer successful events remain part of the original goal.
- Full build passed (1283 jobs); regenerated 850-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: arbitrary-word first propagated target identified
- Added FirstPropagatedTarget. For an actual successful computation front ++ [terminal,last], current +1 geometry identifies evalWord front theta(terminal+1) with theta(y+1), via completionRecord_exact_certificate and naturalCutoff_snoc.
- Covers any word length but only offset zero in the terminal target block (the first inserted target). Does not imply higher-offset packet identification or replace saved historical coverage.
- Full build passed (1284 jobs); regenerated 851-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: larger bounded probe completed without a successful long case
- Added CheckLargerPackets.lean with seed 724813, 60 paths of 140 steps, parent bound 100, copied-entry bound 160 and E(1/2/7/12). Retains explicit checks for factor record existence, block length, proposed source-entry premise and literal parallel traces, and prints full states on a successful long event.
- Process session 95105 completed: 8400 visits, 30 direct successful events, zero longer successful events. larger-packet-check.txt records the result. No probe process remains.
- Larger expansions mostly reduce useful successful-event coverage under these size cutoffs; this adds no evidence for the missing long-event source-entry premise. Do not continue treating blind exploration as a substitute for the historical copied-endpoint invariant.
- Formal baseline remains 1284 jobs / 851 audited declarations (no Lean theorem changed this turn). Main goal remains open.

### 2026-09-10: completion B-bound diagnostic verified
- CheckCompletionB.lean now passes lake env lean (exit 0). Explicit existential witnesses establish ProperMarks, which is not directly decidable by the available instances.
- The row core [0,1,3,5,7], step 2, marks [5], completed at 5 with source [2], remains CoreValid and ProperMarks at owner 7. Both p=3 and e=5 are unchanged, but B increases from 5 to 6. Source and target gaps 1<2<3 and 5+1<7 also hold.
- Consequently validity, proper marks, unchanged p/e and these gaps alone cannot transport a historical B upper bound through completion. A historical endpoint invariant must control inserted columns relative to that bound or derive a stronger alternative condition.
- This is a structural diagnostic only: neither reachability in the generated domain nor a semantic realization is established for this example. It does not refute the manuscript theorem. No library theorem changed; formal baseline remains 1284 jobs / 851 audited declarations. Main goal remains open.

### 2026-09-10: precise B preservation below entrance B
- Added CompletionEndpointBound with three verified theorems. row_b_eq_of_high_core_iff determines B from equality of the upper core region. completionEvent_b_eq_of_mark_lt_b proves B unchanged under a geometrically justified event strictly below old B. frozen_fold_b_eq_of_marks_lt_b proves the same for an entire frozen prefix whose marks all lie below entrance B.
- Uses actual high-core membership preservation, not preservation of p/e. Input/output CoreValid are explicit; event and processed-event geometry remain explicit. No claim that arbitrary generated histories satisfy the strict-mark premise.
- This isolates the boundary exposed by CheckCompletionB: marks at B require additional treatment. Historical copied-endpoint record existence and adequate source entry remain open.
- Full build passed (1285 jobs); regenerated 854-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: exact B increment at endpoint completion
- Added CompletionAtEndpoint. completeMarkRow_b_at_b proves new B = old B + sources.length when completing at old B, with explicit structural validity, source bounds and owner gap.
- completionEvent_b_at_b specializes to an actual successful CompletionEventGeometry and derives all those requirements, including output validity and existence of B. Its conclusion is an exact Option equality, not a bound conditional on a supplied output B witness.
- Together with CompletionEndpointBound this isolates the endpoint boundary: earlier marks preserve B, while successful completion at B extends it by exactly the packet length. Applying these results to copied historical endpoint records still requires the actual history and packet-entry invariant; that is not established here.
- Full build passed (1286 jobs); regenerated 856-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: unified exact endpoint update for actual completion
- Added CompletionEndpointUpdate. completionEvent_b_update gives out.B = oldB + (if mark = oldB then length of actual completionRecord defaulting to [] else 0).
- Covers absent records, successful lower marks, and successful marks at B. Derives successful mark <= oldB from event geometry and core validity; output validity and existence of output B are also derived. No extra proper-mark or source-bound premise is supplied by the caller.
- This gives a concrete update law for a subsequent historical endpoint invariant. It does not itself prove that a copied endpoint has a sufficient bound, or supply missing factor records/source entry.
- Full build passed (1287 jobs); regenerated 857-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: whole frozen completion endpoint from entrance record
- Added FrozenFinalEndpoint. completeFrozenMarks_b_final_mark proves the actual full frozen output B equals entrance B plus the entrance completionRecord length when the original marks split as processed ++ [B].
- Derives strict earlier-mark bounds from proper sorted original marks, prior event geometry from full events, intermediate row existence and validity, and exact prefix B preservation. Uses realized_frozen_completionRecord_eq to replace the last intermediate lookup by the actual entrance lookup; covers arbitrary trace length and None records.
- Requires entrance RankRowRealization and the prior/full event-geometry induction premises. Does not establish those for unproved general long successful events and does not discharge copied factor-record existence/source-entry obligations.
- Full build passed (1288 jobs); regenerated 858-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: full frozen endpoint formula without a last-mark assumption
- Added FrozenEndpointUpdate. properMarks_b_last derives that an occurrence of B in a valid proper row is its last mark, using sorted marks and the maximality of the penultimate core column below owner.
- completeFrozenMarks_b_update gives the actual full-fold output B = entrance B + (if B is an entrance mark then entrance completionRecord length defaulting to [] else 0). The absent-mark branch proves every mark strictly below B and uses frozen high-column preservation; the present branch invokes FrozenFinalEndpoint.
- No assumed split of marks and no output B witness remain. Entrance realization and all actual event geometries are explicit induction premises, not established for the missing general long successful events.
- Full build passed (1289 jobs); regenerated 860-declaration audit passed without sorryAx or errors. Copied historical factor records/source entry and main well-order goal remain open.

### 2026-09-10: actual scan-step endpoint bound
- Added ScanStepEndpointBound. native_bottom_b_le_or_empty removes the nonempty-source restriction from native bottom B nonincrease, identifying the empty native output with its input.
- scan_step_bottom_b_bound composes actual completeFrozenMarks with actual native: final bottom B <= entrance B + (if B is an entrance mark then its entrance completionRecord length else 0). Intermediate row existence, validity and B value are derived, not assumed.
- Entrance realization and actual frozen event geometry remain explicit. This is an endpoint estimate for the real scan operation, not a proof of all event geometries or of copied historical source entry. It correctly retains the increment that invalidates unconditional scan-step B nonincrease.
- Full build passed (1290 jobs); regenerated 862-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: retained record B bound from actual historical birth
- Added RecordedBirthB. scanReach_record_birth_b_bound recovers the actual before/after/history witness of a retained record together with its whole unchanged block prefix, and bounds the current bottom B by that birth entrance B plus its actual entrance endpoint-completion increment.
- Requires realizations and frozen-event geometry only at strictly earlier scan entrances. Derives birth row existence, its B witness, and the identification of the current bottom with the birth bottom. Does not rerun native on the current guarded row or assume current event correctness.
- The birth entrance hypotheses are explicit induction requirements. This result does not establish missing factor record existence or prove sufficient source-segment entry from the bound alone.
- Full build passed (1291 jobs); regenerated 863-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: first parallel predecessor without source-entry assumption
- Added RecordedFirstParallel. scanReach_recorded_first_parallel_predecessor derives predecessor(upper+1)=lower+1 from two retained records, their current predecessor relation and current upper e=lower+1.
- Recovers upper's last (least, not greatest) birth source via RecordedLastEndpoint, hence proves lower+1 belongs to upperSources. Lower-record nonemptiness supplies the size bound. Applies RecordedParallelPredecessor at offset 1 without separately assuming source entry or block size.
- Record existence remains explicit; no higher-offset source-entry claim is proved. The least-source endpoint is compatible with larger sources earlier in the descending native source list.
- Full build passed (1292 jobs); regenerated 864-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: guarded arbitrary-word first parallel edges
- Added GuardedFirstParallel. currentPlusOne_recorded_first_parallel_edges applies to any Trace length: every internal factor pair has predecessor(upper+1)=lower+1, provided each nonterminal factor has a retained record.
- Extracts p/e from the actual current guard, derives lower<upper from row validity, and obtains both records from factor membership. No per-edge source-entry or packet-size hypothesis is required at offset 1.
- This does not prove a whole new MarkTrace, higher offsets, or factor record existence. The latter remains a substantive explicit assumption and is not implied by this theorem.
- Full build passed (1293 jobs); regenerated 865-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: first recorded target literal terminal trace
- Added RecordedFirstTargetTrace. scanReach_record_first_target_trace proves Trace a x (terminal+1) [terminal+1,x] when x is the retained record's last source.
- Derives source decreasing order from actual birth and strictly prior validity, then proves the last source has zero ascending rank by splitting off the last singleton. Uses the actual recorded trace theorem; no independent rank-zero or current-validity assumption.
- Completes the terminal edge needed alongside GuardedFirstParallel internal edges. Assembly into a whole first-column trace remains to do; record existence and higher-column coverage remain open.
- Full build passed (1294 jobs); regenerated 866-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: complete first parallel literal Trace assembled
- Added FirstParallelTrace. trace_of_factor_chain assembles a valid nonempty predecessor chain and its terminal edge into a Trace, deriving source inequalities from valid predecessors.
- currentPlusOne_recorded_first_trace constructs the exact word xs.dropLast.map (+1) ++ [x], where x is the last/least source of the terminal retained record. Uses all internal guarded first-offset edges and the actual recorded terminal edge. No separate source-rank, first-column size or per-edge source-entry assumptions.
- Explicit prerequisites remain: valid current rows, strictly prior valid entrances, actual guarded Trace, nonempty factor decomposition and its terminal, and records for all factors. This is a Trace, not yet a completeMarkRow MarkTrace or a proof of record existence/higher offsets.
- Full build passed (1295 jobs); regenerated 868-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: first parallel Trace from actual successful completion
- Added CompletionFirstTrace. completionRecord_first_parallel_trace extracts computed word, guard, nonempty terminal record, least source and factor decomposition from actual completionRecord success and an original proper mark membership.
- Produces the literal Trace at y+1 with word xs.dropLast.map (+1) ++ [leastSource]. Derives terminal record membership and removes separate word decomposition/head/terminal/source assumptions from FirstParallelTrace.
- Still explicitly requires retained records for all factors of the computed word. This assumption is the unresolved historical existence obligation, not an established consequence of successful completion. MarkTrace placement and higher offsets remain open.
- Full build passed (1296 jobs); regenerated 869-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: first parallel word is an actual completed MarkTrace
- Added CompletionFirstMarkTrace. decreasing_last_rank_zero exposes the elementary minimum-source rank lemma. completionEvent_first_parallel_markTrace combines actual successful first Trace with rankRealization_completion_new_markTrace to establish the exact MarkTrace in completeMark at y+1.
- Derives the least-source rank from actual record birth and strictly prior validity, and derives placement/source geometry from the supplied CompletionEventGeometry. The conclusion uses the actual completeMark operation.
- Event geometry and all-factor record existence are explicit assumptions. This result must not be used circularly to establish current event geometry; it verifies placement after geometry is known. Higher offsets and general existence remain open.
- Full build passed (1297 jobs); regenerated 871-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: exhaustive provenance for every passed scan index
- Added ScanIndexOrigin. scanReach_processed_index_origin proves every positive i below the current cursor either lies in a retained record block [owner, owner+length], or has an actual prior ScanReach entrance at i with an empty native result and equality of its post-step row to the current row.
- Pure actual-scan induction; no validity, realization, Sat or event geometry assumptions. Uses prefix preservation for historical empty steps and exact cursor advance to exhaust new indices.
- This gives concrete branches for the unresolved all-factor record existence argument. A factor could still be an interior target of a block or an empty-step row; copied Sat/endpoint conditions must be used to eliminate or handle these branches. The theorem alone does not establish factor records.
- Full build passed (1298 jobs); regenerated 872-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: concrete alternatives for a missing factor record
- Added UnrecordedIndexCases. scanReach_unrecorded_index_cases refines passed-index provenance under absence of an own-key record: either its current B is exactly i-1 (an interior recorded target), or a real prior entrance at i has nativeSources after frozen completion equal to [] and its completed row equals the current row.
- Uses only actual ScanReach and strictly prior completed-row validity. The block-base case is excluded by missing-record membership, and empty native output is identified with its completed input.
- Neither alternative has yet been ruled out for all relevant copied guarded factors. This is a concrete reduction of the existence problem, not a proof of all-factor record existence.
- Full build passed (1299 jobs); regenerated 873-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: every recorded target predecessor is below its block base
- Added RecordedTargetPredecessor. scanReach_record_target_predecessor_below_base recovers a source x in the actual retained record for every positive target offset k <= length, with predecessor(owner+k)=x and x<owner.
- Uses record distinctness to invert ascending source rank, then actual prior recorded predecessor and source bounds. Requires only strictly prior completed validity; no current semantic event geometry or source-entry premise.
- Covers all target offsets and constrains the interior-target branch of missing factor provenance. It does not yet exclude that branch for guarded copied factors or prove their own records.
- Full build passed (1300 jobs); regenerated 874-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: old image indices exclude interior-target provenance
- Added HistoricalIndexOrigin. historical_image_not_inside_record uses strict monotonicity and consecutive original-index images owner / owner+length+1 to prove any image in the closed record block is its base.
- scanReach_historical_image_origin combines actual passed-index provenance with same-map record alignment: every positive old image below cursor has its own record or an actual empty birth. The interior-target branch is eliminated for these images.
- Verified native shift convention: shiftAfter fixes the old owner, moving only strictly larger indices. Thus old owners map to block bases, not tops. The existing historical certificate supplies exactly the required map alignment; applying it to every relevant word factor and ruling out empty births remain to do.
- Full build passed (1301 jobs); regenerated 876-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: actual original mark factor provenance
- Added MarkFactorOrigin. scanRankReach_mark_factor_origin extracts the exact original mark word and computed trace from the historical certificate, then proves every positive factor has its own record or an actual empty native birth with current-row equality.
- The same strict map and record-block alignment come from scanRankReach_current_historical_certificates, not separate assumptions. Factor bounds below cursor follow from the actual trace and current proper marks.
- Requires initial and current RankRowRealization and strictly prior ScanPriorGeometry. Applies to entrance original marks; the positive-factor condition is explicit. Empty births remain to be excluded/handled in the copied guarded success setting, and higher-column entry remains open.
- Full build passed (1302 jobs); regenerated 877-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: actual completion e preservation
- Added CompletionPreservesEndpoint. completionEvent_preserves_e handles None and successful completions with e<=mark. completionEvent_reachable_preserves_e discharges that inequality at actual ScanReach entrances using prior validity and the marked-source minimum theorem, including long rows.
- Output is the actual completeMark owner row. Source/target gaps and source<p<e are derived from event geometry; no separately assumed output e witness.
- This is needed to transport original endpoint images through empty-birth rows. Whole frozen-fold e preservation and coherent historical endpoint-image induction remain to do; no empty-birth branch has yet been excluded.
- Full build passed (1303 jobs); regenerated 879-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: entire frozen completion preserves entrance e
- Added FrozenPreservesEndpoint. completionEvent_frozen_preserves_e uses the actual frozen-prefix source-minimum theorem to discharge e<=mark without treating intermediate states as ScanReach entrances.
- completeFrozenMarks_preserves_e proves full-fold preservation via frozen_prefix_bootstrap. Actual current mark membership is recovered by transporting each original marked trace through prior verified events. No assumed intermediate realization beyond the supplied event geometry, and no caller-supplied intermediate e witnesses.
- Entrance RankRowRealization, strictly prior completed validity and actual event geometries remain explicit. Next substantive dependency is coherent original endpoint-image transport for empty births, needed to contradict a lower nonempty record gap and current +1 guard.
- Full build passed (1304 jobs); regenerated 881-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: native endpoint transport outside nonempty owner expansion
- Added NativeUnexpandedEndpoint. native_unexpanded_endpoint_shift gives the exact mapped Row.e for any old row i when i differs from the native owner or sources=[]. Covers unchanged prefix, shifted suffix and empty owner in one statement.
- Requires only input row validity and actual native success; derives endpoint <= row index for the prefix branch. It does not assert e preservation for a nonempty native owner, whose bottom e changes to the least source.
- This provides the native component of coherent endpoint-image transport for unrecorded original rows. Combining with full frozen e preservation and the unified origin-map induction remains to do; the empty-birth contradiction is not yet proved.
- Full build passed (1305 jobs); regenerated 882-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: combined scan-step endpoint transport for unexpanded old rows
- Added ScanStepUnexpandedEndpoint. scan_step_unexpanded_endpoint composes actual full frozen completion with actual native. For any old row other than a nonempty expanded owner, its e is transported by the same shiftAfter as its index.
- Derives intermediate row existence from preserved length, endpoint preservation from full frozen e at owner or other-row equality, and completed validity from actual event geometries. No intermediate row/e witnesses are caller assumptions.
- Ready for coherent origin-map induction with absence of own record ensuring no nonempty owner expansion. That induction and the contradiction with a lower retained block gap remain unproved.
- Full build passed (1306 jobs); regenerated 883-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: coherent historical endpoint and record-block map
- Added ScanPriorEndpointTransport and ScanEndpointAlignment. scanRankReach_endpoint_alignment strengthens the origin map with exact mapped e for every original row whose image has no own record. The SAME phi retains semantic assignments, predecessor alignment, unscanned tail, and consecutive original-index endpoints for every retained block.
- Induction propagates missing-record membership backward and excludes nonempty owner expansion at the relevant old image. No separate unrelated endpoint map is used.
- scanPriorEndpointTransport_of_events discharges transport obligations using strictly prior completed validity, actual prior entrance realizations, and their frozen event geometries via ScanStepUnexpandedEndpoint. The prior obligations remain explicit; no current event is assumed correct.
- This is the needed coherent-map bridge for excluding an unrecorded +1 upper factor above a recorded lower factor. That contradiction and its application to all actual word factors remain to do.
- Full build passed (1308 jobs); regenerated 886-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: +1 endpoint forces an upper record under the coherent map
- Added EndpointRecordPropagation. historical_image_ne_first_target excludes any old image at the first target of a nonempty record block.
- scanRankReach_endpoint_record_propagation extracts one coherent map with semantic holds and record alignment, and proves: an original row image whose current e is lower+1 must have its own retained record whenever lower has a record.
- The upper record is derived by contradiction from absent-record endpoint transport and the lower record's consecutive-image gap; it is no longer an assumption in this local propagation theorem. Requires initial validity and prior endpoint transport (already reducible to verified prior events).
- Remaining integration: align the actual marked word with this SAME map and original row existence, then propagate from its terminal record through every guarded edge. Higher-offset full source entry and final global results remain open.
- Full build passed (1309 jobs); regenerated 888-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: record propagation for actual marked-word factors
- Added OriginMapComparison and MarkEndpointRecordPropagation. Bounded indices with equal realized column values are equal; the coherent endpoint map sends original bounded indices into the current bounded range.
- scanRankReach_mark_endpoint_record_propagation obtains the actual original mark word and establishes upward record propagation for its positive factors with e=lower+1 above a retained lower record. It reconciles the marked-word map and endpoint map using equal semantic values and proved bounds, rather than assuming the maps coincide.
- Original factor row existence is derived from the initial trace and index bounds. Initial/current realization, prior geometry and prior endpoint transport remain explicit; the upper record is a conclusion.
- Next: chain induction from the actual terminal completion record to all factors, then remove the all-factor record premise from first-column theorems. General higher-offset source entry and global goal remain open.
- Full build passed (1311 jobs); regenerated 891-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: all factors of a successful original word have records
- Added CompletionFactorRecords. list_all_of_last_and_backward supplies the finite backward-chain induction. scanRankReach_completion_all_factor_records starts from the actual successful terminal record and propagates through currentPlusOne_all_endpoints using MarkEndpointRecordPropagation.
- All-factor record existence is now a conclusion for successful original entrance marks under initial/current realization, prior geometry and prior endpoint transport. Positive factors needed by propagation are derived from actual upper-row lookup. No explicit copied-region assumption is required by this conditional theorem.
- scanRankReach_completion_first_trace removes the all-factor-record premise from the complete first-column Trace theorem by applying the new result.
- Scope: prior endpoint transport is reducible to verified prior events, not automatically available without the event induction. Intermediate frozen successes still need integration via record/trace preservation. General higher-offset source-segment entry and packet coverage, and the full global goal, remain open.
- Full build passed (1312 jobs); regenerated 894-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: all-factor records at intermediate frozen successes
- Added FrozenFactorRecords. scanRankReach_frozen_all_factor_records proves every factor of the actual intermediate computed word has a retained record, for any successful original frozen mark.
- Transfers success to the entrance via realized_frozen_completionRecord_eq, obtains entrance all-factor records, and identifies the intermediate computed word using transported actual MarkTrace and derived frozen validity.
- Only prior processed event geometries are required; current event geometry is not assumed. Initial/current entrance realization, prior scan geometry and prior endpoint transport remain explicit induction hypotheses.
- The earlier all-factor existence gap is now handled at both entrance and intermediate original-mark events under these hypotheses. Full higher-offset source entry/packet geometry and the global well-order goal remain open.
- Full build passed (1313 jobs); regenerated 895-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: full source-segment entry reduced to no interior jumps
- Added NativeNoJumpEntry. nativeSourcesFuel_enters_segment_of_no_jump proves that an actual successful B walk starting above base+top and reaching base+1 includes base+top, provided B edges from above the segment cannot land strictly between base and its top.
- nativeSourcesFuel_full_segment_of_no_jump combines this entry result with the existing consecutive target B chain to derive all segment source memberships. No global validity is needed for this purely operational walk argument.
- The noJump condition is an explicit unproved structural obligation for the relevant historical copy states, as is the appropriate birth start bound. These results do not discharge general packet coverage by themselves or replace the original goal with a conditional theorem.
- Full build passed (1314 jobs); regenerated 897-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: targeted finite check of the no-interior-jump candidate
- Added CheckNoJump.lean. It checks every retained block against all later B rows at both scan entrance and post-frozen completion, failing with full pattern/records on base < B(z) < base+block.length for z above the block.
- Final run completed successfully: seed 193171, 30 paths x 60 steps, 1800 state visits, 20334 scanned steps, 1206 checked B-edge instances involving record lengths >1. Parent/copy size bounds remain 45/80; expansions E1/E2/E3/E5, cut and Mstar. no-jump-check.txt contains the output.
- The initial 300-visit run lacked informative counters and is not the coverage claim. The final counter measures actual nontrivial edge checks, not successful long packet events or distinct states.
- Finite support only; noJump remains unproved for all actual birth states. No probe process remains. No library theorem changed; verified baseline stays 1314 jobs / 897 audited declarations. Main goal remains open.

### 2026-09-10: exact obstruction to an overly global noJump invariant
- Added NoJumpEndpointObstruction. shorter_endpoint_completion_enters_record_interior proves that an actual geometrically valid completion at B=base with 0<readSources.length<the retained base block length yields output B strictly inside that block, at an owner strictly above its top.
- This is a conditional obstruction, not an exhibited reachable counterexample. It shows that a global noJump proof would additionally need to exclude all such shorter endpoint completions. Existing all-factor record existence and first-column proofs do not establish that exclusion.
- The finite CheckNoJump pass cannot resolve this issue; prior probes exercised no successful long-word events. Do not treat the global candidate as known valid. Focus subsequent source-entry work on the needed historical path and packet width, or establish the missing length restriction before using global noJump.
- Full build passed (1315 jobs); regenerated 898-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: source entry requires noJump only on the actual native path
- Added NativePathEntry. nativeSourcesFuel_enters_segment_of_path_no_jump and nativeSourcesFuel_full_segment_of_path_no_jump weaken the global noJump assumption to visited rows in u::sources of the actual successful walk.
- The recursive proof passes exact visited-tail membership backward; unrelated rows are not constrained. Full target-segment membership still follows from path entry and the recorded consecutive B chain.
- Path-local noJump, start-above, and reaching-first-target must still be derived for the intended historical upper birth and requested packet width. No such universal birth-state derivation is claimed here. The global shorter-completion obstruction remains relevant to choosing the invariant scope.
- Full build passed (1316 jobs); regenerated 900-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: native entrance e is above the full predecessor record block
- Added NativeEntranceAboveRecord. scanRankReach_e_above_predecessor_block derives base+record.length<e from the actual current-row original-column gap and p<e.
- scanRankReach_completed_e_above_predecessor_block transports this exact e through all frozen completions using FrozenPreservesEndpoint, reaching the actual native input. The whole lower-record length bounds any shorter required target segment as well.
- Requires a retained predecessor record, current entrance realization and verified frozen events for the second theorem. Application at recovered upper birth must match those entrance witnesses; path-local noJump remains unproved.
- Full build passed (1317 jobs); regenerated 902-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: real native birth full segment conditional only on path noJump
- Added NativeBirthSegment. native_birth_full_segment_of_path_no_jump uses an actual ScanRankReach entrance, full frozen events, actual nonempty native result and its bottom e=base+1, with a retained lower record.
- Derives the actual input p/e, e above the entire lower block, last source=base+1 from native bottom witness, and all lower target B edges at the same completed entrance. For any positive top <= lower record length, path-local noJump then yields every base+k source through top.
- Removes independently supplied walk, start bound, first-source entry and B-chain assumptions at this birth. Path noJump and applicability of the birth premises to each historical factor pair still require proof; no claim that general packet coverage is complete.
- Full build passed (1318 jobs); regenerated 903-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: exact first-target entry and actual birth packet
- Added NativeFirstTargetSegment. An arbitrary native-walk starting endpoint with B exactly base+top and the consecutive target B chain gives exact source length top and all segment members. Unlike NativeTargetEntry, the starting endpoint need not equal base+top+1.
- Added NativeBirthExactPacket. At an actual ScanRankReach birth, derives the completed p/e and retained lower-record chain from prior validity and verified frozen events, then obtains exact packet length and every parallel predecessor from the first-target equality. No bottom-endpoint or noJump premise is needed for this alternative.
- The exact first-target equality remains an explicit hypothesis. Its derivation from the intended Sat_rec history, or a broader sufficient entry statement when that equality is too strong, remains open. This does not complete general successful long-word packet coverage or the main well-order theorem.
- Full build passed (1320 jobs); regenerated 905-declaration audit passed without sorryAx or errors.

### 2026-09-10: native preserves bottom B exactly, eliminating a historical uncertainty
- Added NativeHighEntryRetention: short descent retains any high core entry below the owner without a mark hypothesis; iterated short descents and the initial medium exception retain its exact bottom index.
- Added NativeBottomBExact. nativeBlock_bottom_contains_b derives retention of the original B for every actual nonempty block using ordinary shape (short nonempty rows have step >= 3), exact top rank, and both descent lemmas. native_bottom_b_eq then combines retention with the prior upper bound and handles empty steps to prove exact B preservation for every actual native output.
- Added ScanStepBExact. scan_step_bottom_b_update gives exact bottom B after completeFrozenMarks followed by native: entrance B plus the entrance completion-record length when B is marked, otherwise entrance B. Requires actual current realization and verified frozen events; does not assume current native packet geometry separately.
- This strengthens NativeBottomBound/ScanStepEndpointBound from inequalities to equalities. Next work should transport this exact update along historical endpoint origins and analyze which endpoint completion record supplies the width. The shorter-completion obstruction is still relevant; exact native preservation alone does not exclude it or prove all higher-offset packets.
- Full build passed (1323 jobs); regenerated 911-declaration audit passed without sorryAx or errors. Main well-order goal remains open.

### 2026-09-10: exact historical B and transport at every old index
- Added RecordedBirthBExact. scanReach_record_birth_b_exact upgrades the retained-record birth bound to equality, preserving the actual prior entrance, native result and unchanged-prefix witnesses. Uses only strict earlier verified realizations/events.
- Added NativeBTransport. native_b_shift transports B at every old row under shiftAfter, including the expanded owner. This has only actual native success and input CoreValid premises; there is no unexpanded-owner restriction.
- Added ScanBTransport. scan_step_all_b_update gives the exact old-index update across the complete scan step: add the endpoint-completion length only at the owner with marked entrance B, then apply shiftAfter. All other old B edges transport exactly.
- Next: use this formula in the origin-map induction to classify historical endpoint images and their possible completion increments. No claim yet that the relevant increment equals the lower record width, nor that full higher-offset packet coverage is proved.
- Full build passed (1326 jobs); regenerated 914-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: historical cutoff bounded by the head record successor
- Completed and integrated ScanHistoricalWidthCutoff and ScanFrozenWidthCutoff from the interrupted turn. Their bounded certificates retain delta <= theta(y+headRecord.length+1) whenever the mark y has a retained record, using original trace cutoff bounds and the same origin-map record alignment.
- Added ScanBoundedPacketCoverage and RecordedWordWidthBound. Successful arbitrary-word completion now yields a single historical delta with both terminal packet coverage below delta and the head-record successor upper bound. The mapped word, source record and weak agreement remain part of that same witness.
- This is a semantic upper bound on propagated packet values, not yet a natural-number packet-width inequality. Identifying all propagated targets as actual parallel columns remains necessary; do not use that identification circularly to derive itself.
- Interrupted build had no live lake/lean processes on recovery. Full build now passed (1330 jobs); regenerated 918-declaration audit passed without sorryAx or errors. Main goal remains open.

### 2026-09-10: verified packet widths and original B intervals
- Added VerifiedCompletionWidth. scanRankReach_verified_completion_width proves readSources.length <= headRecord.length for an already verified frozen completion, using the same historical delta's terminal-packet coverage and head-successor bound. If the read packet were wider, the source at rank headRecord.length would have its identified target both below delta and at/above that successor, a contradiction.
- Added CompletionHeadRecord and FrozenHeadWidth. A successful entrance completion supplies its head record via the established all-factor theorem; an actual verified frozen event therefore supplies its own head record and width bound. This still requires the current event's packet identification when proving its width and is used only as a prior-event fact for later scanning.
- Added BirthBOriginalInterval: the bottom B at a verified birth belongs to [phi(v), phi(v+1)) for the original owner's original B=v, with the actual semantic origin map and original row witnesses retained.
- Added ScanOriginalBIntervals, defining ScanPriorVerifiedEvents and proving scanRankReach_original_b_intervals by the full actual ScanRankReach induction. The SAME map aligns all semantic assignments, all untouched future rows, record successor boundaries, and B intervals for EVERY original row, including recorded/expanded owners. At the current owner, endpoint completion width bounds its increment; elsewhere exact scan B transport preserves the interval.
- Added VerifiedScanObligations: prior verified realizations/events discharge both ScanPriorGeometry and ScanPriorEndpointTransport, the latter by lifting unlabelled actual scan states for history validity. No new axiom or unresolved proof obligation was introduced.
- Added HistoricalSatEndpointCap. An original local witness B(e)=v <= lower and a retained record at phi(lower) imply current B(phi(e)) <= phi(lower)+record.length, under the same map as untouched future rows. This does not assume the whole short-copy output is Sat; local copied-region witnesses can be supplied later.
- Remaining: synchronize the relevant short-copy internal Sat witnesses and endpoint images with recovered upper-factor births; use the cap and actual consecutive B chains to identify source segments; prove the lower width needed by an arbitrary successful word. The upper width bounds here do not imply full parallel coverage by themselves. Root/realization, full generated-domain closure, Steel integration and final well-order requirements remain open.
- Full build passed (1337 jobs); regenerated 926-declaration audit passed without sorryAx or errors. Main goal remains active.

### 2026-09-10: actual Sat-copy births yield initial packets and all head-width traces
- Added CopyPrefixValues: both original ordinal columns and row embeddings at i <= parent.length stay fixed throughout the actual short-copy scan. Nonempty births cannot occur before parent.length by the existing record-region theorem.
- Added CopyOwnerEndpointCap: aligns the current owner row and all original B intervals under the same phi; an original predecessor below parent.length would have its unchanged prefix value identify phi(lower)=lower, contradicting the recorded-owner region. This supplies an actual copied-region Sat witness and proves current B(e) <= base+lowerRecord.length, without assuming the entire copied pattern is Sat.
- Added FrozenEligibility: verified completion preserves core.length + 2*oldStep = oldCore.length + 2*newStep, individually and through an arbitrary frozen prefix; native eligibility is equivalent before/after full completion.
- Added CopyNativeInitialPacket: every actual nonempty native birth with a retained predecessor after a Sat short copy has sources.length <= lowerSources.length and all lower+k source members / output parallel predecessors for 1 <= k <= sources.length. It derives input eligibility, e<owner, exact frozen p/e, the copied Sat B cap, and exact initial B target. NO source-entry, first-target-equality, noJump, or bottom-e guard hypothesis remains. Requires the actual birth's verified frozen events and strict prior verified events.
- Added CopyRecordedInitialPacket: recovers each ordered pair's actual higher birth and preserves the whole output prefix to obtain the same width inequality and all upper-width parallel edges for retained records whose predecessors are adjacent in the current word. Uses earlier verified events only, not current event geometry or guard.
- Added CopyParallelThroughHead and CopyTraceThroughHead: every factor's record has width at least the head width; every offset within the head width has a whole literal parallel trace ending at the terminal source of the same ascending rank. Added RecordUnique for actual history lookup consistency, and the generic forward-list property lemma.
- Added CopyCompletionHeadPacket: actual arbitrary successful entrance completion supplies its own word, head record, headWidth <= readSources.length, and every full parallel trace for 1 <= k <= headWidth. All-factor record and geometry/endpoint transport premises are discharged using earlier verified events.
- The central remaining width gap is now explicit: headWidth <= terminal/readWidth is proved, but complete coverage requires readWidth <= headWidth. VerifiedCompletionWidth proves that reverse bound ONLY when the current event already has its entire identified packet, so using it here would be circular. Need a prior-history/endpoint-word argument (or an independent proof) for the reverse bound. Do not claim initial packets cover all lower records, nor that long-word closure is complete.
- Full build passed (1346 jobs); regenerated 938-declaration audit passed without sorryAx or errors. No running build remains. Main well-order goal remains active.

### 2026-09-10: full arbitrary-word packets and actual full-scan row closure
- Added CopyVerifiedWidthEquality and CopyBBoundaries. A strictly earlier verified event reads exactly its head-record width. The same origin map now puts every original B either at its original image or at the top of an actual retained block, using earlier verification only. This strengthens the former open-interval bound without assuming current event correctness.
- Added CopyOwnerEndpointBoundary, CopyNativeFullPacket and CopyRecordedFullPacket. A current copied-region Sat endpoint is either at/below the predecessor base or at the predecessor block top. An actual nonempty native walk must start at that top; its exact consecutive B chain gives the full source packet and every parallel predecessor. Ordered actual record births transport this to all adjacent recorded factors.
- Added CopyCompletionFullTraces, CopyFrozenFullTraces and CopyPacketOwnerEdges. Every factor of an actual successful arbitrary word has the same width as its terminal/read record. All offsets therefore have whole literal parallel traces, including intermediate frozen states. Their evaluated embedding words identify every owner packet edge using the preserved historical weak agreement.
- Added CopyFrozenEventGeometry, CopyFrozenNewCertificate, CopyFrozenAllCertificates and CopyFrozenRealization. Equal head width supplies all target gaps and bounds, yielding the complete current event geometry independently of that event's verification. The historical origin map supplies exact factor embeddings and successor bounds for each full parallel word; its own natural cutoff carries the weak owner agreement. Old and new marks together give full row realization after each frozen event.
- Added CopyFrozenFold: induction over the actual sorted entrance mark list simultaneously proves all intermediate realizations and every event. No active/direct-word restriction remains.
- Added CopyScanRealization: strong induction on the actual cursor proves all scan entrances and all frozen events. NativeRankRealization advances each completed entrance; strict cursor decrease supplies exactly the prior verified histories used by the packet lemmas. The previous ScanPriorVerifiedEvents premise is discharged, not assumed by this theorem.
- Added CopyFullScanClosure: shortCopy_fullScan_total_realized lifts every unlabelled history to the verified semantic scan, derives history validity, and applies actual scan totality and Sat closure. The literal fullScan succeeds and its output has RankMarkedRealization on the same rank domain.
- Remaining assumptions/boundaries: CoreValid Sat parent, actual successful shortCopy, a supplied RankRowRealization of that copy, and Order.IsSuccLimit lambda. Constructing the copied entry realization, first-triple common-endpoint linedness, I2 root, full E/M_star generated closure, Steel integration, final well-ordering and injectivity remain open. RankMarkedRealization here is the row/mark component, not the full linedness certificate.
- Full build passed (1361 jobs). Regenerated audit passed for 955 theorem declarations, with no sorryAx, custom axioms or errors. Source scan found no axiom/sorry/admit/unsafe declarations. Main goal remains active and unproved.

### 2026-09-10: genuine application construction, elementarity and algebra
- The copied-entry realization requires applied owners; the prior library had genuine elementary embeddings and ordinary composition but no application construction. Addressed this foundational gap directly, without postulating application or its closure.
- Added RankSubsetPreservation and RankRestrictionGraph. Restrictions of k to the members of any set d in V_lambda have range in k(d), are set graphs inside the same domain, and map under j to actual function graphs. Restriction inclusion and the graph edge j(x) -> j(k(x)) are proved.
- Added RankApplicationRelation. The union of image restrictions is functional using a common union domain. Totality is first proved under the precisely defined membership-cofinality condition; RankImageCofinality then discharges that condition for every actual elementary self-embedding of a successor-limit rank.
- Added RankPowersetPreservation and RankImageCofinality. An explicit membership-language formula gives powerset preservation. Well-founded induction on alpha proves V_alpha subset j(V_alpha), using the earlier-level powersets in the definition of V_alpha. This gives point coverage and common coverage of finite tuples, with no cofinality assumption left.
- Added RankGraphElementarity. For each finite formula phi, an explicit first-order formula expresses that a set graph preserves phi. This is not a uniform satisfaction predicate. Image restrictions preserve every such phi by elementarity of j, so their total union is fully elementary.
- Added RankApplication: rankApply is an actual RankElementaryEmbedding, built from that total union and its full formula proof. Proved the semiconjugacy equation, the embedding composition equation and the ordinal-image equation.
- Added RankApplicationIdentification: rankTruncatedGraph is literally the external graph of k separated inside V_alpha. Cofinal inclusions between these graph cuts and the domain restrictions identify the constructed application pointwise with the standard union of j(k intersect V_alpha). The construction therefore matches the intended operation, not merely its image equation.
- Added RankApplicationCritical: first-order bounded-ordinal fixedness transfers from the original restrictions; together with movement at j(c), this proves RankCriticalPoint (rankApply j k) (j(c)) from RankCriticalPoint k c.
- Added RankApplicationComposition: transfers graph composition and proves j applied to (k composed with l) equals (j applied to k) composed with (j applied to l), then derives the identity and finite-word laws. These hold on all inputs, not just the range of j.
- Source correspondence and outstanding obligations are recorded in APPLICATION_FOUNDATION.md, referencing Laver's original application definition. The next key weak-cutoff dependency is the exact hierarchy image j(V_alpha)=V_{j(alpha)}; only V_alpha subset j(V_alpha) is currently proved. A concrete graph-recursion route is documented there as a proposal, not a completed proof.
- Full build passed (1371 jobs). All 996 theorem declarations passed the regenerated audit; only propext, Classical.choice and Quot.sound occur, and the source scan found no axiom/sorry/admit/unsafe declarations. No build remains running. Main goal remains active: copied-entry realization, full linedness and generated closure, I2 root, Steel integration, final well-ordering and injectivity are not yet complete.

### 2026-09-10: exact hierarchy images, copied-row geometry and high certificates
- Added RankHierarchyGraph and RankHierarchyRecursion: the actual V hierarchy is represented by a set graph on alpha+1; an explicit first-order recursion formula transfers through elementarity, and ordinal induction proves uniqueness. RankHierarchyImage gives j(V_alpha)=V_(j(alpha)) and exact set-rank preservation. The earlier hierarchy-image gap is closed.
- Added RankApplicationAgreement, RankApplicationCutoff and RankApplicationBelowCritical: actual weak membership agreement transfers through application at the exact image cutoff; arbitrary finite natural words have exact cutoff images and transferred certificates; all sets below the critical point are fixed and j applied to k weakly agrees with k there.
- Added CopySemanticValues, CopySemanticEdges, CopyDecomposition, CopySemanticColumns and CopySemanticRows: the concrete short-copy columns and applied owners agree with all three successful copyEntry branches. The full list mapping includes the implicit endpoint. Every output row has its exact original source, and every edge, critical point, cardinal column and strict column inequality is proved for the whole successful copy.
- Added NaturalCutoffReindexExact, CopyWordCertificates, CopyHighWord, CopyPrefixCertificates and CopyHighCertificates: exact factor/successor reindexing transports natural cutoffs. Retained prefix marks have their full certificates. The actual all-high branch has an identified full factor word, even if its endpoint is below p, and a complete weak certificate at the exact image cutoff.
- Added RankIntersectionPreservation and RankAgreementComposition: intersection preservation is proved by an explicit first-order formula. At a limit cutoff, weak agreement extends to all inputs by truncating each input above the test rank; equality of truncated images then transports agreement through ordinary postcomposition at the image cutoff.
- Added RankCriticalLimit: zero and successor preservation are proved from actual elementarity, powerset and rank preservation, so every actual critical point is a nonzero limit. RankApplicationLowTail consequently proves low-tail replacement through an arbitrary applied prefix and the corresponding historical-certificate transfer with a possibly lowered cutoff. This is an embedding-level result, not yet a certificate for the concrete low copy trace.
- Next: identify the exact mixed low word and its successor cutoff, use the low-tail certificate, and prove the guarded middle-splice word certificate. Then assemble all copy retention branches into RankRowRealization and eliminate the copied-entry premise of CopyFullScanClosure. Full same-endpoint linedness, I2 root, E closure, exact generated domain, Steel integration, final comparison well-order and injectivity remain open.
- Full build passed (1391 jobs). Regenerated audit passed for all 1047 theorem declarations; only propext, Classical.choice and Quot.sound occur. Source scan found no axiom/sorry/admit/unsafe declarations. No build or audit remains running. The original goal remains active and unproved.

### 2026-09-10: all natural copy branches and actual M_star row/mark closure
- Added CopyLowWord: the first-below-p split gives the actual translated high prefix and unchanged low tail; the terminal-low condition ensures the tail has a nonempty factor word. RankWordConcatenation proves exact natural-cutoff and bundled-embedding concatenation/reindexing. CopyLowWordCertificate and CopyLowCertificates derive the tail bound from its actual trace and establish the complete literal low-branch marked certificate.
- Added RankMiddleSplice: weak agreement at a limit cutoff also survives right composition. Critical-point fixedness and left-composition transfer compare an application owner with its ordinary composition at the applied owner's critical-point image. Combined with the two parent certificates this gives the middle splice at three explicit bounds.
- Added RankNaturalCutoffCardinal: natural cutoffs of realized traces are actual cardinal ordinals. Above a genuine critical point they are infinite cardinals and hence nonzero limits, discharging the composition lemma's limit hypotheses in the middle case.
- Added CopyMiddleWord: identifies the full actual middle word as translated high factors, the parent's marked bridge factors, and the unchanged low tail. RankTraceGeometry proves cutoff and source-successor bounds from only row validity, increasing columns and realized edges, without assuming the mark certificate being constructed.
- Added CopyGuardCutoff: the correct one-based guard bounds the next source column; its actual step edge covers the marked target's successor. Thus the new natural cutoff is below the copied owner's image of the removed last row's critical point. This discharges the delicate owner bound without a circular copied-entry realization premise.
- Added CopyMiddleNaturalData and CopyMiddleCertificates: the bridge's trace and weak certificate give the two remaining image/cutoff bounds; all limits, exact factor assignments, whole-word identification and the guard-derived owner bound are discharged from actual parent/copy data. CopyAllCertificates combines all three literal retention cases and all retained prefix marks.
- Added CopyRankRealization. rankRowRealization_shortCopy now constructs the complete copied-entry RankRowRealization using the concrete copied columns/applied owners, from a parent RankRowRealization and literal shortCopy success. It has no Sat, internal +1, packet geometry, copied certificate, or semantic legality filter premise.
- Added MStarRankRealization. rankMarkedRealization_copy_fullScan eliminates the supplied copied-entry hypothesis of CopyFullScanClosure. rankMarkedRealization_mStar_total proves actual M_star success and full row/mark/Sat realization on the same domain for every realized transient parent with a legal original short copy. rankMarkedRealization_mStar handles a specified successful output. mStar_exists_iff_shortCopy proves scanning adds no extra failure condition.
- Remaining: full common-endpoint linedness and its preservation; semantic E(k) and the actual auxiliary owners; I2 root; exact generated-domain closure; terminal ordinal/owner transport through the full operations; same-domain Steel theorem; final short-key comparison bridge, injectivity and well-ordering. The row/mark M_star theorem is a substantial local closure theorem, not the complete manuscript theorem.
- Next concrete E interface: extend a realized pattern by the literal auxiliary row using an actual embedding with critical point theta(anchor) and edge theta(anchor) -> theta(last endpoint), with its image as the new final column; then invoke short-copy realization and combinatorial auxiliary Sat preservation. Construct these embeddings from complete finite common-endpoint linedness witnesses, not as an assumed extension property.
- Full build passed (1405 jobs). All 1078 theorem declarations passed the regenerated audit, using only propext, Classical.choice and Quot.sound; source scan found no axiom/sorry/admit/unsafe declarations. No tool process remains running. Main goal remains active and unproved.

## Continuation update: complete finite witnesses and actual E semantic closure

Added AuxiliaryRankRealization, RankLinedWitness, ExpansionRankStages,
ExpansionRankEdges and ExpansionRankRealization. All are imported by the
project root; the full build passes with 1410 jobs and all 1089 theorem
declarations audit to Classical.choice, propext and Quot.sound only.

The auxiliary append uses its actual elementary embedding to define the new
terminal and retains the old columns and embeddings. The literal appended
row is realized with all critical points, edges, cardinality, increasing
columns and inherited exact natural-cutoff certificates. Composing with the
proved short-copy theorem gives actual auxiliaryStep closure, old-column
preservation, the new terminal aux(old terminal), and last owner aux(old owner)
under application, together with combinatorial Sat preservation and totality.

RankLinedWitness records a complete positive finite chain, both fixed endpoints,
and each factor's critical point and two edges. Its application transport is
constructed using rankApply, not postulated. The expansion-stage induction
tracks the current terminal as the exact current point of this fixed witness;
only completing all k stages recovers the specified final endpoint.

The literal successor/limit row classification forces J(theta0)=theta(anchor),
J(theta1)=theta(parent owner), and J(theta2)=theta(parent terminal). Applying J
to the whole first-triple witness produces the actual auxiliary factors. Thus
rankMarkedRealization_expand proves the real expand computation succeeds and
retains the parent terminal. Its final owner is (J(l_k))(H), and crit(J(l_k))
is strictly below that terminal. rankMarkedRealization_expand_total chooses
a complete witness for the requested k and retains the WHOLE family at the
unchanged first triple, so later E parameters remain unrestricted.

Remaining: I2 existence of the standard root and all complete same-endpoint
finite witnesses; linedness preservation through copy/full M_star/cut;
full M_star terminal/owner transport; the actual same-domain Steel theorem;
exact generated-domain closure and final short-key injectivity/well-ordering.
The original goal remains active and is not proved.

## Continuation update: full local closure and bounded-descent reduction

Added ScanBoundaryPreservation, CopyBoundaryPreservation,
MStarBoundaryPreservation, FullRankRealization, BoundedApplicationStep and
RankWellFoundedReduction. The full build passes with 1416 jobs.

The scan boundary proof follows the actual ScanRankReach assignments. Any
native source in row 1 would have to be a positive integer strictly below 1,
so the first native packet is empty. Later insertions preserve columns 0,1,2.
Every insertion preserves the terminal and final embedding, including a
nonempty native block at the last row. The strengthened full-scan theorem
returns all equalities on the SAME assignment as its full row/mark certificate.

Short copying preserves the first triple and terminal and has final embedding
J(j_(e-1)). The full M_star therefore has exactly that final embedding and
retains the complete finite common-endpoint witness family. A realized last
row supplies an actual critical point strictly below its terminal.

RankFullMarkedRealization now contains the entire required certificate.
All literal Step cases have full semantic lifts retaining the first triple;
cut strictly decreases the terminal and the other operations preserve it.
Given the full standard-root certificate, every literal Generated item has
a certificate in the original rank domain, with terminal at most the root's.
No semantic filter has been added to Step or Generated.

RankBoundedApplication is defined with the actual constructed rankApply,
child-first orientation, and the left embedding's critical point below the
fixed terminal. Each Step lifts to strict terminal descent or a nonempty
transitive chain of these applications; E contributes two and M_star one.
Double well-founded induction then reduces expansion well-foundedness to
the root certificate and the actual bounded-application well-foundedness
statement. These two inputs remain unproved; the conditional reduction does
not claim that I2 or Steel has been formalized.

The old source-line audit parser mistakenly read the prose 'theorem are
supplied' as a declaration. Audit.lean now enumerates theorem constants from
Lean's actual compiled environment and rejects any axiom beyond propext,
Classical.choice and Quot.sound. Its verified result is 3333 theorem constants,
including compiler-generated helpers; this broader total is not comparable
to earlier authored-declaration counts. The source scan finds no proof holes,
unsafe declarations or custom axioms. No source proof needed a new axiom.

Remaining mathematical work: the I2 standard-root existence and full witness
family; the genuine same-domain Steel theorem for rankApply; the exact
prefix-barrier comparison bridge, short-key injectivity and final I2 well-order.

## Continuation update: actual finite root and critical-sequence lining

Added RankCriticalCardinal, RankCriticalSequence, RankFiniteLining and
RootRankRealization. Full build: 1420 jobs. Compiler-environment audit: 3364
theorem constants, including generated helpers, using only propext,
Classical.choice and Quot.sound. Source scan has no proof holes or custom axioms.

Proved that a set fixed together with all its members cannot surject onto an
embedding's critical ordinal: the transported function would map a fixed input
to the new critical ordinal, contradicting its old fixed value. This yields
rankCriticalPoint_isCardinal, removing cardinality as a root premise. Critical
sequences are strictly increasing and every entry is cardinal.

Constructed actual finite lining factors F_0 = g and F_(n+1) = g(g)(F_n).
They have the same critical point, send it to the (n+1)-st critical image,
and send that point to the next one. Thus every finite critical-sequence
segment has a COMPLETE witness with its correct final endpoint. A family
of embeddings with common critical point, common first image and a prescribed
(k+1)-st image yields the full common-endpoint finite witness family.

Constructed the actual standard root with theta_i = g^i(c), owners g,g,h,h,h(h)
and h = g composed with g. This is an alternative existence witness for the
same five literal rows and marks, not a g_(11) identity or an altered syntax
system. Its unique mark is certified by equality of owner h and singleton
factor h. The k=1 endpoint embedding provides g, so the entire endpoint
family gives a full standard-root certificate. Its I2 existence is NOT proved.

Inspected Dougherty math/9503204 Theorem 2.2 and Qi arXiv:2501.06733v5
Propositions 4.8-4.9 in the original sources. Steel additionally requires
Kunen critical-sequence cofinality, inaccessible cardinal bounds and the
ordinal-hull order-type decrease. These are real missing mathematical inputs,
not consequences of the currently proved application identities alone.
FOUNDATION_REMAINING.md records the precise remaining targets and source
index issue; do not treat any of them as supplied axioms.

