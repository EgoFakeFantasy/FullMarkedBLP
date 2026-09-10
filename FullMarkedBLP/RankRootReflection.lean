import FullMarkedBLP.RankSecondOrder
import FullMarkedBLP.RankCoherentRoots

namespace FullMarkedBLP

/-- Definability by an actual finite Sigma-one formula with one free class
parameter. This is an expressibility obligation, not an elementarity axiom. -/
def RankSigmaOneClassDefinable {lambda : Ordinal.{u}} (property : RankClass lambda → Prop) : Prop :=
  ∃ (p : Nat) (matrix : RankPredicateFormula (1 + p) 0),
    ∀ a : RankClass lambda, rankSigmaOneSatisfies matrix (fun _ : Fin 1 => a) Fin.elim0 ↔ property a

theorem rankSigmaOne_reflect_definable {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    (elementary : RankSigmaOneElementary j) {property : RankClass lambda → Prop}
    (definable : RankSigmaOneClassDefinable property) (a : RankClass lambda) :
    property (rankClassImage j a) ↔ property a := by
  obtain ⟨p, matrix, describes⟩ := definable
  have transfer := elementary 1 0 p matrix (fun _ => a) Fin.elim0
  have empty : j ∘ (Fin.elim0 : Fin 0 → RankDomain lambda) = Fin.elim0 := by
    funext i
    exact Fin.elim0 i
  rw [empty] at transfer
  change rankSigmaOneSatisfies matrix (fun _ : Fin 1 => rankClassImage j a) Fin.elim0 ↔
    rankSigmaOneSatisfies matrix (fun _ : Fin 1 => a) Fin.elim0 at transfer
  exact (describes _).symm.trans (transfer.trans (describes _))

def RankRootExists {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (n : Nat) (graph : RankClass lambda) : Prop :=
  ∃ (j : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda),
    RankCriticalPoint j critical ∧
      rankEmbeddingClassGraph (rankApply hl (rankCriticalSequenceEmbedding hl j n) j) = graph

def RankApplicationRootReflection {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (base : RankElementaryEmbedding lambda) : Prop :=
  ∀ (n : Nat) (current : RankElementaryEmbedding lambda) (critical : OrdinalDomain lambda),
    RankCriticalPoint current critical → rankCriticalSequenceEmbedding hl current n = base →
      ∃ (next : RankElementaryEmbedding lambda) (nextCritical : OrdinalDomain lambda),
        RankCriticalPoint next nextCritical ∧
          current = rankApply hl (rankCriticalSequenceEmbedding hl next n) next

/-- The reflection step in the source proof. The missing ingredient is
explicitly the finite-formula definability of elementary embedding roots. -/
theorem rankApplicationRootReflection_of_sigmaOne {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {base : RankElementaryEmbedding lambda} (elementary : RankSigmaOneElementary base)
    (definable : ∀ n, RankSigmaOneClassDefinable (RankRootExists hl n)) :
    RankApplicationRootReflection hl base := by
  intro n current critical cp power
  have imageRoot : RankRootExists hl n (rankClassImage base (rankEmbeddingClassGraph current)) := by
    refine ⟨current, critical, cp, ?_⟩
    rw [power, rankClassImage_embeddingGraph hl]
  obtain ⟨next, nextCritical, nextCp, equation⟩ :=
    (rankSigmaOne_reflect_definable elementary (definable n) (rankEmbeddingClassGraph current)).mp imageRoot
  exact ⟨next, nextCritical, nextCp, (rankEmbeddingClassGraph_injective hl equation).symm⟩

/-- Construct the infinite coherent sequence by recursive choices, keeping
the base-power invariant at every stage. -/
theorem exists_rankCoherentRoots_of_reflection {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {base : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint base critical) (reflection : RankApplicationRootReflection hl base) :
    ∃ roots : RankCoherentRoots hl, roots.embedding 0 = base := by
  classical
  let Stage (n : Nat) := {j : RankElementaryEmbedding lambda // ∃ c : OrdinalDomain lambda,
    RankCriticalPoint j c ∧ rankCriticalSequenceEmbedding hl j n = base}
  have extend : ∀ (n : Nat) (stage : Stage n), ∃ next : Stage (n + 1),
      stage.val = rankApply hl (rankCriticalSequenceEmbedding hl next.val n) next.val := by
    intro n stage
    obtain ⟨c, stageCp, stagePower⟩ := stage.property
    obtain ⟨next, nextCritical, nextCp, equation⟩ := reflection n stage.val c stageCp stagePower
    have nextPower : rankCriticalSequenceEmbedding hl next (n + 1) = base := by
      calc
        rankCriticalSequenceEmbedding hl next (n + 1) =
            rankCriticalSequenceEmbedding hl (rankApply hl (rankCriticalSequenceEmbedding hl next n) next) n :=
          (rankCriticalSequenceEmbedding_root_identity hl next n).symm
        _ = rankCriticalSequenceEmbedding hl stage.val n := by rw [← equation]
        _ = base := stagePower
    exact ⟨⟨next, nextCritical, nextCp, nextPower⟩, equation⟩
  let next (n : Nat) (stage : Stage n) : Stage (n + 1) := Classical.choose (extend n stage)
  let stages : (n : Nat) → Stage n := Nat.rec ⟨base, critical, cp, rfl⟩ next
  let roots : RankCoherentRoots hl := {
    embedding := fun n => (stages n).val
    critical := fun n => Classical.choose (stages n).property
    criticalPoint := fun n => (Classical.choose_spec (stages n).property).1
    coherent := fun n => Classical.choose_spec (extend n (stages n)) }
  exact ⟨roots, rfl⟩

theorem exists_rankCoherentRoots_of_sigmaTwo_and_definability {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {base : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint base critical) (elementary : RankSigmaTwoElementary base)
    (definable : ∀ n, RankSigmaOneClassDefinable (RankRootExists hl n)) :
    ∃ roots : RankCoherentRoots hl, roots.embedding 0 = base :=
  exists_rankCoherentRoots_of_reflection hl cp
    (rankApplicationRootReflection_of_sigmaOne hl (rankSigmaTwoElementary_sigmaOne elementary) definable)

end FullMarkedBLP
