import FullMarkedBLP.RankRootReflection
import FullMarkedBLP.RankSyntaxData

namespace FullMarkedBLP

/-- A finite Sigma-one definition with explicitly supplied set parameters. -/
def RankSigmaOneClassDefinableAt {lambda : Ordinal.{u}} {q : Nat}
    (parameters : Fin q → RankDomain lambda) (property : RankClass lambda → Prop) : Prop :=
  ∃ (p : Nat) (matrix : RankPredicateFormula (1 + p) q), ∀ a : RankClass lambda,
    rankSigmaOneSatisfies matrix (fun _ : Fin 1 => a) parameters ↔ property a

/-- All parameters are actual sets of rank at most omega, so their
fixedness follows from a genuine critical point rather than being assumed. -/
def RankSigmaOneClassLowRankDefinable {lambda : Ordinal.{u}} (property : RankClass lambda → Prop) : Prop :=
  ∃ (q : Nat) (parameters : Fin q → RankDomain lambda),
    (∀ i, (parameters i).val.rank ≤ Ordinal.omega0) ∧ RankSigmaOneClassDefinableAt parameters property

theorem rankSigmaOne_reflect_at_fixed {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    (elementary : RankSigmaOneElementary j) {q : Nat} {parameters : Fin q → RankDomain lambda}
    (fixed : ∀ i, j (parameters i) = parameters i) {property : RankClass lambda → Prop}
    (definable : RankSigmaOneClassDefinableAt parameters property) (a : RankClass lambda) :
    property (rankClassImage j a) ↔ property a := by
  obtain ⟨p, matrix, describes⟩ := definable
  have transfer := elementary 1 q p matrix (fun _ => a) parameters
  have same : j ∘ parameters = parameters := funext fixed
  rw [same] at transfer
  exact (describes _).symm.trans (transfer.trans (describes _))

theorem rankSigmaOne_reflect_lowRank {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint j critical) (elementary : RankSigmaOneElementary j)
    {property : RankClass lambda → Prop} (definable : RankSigmaOneClassLowRankDefinable property)
    (a : RankClass lambda) : property (rankClassImage j a) ↔ property a := by
  obtain ⟨q, parameters, small, describes⟩ := definable
  exact rankSigmaOne_reflect_at_fixed elementary
    (fun i => rankCriticalPoint_fixes_rank hl cp ((small i).trans_lt (rankCriticalPoint_omega_lt hl cp))) describes a

theorem rankApplicationRootReflection_of_lowRank_definability {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {base : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint base critical) (elementary : RankSigmaOneElementary base)
    (definable : ∀ n, RankSigmaOneClassLowRankDefinable (RankRootExists hl n)) :
    RankApplicationRootReflection hl base := by
  intro n current currentCritical currentCp power
  have imageRoot : RankRootExists hl n (rankClassImage base (rankEmbeddingClassGraph current)) := by
    refine ⟨current, currentCritical, currentCp, ?_⟩
    rw [power, rankClassImage_embeddingGraph hl]
  obtain ⟨next, nextCritical, nextCp, equation⟩ :=
    (rankSigmaOne_reflect_lowRank hl cp elementary (definable n) (rankEmbeddingClassGraph current)).mp imageRoot
  exact ⟨next, nextCritical, nextCp, (rankEmbeddingClassGraph_injective hl equation).symm⟩

theorem rankCoherentRoots_of_sigmaTwo_and_lowRank_definability {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {base : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint base critical) (elementary : RankSigmaTwoElementary base)
    (definable : ∀ n, RankSigmaOneClassLowRankDefinable (RankRootExists hl n)) :
    ∃ roots : RankCoherentRoots hl, roots.embedding 0 = base :=
  rankCoherentRoots_of_reflection hl cp
    (rankApplicationRootReflection_of_lowRank_definability hl cp
      (rankSigmaTwoElementary_sigmaOne elementary) definable)

end FullMarkedBLP
