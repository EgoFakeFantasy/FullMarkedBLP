import FullMarkedBLP.RankRootTermMatrix
import FullMarkedBLP.RankSteelWellFounded

namespace FullMarkedBLP

/-- The actual coherent root sequence now follows from Sigma-two
elementarity alone, with the finite expressibility theorem discharged. -/
theorem exists_rankCoherentRoots_of_sigmaTwo {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {base : RankElementaryEmbedding lambda} {critical : OrdinalDomain lambda}
    (cp : RankCriticalPoint base critical) (elementary : RankSigmaTwoElementary base) :
    ∃ roots : RankCoherentRoots hl, roots.embedding 0 = base := by
  have hw : Ordinal.omega0 < lambda := (rankCriticalPoint_omega_lt hl cp).trans critical.property
  exact exists_rankCoherentRoots_of_sigmaTwo_and_lowRank_definability hl cp elementary
    (rankRootExists_lowRankDefinable hl hw)

/-- The source's standard rank formulation of I2 gives the complete
common-endpoint witness family and a full realization of the unchanged root. -/
theorem exists_full_root_of_rankI2 (i2 : RankI2.{u}) :
    ∃ (lambda : Ordinal.{u}) (_hl : Order.IsSuccLimit lambda)
      (theta : Nat → OrdinalDomain lambda) (embedding : Nat → RankElementaryEmbedding lambda),
      RankFullMarkedRealization start theta embedding := by
  obtain ⟨lambda, hl, base, critical, cp, elementary⟩ := i2
  obtain ⟨roots, _⟩ := exists_rankCoherentRoots_of_sigmaTwo hl cp elementary
  obtain ⟨theta, embedding, realized, _⟩ := roots.full_root
  exact ⟨lambda, hl, theta, embedding, realized⟩

theorem rankI2_start_accessible (i2 : RankI2.{u}) :
    Acc (fun child parent => Step parent child) start := by
  obtain ⟨lambda, hl, theta, embedding, root⟩ := exists_full_root_of_rankI2 i2
  exact rankFullMarkedRealization_accessible_actual hl root

/-- Manuscript Theorem 4.1 for the exact ordinary E/M_star generated
domain. This is the expansion component; ShortKeyWellOrder proves the
comparison well-order and short-key injectivity from it. -/
theorem rankI2_generatedStep_wellFounded (i2 : RankI2.{u}) :
    WellFounded (fun (child parent : {a : Pattern // Generated a}) => Step parent.val child.val) := by
  obtain ⟨lambda, hl, theta, embedding, root⟩ := exists_full_root_of_rankI2 i2
  exact generatedStep_wellFounded_of_root hl root

end FullMarkedBLP
