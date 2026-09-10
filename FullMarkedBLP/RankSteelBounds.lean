import FullMarkedBLP.RankKunenCofinality

namespace FullMarkedBLP

/-- A nontrivial limit rank domain is a singular strong-limit cardinal of
cofinality omega. The equalities now use the proved Kunen cofinality theorem. -/
theorem rankDomain_cardinal_of_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    lambda.card.ord = lambda := by
  rw [← rankCriticalSupremum_eq_domain hl cp]
  exact rankCriticalSupremum_cardinal hl cp

theorem rankDomain_cof_of_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    lambda.cof = Cardinal.aleph0 := by
  rw [← rankCriticalSupremum_eq_domain hl cp]
  exact rankCriticalSupremum_cof cp

theorem rankDomain_strongLimit_of_criticalPoint {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical) :
    Cardinal.IsStrongLimit lambda.card := by
  rw [← rankCriticalSupremum_eq_domain hl cp]
  exact rankCriticalSupremum_isStrongLimit hl cp

/-- Steel's inaccessible bound may be chosen as a genuine critical image
above any prescribed ordinal in the same domain. The actual embedding with
that critical point also supplies every needed small-hierarchy estimate. -/
theorem rankDomain_inaccessible_above {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (bound : OrdinalDomain lambda) :
    ∃ gamma : OrdinalDomain lambda, bound < gamma ∧
      Cardinal.IsInaccessible gamma.val.card ∧
      ∃ owner : RankElementaryEmbedding lambda, RankCriticalPoint owner gamma ∧
        ∀ alpha : OrdinalDomain lambda, alpha < gamma →
          (rankHierarchy alpha).val.card < gamma.val.card := by
  obtain ⟨n, above⟩ := rankCriticalSequence_cofinal hl cp bound
  refine ⟨rankCriticalSequence j critical n, above, rankCriticalSequence_isInaccessible hl cp n,
    rankCriticalSequenceEmbedding hl j n, rankCriticalSequenceEmbedding_criticalPoint hl cp n, ?_⟩
  exact fun alpha below => rankCriticalSequence_hierarchy_card_lt hl cp n alpha below

/-- If crit(j) < gamma < lambda, some alpha < gamma has j(alpha) at least
gamma. Otherwise the whole critical sequence would remain below gamma,
contradicting Kunen cofinality. -/
theorem rankOrdinalAction_crosses_bound {lambda : Ordinal.{u}}
    (hl : Order.IsSuccLimit lambda) {j : RankElementaryEmbedding lambda}
    {critical : OrdinalDomain lambda} (cp : RankCriticalPoint j critical)
    (gamma : OrdinalDomain lambda) (below : critical < gamma) :
    ∃ alpha : OrdinalDomain lambda, alpha < gamma ∧ gamma ≤ rankOrdinalAction j alpha := by
  classical
  by_contra failure
  have closed : ∀ alpha : OrdinalDomain lambda, alpha < gamma → rankOrdinalAction j alpha < gamma := by
    intro alpha ha
    apply lt_of_not_ge
    exact fun crosses => failure ⟨alpha, ha, crosses⟩
  have bounded : ∀ n, rankCriticalSequence j critical n < gamma := by
    intro n
    induction n with
    | zero => exact below
    | succ n ih => exact closed _ ih
  obtain ⟨n, above⟩ := rankCriticalSequence_cofinal hl cp gamma
  exact (lt_asymm above) (bounded n)

end FullMarkedBLP
