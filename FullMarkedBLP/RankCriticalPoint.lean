import FullMarkedBLP.OrdinalAction

namespace FullMarkedBLP

def RankCriticalPoint {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (c : OrdinalDomain lambda) : Prop :=
  rankOrdinalAction j c ≠ c ∧ ∀ x, x < c → rankOrdinalAction j x = x

theorem rankCriticalPoint_exists {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (hmoved : ∃ x, rankOrdinalAction j x ≠ x) : ∃ c, RankCriticalPoint j c := by
  classical
  obtain ⟨c, hc, hmin⟩ := (wellFounded_lt : WellFounded ((· < ·) : OrdinalDomain lambda → OrdinalDomain lambda → Prop)).has_min
    {x | rankOrdinalAction j x ≠ x} hmoved
  refine ⟨c, hc, ?_⟩
  intro x hx
  by_contra hne
  exact hmin x hne hx

theorem rankCriticalPoint_unique {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    {c d : OrdinalDomain lambda} (hc : RankCriticalPoint j c) (hd : RankCriticalPoint j d) : c = d := by
  rcases lt_trichotomy c d with h | h | h
  · exact False.elim (hc.1 (hd.2 c h))
  · exact h
  · exact False.elim (hd.1 (hc.2 d h))

theorem rankCriticalPoint_lt_image {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    {c : OrdinalDomain lambda} (hc : RankCriticalPoint j c) : c < rankOrdinalAction j c :=
  rankOrdinalAction_moved_up j hc.1

theorem rankCriticalPoint_le_moved {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    {c x : OrdinalDomain lambda} (hc : RankCriticalPoint j c) (hx : rankOrdinalAction j x ≠ x) : c ≤ x := by
  by_contra h
  exact hx (hc.2 x (lt_of_not_ge h))

theorem rankCriticalPoint_fixed_set {lambda : Ordinal.{u}} {j : RankElementaryEmbedding lambda}
    {c x : OrdinalDomain lambda} (hc : RankCriticalPoint j c) (hx : x < c) :
    j (ordinalDomainElement x) = ordinalDomainElement x := by
  rw [← ordinalDomainElement_action, hc.2 x hx]

/-- Composition has the smaller critical point; inflationarity prevents either
    factor from undoing the movement made by the other. -/
theorem rankCriticalPoint_comp {lambda : Ordinal.{u}} {j k : RankElementaryEmbedding lambda}
    {c d : OrdinalDomain lambda} (hc : RankCriticalPoint j c) (hd : RankCriticalPoint k d) :
    RankCriticalPoint (j.comp k) (min c d) := by
  constructor
  · have hlt : min c d < rankOrdinalAction (j.comp k) (min c d) := by
      rw [rankOrdinalAction_comp]
      by_cases hcd : c ≤ d
      · rw [min_eq_left hcd]
        exact (rankCriticalPoint_lt_image hc).trans_le
          (rankOrdinalAction_monotone j (rankOrdinalAction_le_self_image k c))
      · rw [min_eq_right (le_of_not_ge hcd)]
        exact (rankCriticalPoint_lt_image hd).trans_le
          (rankOrdinalAction_le_self_image j (rankOrdinalAction k d))
    exact ne_of_gt hlt
  · intro x hx
    obtain ⟨hxc, hxd⟩ := lt_min_iff.mp hx
    rw [rankOrdinalAction_comp, hd.2 x hxd, hc.2 x hxc]

end FullMarkedBLP

