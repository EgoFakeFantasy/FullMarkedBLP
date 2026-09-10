import FullMarkedBLP.OrdinalDefinability

namespace FullMarkedBLP

abbrev OrdinalDomain (lambda : Ordinal.{u}) := {o : Ordinal.{u} // o < lambda}

noncomputable def ordinalDomainElement {lambda : Ordinal.{u}} (o : OrdinalDomain lambda) : RankDomain lambda :=
  ⟨o.val.toZFSet, by simpa only [Ordinal.rank_toZFSet] using o.property⟩

noncomputable def rankOrdinalAction {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (o : OrdinalDomain lambda) : OrdinalDomain lambda :=
  ⟨(j (ordinalDomainElement o)).val.rank, (j (ordinalDomainElement o)).property⟩

theorem rankOrdinalAction_compat {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (o : OrdinalDomain lambda) :
    (j (ordinalDomainElement o)).val = (rankOrdinalAction j o).val.toZFSet := by
  have ho : ZFSet.IsOrdinal (ordinalDomainElement o).val := ZFSet.isOrdinal_toZFSet o.val
  exact ((rankElementary_isOrdinal_iff j (ordinalDomainElement o)).mpr ho).toZFSet_rank_eq.symm

theorem rankOrdinalAction_lt_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (a b : OrdinalDomain lambda) : rankOrdinalAction j a < rankOrdinalAction j b ↔ a < b := by
  change (rankOrdinalAction j a).val < (rankOrdinalAction j b).val ↔ a.val < b.val
  rw [← Ordinal.toZFSet_mem_toZFSet_iff, ← rankOrdinalAction_compat j a, ← rankOrdinalAction_compat j b]
  exact (rankElementary_mem_iff j (ordinalDomainElement a) (ordinalDomainElement b)).trans
    Ordinal.toZFSet_mem_toZFSet_iff

theorem rankOrdinalAction_strictMono {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda) :
    StrictMono (rankOrdinalAction j) := fun a b h => (rankOrdinalAction_lt_iff j a b).mpr h

theorem rankOrdinalAction_monotone {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda) :
    Monotone (rankOrdinalAction j) := (rankOrdinalAction_strictMono j).monotone

theorem rankOrdinalAction_le_self_image {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (o : OrdinalDomain lambda) :
    o ≤ rankOrdinalAction j o := (rankOrdinalAction_strictMono j).le_apply

theorem rankOrdinalAction_moved_up {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) {o : OrdinalDomain lambda}
    (h : rankOrdinalAction j o ≠ o) : o < rankOrdinalAction j o := by
  exact lt_of_le_of_ne (rankOrdinalAction_le_self_image j o) h.symm

theorem ordinalDomainElement_action {lambda : Ordinal.{u}}
    (j : RankElementaryEmbedding lambda) (o : OrdinalDomain lambda) :
    ordinalDomainElement (rankOrdinalAction j o) = j (ordinalDomainElement o) := by
  apply Subtype.ext
  exact (rankOrdinalAction_compat j o).symm

theorem rankOrdinalAction_comp {lambda : Ordinal.{u}}
    (j k : RankElementaryEmbedding lambda) (o : OrdinalDomain lambda) :
    rankOrdinalAction (j.comp k) o = rankOrdinalAction j (rankOrdinalAction k o) := by
  apply Subtype.ext
  change (j (k (ordinalDomainElement o))).val.rank =
    (j (ordinalDomainElement (rankOrdinalAction k o))).val.rank
  rw [ordinalDomainElement_action]

end FullMarkedBLP


