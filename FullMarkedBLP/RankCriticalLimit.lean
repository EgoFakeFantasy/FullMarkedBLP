import FullMarkedBLP.RankHierarchyImage

namespace FullMarkedBLP
open FirstOrder Language

def rankEmptyFormula : membershipLanguage.Formula (Fin 1) :=
  .all ((rankMemAt (.inr 0) (.inl 0)).not)

theorem rankEmptyFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankEmptyFormula.Realize ![x] ↔ x.val = ∅ := by
  have semantics : rankEmptyFormula.Realize ![x] ↔ ∀ z : RankDomain lambda, z.val ∉ x.val := by
    simp [rankEmptyFormula, Formula.Realize, BoundedFormula.realize_all,
      BoundedFormula.realize_not, rankMemAt_realize, Fin.snoc]
  rw [semantics]
  constructor
  · intro h
    apply ZFSet.ext
    intro z
    simp only [ZFSet.notMem_empty, iff_false]
    intro hz
    exact h (rankMember x z hz) hz
  · intro same z
    rw [same]
    exact ZFSet.notMem_empty _

theorem rankOrdinalAction_zero {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) : rankOrdinalAction j ⟨0, hl.pos⟩ = ⟨0, hl.pos⟩ := by
  let zero : OrdinalDomain lambda := ⟨0, hl.pos⟩
  have result := j.map_formula rankEmptyFormula ![ordinalDomainElement zero]
  have same : j ∘ ![ordinalDomainElement zero] = ![j (ordinalDomainElement zero)] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same, rankEmptyFormula_realize, rankEmptyFormula_realize] at result
  have empty : (j (ordinalDomainElement zero)).val = ∅ := result.mpr (by simp [ordinalDomainElement, zero])
  apply Subtype.ext
  change (j (ordinalDomainElement zero)).val.rank = 0
  rw [empty, ZFSet.rank_empty]

theorem rankOrdinalAction_succ {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) (alpha : OrdinalDomain lambda) :
    (rankOrdinalAction j ⟨Order.succ alpha.val, hl.succ_lt alpha.property⟩).val =
      Order.succ (rankOrdinalAction j alpha).val := by
  let level := rankPowerset hl (rankHierarchy alpha)
  have sourceRank : level.val.rank = Order.succ alpha.val := by
    simp only [level, rankPowerset, rankHierarchy, ZFSet.rank_powerset, ZFSet.rank_vonNeumann]
  have sourceOrdinal : (⟨level.val.rank, level.property⟩ : OrdinalDomain lambda) =
      ⟨Order.succ alpha.val, hl.succ_lt alpha.property⟩ := Subtype.ext sourceRank
  have result := rankElementary_rank hl j level
  rw [sourceOrdinal] at result
  dsimp only [level] at result
  rw [rankElementary_powerset, rankElementary_hierarchy hl] at result
  exact result.symm.trans (by
    simp only [rankPowerset, rankHierarchy, ZFSet.rank_powerset, ZFSet.rank_vonNeumann])

/-- The least moved ordinal of a genuine rank elementary embedding is
a nonzero limit ordinal, as needed for weak-agreement composition. -/
theorem rankCriticalPoint_isSuccLimit {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {j : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda} (critical : RankCriticalPoint j c) :
    Order.IsSuccLimit c.val := by
  rcases Ordinal.zero_or_succ_or_isSuccLimit c.val with zero | ⟨beta, succ⟩ | limit
  · have same : c = ⟨0, hl.pos⟩ := Subtype.ext zero
    exact False.elim (critical.1 (by rw [same]; exact rankOrdinalAction_zero hl j))
  · have below : beta < c.val := by rw [← succ]; exact Order.lt_succ _
    let b : OrdinalDomain lambda := ⟨beta, below.trans c.property⟩
    have fixed := critical.2 b below
    have same : c = ⟨Order.succ b.val, hl.succ_lt b.property⟩ := Subtype.ext succ.symm
    apply False.elim
    apply critical.1
    apply Subtype.ext
    calc
      (rankOrdinalAction j c).val = Order.succ (rankOrdinalAction j b).val := by
        rw [same]
        exact rankOrdinalAction_succ hl j b
      _ = Order.succ b.val := by rw [fixed]
      _ = c.val := succ
  · exact limit

end FullMarkedBLP
