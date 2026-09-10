import FullMarkedBLP.RankCriticalLimit

namespace FullMarkedBLP
open FirstOrder Language

/-- The membership condition for a nonzero limit ordinal. Ordinality is
handled separately, so the condition is a particularly small formula. -/
def rankIsNonzeroLimit {lambda : Ordinal.{u}} (x : RankDomain lambda) : Prop :=
  (∃ z : RankDomain lambda, z.val ∈ x.val) ∧
    ∀ z : RankDomain lambda, z.val ∈ x.val →
      ∃ w : RankDomain lambda, w.val ∈ x.val ∧ z.val ∈ w.val

def rankNonzeroLimitFormula : membershipLanguage.Formula (Fin 1) :=
  (.ex (rankMemAt (.inr 0) (.inl 0))) ⊓
    .all ((rankMemAt (.inr 0) (.inl 0)).imp
      (.ex (rankMemAt (.inr 1) (.inl 0) ⊓ rankMemAt (.inr 0) (.inr 1))))

theorem rankNonzeroLimitFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankNonzeroLimitFormula.Realize ![x] ↔ rankIsNonzeroLimit x := by
  simp [rankNonzeroLimitFormula, Formula.Realize, BoundedFormula.Realize,
    rankMemAt_realize, rankIsNonzeroLimit, Fin.snoc, and_assoc, and_comm]

theorem rankIsNonzeroLimit_ordinal_iff {lambda : Ordinal.{u}} (o : OrdinalDomain lambda) :
    rankIsNonzeroLimit (ordinalDomainElement o) ↔ Order.IsSuccLimit o.val := by
  constructor
  · rintro ⟨⟨z, hz⟩, cofinal⟩
    rw [Ordinal.isSuccLimit_iff, Order.isSuccPrelimit_iff_succ_lt]
    refine ⟨?_, ?_⟩
    · intro zero
      have below : z.val.rank < o.val := by
        simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hz
      rw [zero] at below
      exact (not_lt_of_ge zero_le) below
    · intro a ha
      let input := ordinalDomainElement (⟨a, ha.trans o.property⟩ : OrdinalDomain lambda)
      obtain ⟨w, hw, above⟩ := cofinal input (Ordinal.toZFSet_mem_toZFSet_iff.mpr ha)
      have lower : a < w.val.rank := by
        simpa only [input, ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem above
      have upper : w.val.rank < o.val := by
        simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using ZFSet.rank_lt_of_mem hw
      exact (Order.succ_le_of_lt lower).trans_lt upper
  · intro limit
    refine ⟨⟨ordinalDomainElement ⟨0, limit.pos.trans o.property⟩,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr limit.pos⟩, ?_⟩
    intro z hz
    obtain ⟨a, ha, eqZ⟩ := Ordinal.mem_toZFSet_iff.mp hz
    let output := ordinalDomainElement (⟨Order.succ a,
      (limit.succ_lt ha).trans o.property⟩ : OrdinalDomain lambda)
    refine ⟨output, Ordinal.toZFSet_mem_toZFSet_iff.mpr (limit.succ_lt ha), ?_⟩
    change z.val ∈ (Order.succ a).toZFSet
    rw [← eqZ]
    exact Ordinal.toZFSet_mem_toZFSet_iff.mpr (Order.lt_succ a)

def rankNonzeroLimitAt {alpha : Type} {n : Nat} (x : alpha ⊕ Fin n) :
    membershipLanguage.BoundedFormula alpha n :=
  BoundedFormula.relabel ![x] rankNonzeroLimitFormula

theorem rankNonzeroLimitAt_realize {lambda : Ordinal.{u}} {alpha : Type} {n : Nat}
    (x : alpha ⊕ Fin n) (v : alpha → RankDomain lambda) (xs : Fin n → RankDomain lambda) :
    (rankNonzeroLimitAt x).Realize v xs ↔ rankIsNonzeroLimit (Sum.elim v xs x) := by
  simp only [rankNonzeroLimitAt, BoundedFormula.realize_relabel]
  change rankNonzeroLimitFormula.Realize (Sum.elim v xs ∘ ![x]) ↔ _
  have same : Sum.elim v xs ∘ ![x] = ![Sum.elim v xs x] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same]
  exact rankNonzeroLimitFormula_realize _

def rankIsFirstLimit {lambda : Ordinal.{u}} (x : RankDomain lambda) : Prop :=
  rankIsNonzeroLimit x ∧ ∀ y : RankDomain lambda, y.val ∈ x.val → ¬rankIsNonzeroLimit y

def rankFirstLimitFormula : membershipLanguage.Formula (Fin 1) :=
  rankNonzeroLimitFormula ⊓
    .all ((rankMemAt (.inr 0) (.inl 0)).imp (rankNonzeroLimitAt (.inr 0)).not)

theorem rankFirstLimitFormula_realize {lambda : Ordinal.{u}} (x : RankDomain lambda) :
    rankFirstLimitFormula.Realize ![x] ↔ rankIsFirstLimit x := by
  change (rankNonzeroLimitFormula ⊓ _).Realize ![x] ↔ _
  simp only [Formula.Realize, BoundedFormula.realize_inf]
  change (rankNonzeroLimitFormula.Realize ![x] ∧ _) ↔ _
  rw [rankNonzeroLimitFormula_realize]
  simp [rankIsFirstLimit, BoundedFormula.Realize, rankMemAt_realize,
    rankNonzeroLimitAt_realize, Fin.snoc]

theorem rankIsFirstLimit_omega {lambda : Ordinal.{u}} (hw : Ordinal.omega0 < lambda) :
    rankIsFirstLimit (ordinalDomainElement (⟨Ordinal.omega0, hw⟩ : OrdinalDomain lambda)) := by
  refine ⟨(rankIsNonzeroLimit_ordinal_iff _).mpr Ordinal.isSuccLimit_omega0, ?_⟩
  intro y hy limit
  obtain ⟨a, below, eqY⟩ := Ordinal.mem_toZFSet_iff.mp hy
  let ordinal : OrdinalDomain lambda := ⟨a, below.trans hw⟩
  have same : ordinalDomainElement ordinal = y := Subtype.ext eqY
  rw [← same] at limit
  have above := Ordinal.omega0_le_of_isSuccLimit ((rankIsNonzeroLimit_ordinal_iff ordinal).mp limit)
  exact (not_lt_of_ge above) below

/-- Every elementary rank embedding fixes omega whenever omega belongs to
its domain: omega is defined as the first nonzero limit ordinal. -/
theorem rankOrdinalAction_omega {lambda : Ordinal.{u}} (hw : Ordinal.omega0 < lambda)
    (j : RankElementaryEmbedding lambda) :
    rankOrdinalAction j ⟨Ordinal.omega0, hw⟩ = ⟨Ordinal.omega0, hw⟩ := by
  let ordinal : OrdinalDomain lambda := ⟨Ordinal.omega0, hw⟩
  let source := ordinalDomainElement ordinal
  have result := j.map_formula rankFirstLimitFormula ![source]
  have same : j ∘ ![source] = ![j source] := by
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same, rankFirstLimitFormula_realize, rankFirstLimitFormula_realize] at result
  have first := result.mpr (rankIsFirstLimit_omega hw)
  apply le_antisymm
  · apply le_of_not_gt
    intro moved
    have member : source.val ∈ (j source).val := by
      change ordinal.val.toZFSet ∈ (j (ordinalDomainElement ordinal)).val
      rw [rankOrdinalAction_compat]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr moved
    exact first.2 source member (rankIsFirstLimit_omega hw).1
  · exact rankOrdinalAction_le_self_image j ordinal

end FullMarkedBLP
