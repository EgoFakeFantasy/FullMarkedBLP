import FullMarkedBLP.RankApplication

namespace FullMarkedBLP
open FirstOrder Language

def RankGraphFixesBelow {lambda : Ordinal.{u}} (graph bound : RankDomain lambda) : Prop :=
  ∀ x y : RankDomain lambda, x.val ∈ bound.val → rankGraphApplies graph x y → y = x

def rankGraphFixesBelowFormula : membershipLanguage.Formula (Fin 2) :=
  .all (.all ((rankMemAt (.inr 0) (.inl 1)).imp
    ((rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 1)).imp
      (.equal (.var (.inr 1)) (.var (.inr 0))))))

theorem rankGraphFixesBelowFormula_realize {lambda : Ordinal.{u}} (graph bound : RankDomain lambda) :
    rankGraphFixesBelowFormula.Realize ![graph, bound] ↔ RankGraphFixesBelow graph bound := by
  simp [rankGraphFixesBelowFormula, RankGraphFixesBelow, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.Realize, rankMemAt_realize, rankGraphAppliesAt_realize, Fin.snoc]

theorem rankElementary_graphFixesBelow_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (graph bound : RankDomain lambda) :
    RankGraphFixesBelow (j graph) (j bound) ↔ RankGraphFixesBelow graph bound := by
  have result := j.map_formula rankGraphFixesBelowFormula ![graph, bound]
  have same : j ∘ ![graph, bound] = ![j graph, j bound] := by
    funext i
    rcases i with ⟨i, hi⟩
    match i with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => omega
  rw [same, rankGraphFixesBelowFormula_realize, rankGraphFixesBelowFormula_realize] at result
  exact result

theorem rankRestrictionGraph_fixesBelow_critical {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {k : RankElementaryEmbedding lambda} {c : OrdinalDomain lambda} (critical : RankCriticalPoint k c)
    (domain : RankDomain lambda) : RankGraphFixesBelow (rankRestrictionGraph hl k domain) (ordinalDomainElement c) := by
  intro x y hx applies
  obtain ⟨beta, below, representation⟩ := Ordinal.mem_toZFSet_iff.mp hx
  let b : OrdinalDomain lambda := ⟨beta, below.trans c.property⟩
  have same : ordinalDomainElement b = x := Subtype.ext representation
  have fixed : k x = x := by
    rw [← same]
    exact rankCriticalPoint_fixed_set critical below
  exact ((rankRestrictionGraph_applies_iff hl k domain x y).mp applies).2.symm.trans fixed

/-- Application transports the actual least moved ordinal to its image. -/
theorem rankApply_criticalPoint {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (j : RankElementaryEmbedding lambda) {k : RankElementaryEmbedding lambda}
    {c : OrdinalDomain lambda} (critical : RankCriticalPoint k c) :
    RankCriticalPoint (rankApply hl j k) (rankOrdinalAction j c) := by
  constructor
  · intro fixed
    have same := (rankApply_ordinal_image hl j k c).symm.trans fixed
    exact critical.1 ((rankOrdinalAction_strictMono j).injective same)
  · intro b below
    obtain ⟨domain, applies⟩ := rankApply_spec hl j k (ordinalDomainElement b)
    have fixed := (rankElementary_graphFixesBelow_iff j _ _).mpr
      (rankRestrictionGraph_fixesBelow_critical hl critical domain)
    have member : (ordinalDomainElement b).val ∈ (j (ordinalDomainElement c)).val := by
      rw [rankOrdinalAction_compat]
      exact Ordinal.toZFSet_mem_toZFSet_iff.mpr below
    have point := fixed (ordinalDomainElement b) (rankApply hl j k (ordinalDomainElement b)) member applies
    apply Subtype.ext
    change (rankApply hl j k (ordinalDomainElement b)).val.rank = b.val
    rw [point]
    exact Ordinal.rank_toZFSet b.val

end FullMarkedBLP
