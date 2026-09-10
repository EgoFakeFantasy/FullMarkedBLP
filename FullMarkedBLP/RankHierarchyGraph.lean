import FullMarkedBLP.RankImageCofinality

namespace FullMarkedBLP

/-- The initial hierarchy sequence on the ordinals below upper, bounded
as a set-valued function by V_upper. -/
noncomputable def rankHierarchyMember {lambda : Ordinal.{u}} (upper : OrdinalDomain lambda) :
    (ordinalDomainElement upper).val → (rankHierarchy upper).val := fun a =>
  ⟨ZFSet.vonNeumann a.val.rank, ZFSet.mem_vonNeumann.mpr (by
    rw [ZFSet.rank_vonNeumann]
    have bound := ZFSet.rank_lt_of_mem a.property
    simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using bound)⟩

noncomputable def rankHierarchyGraph {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (upper : OrdinalDomain lambda) : RankDomain lambda :=
  ⟨zfFunctionGraph (rankHierarchyMember upper), rank_function_lt_of_limit hl
    (ordinalDomainElement upper).property (rankHierarchy upper).property
    (zfFunctionGraph_isFunc (rankHierarchyMember upper))⟩

theorem rankHierarchyGraph_isFunction {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (upper : OrdinalDomain lambda) :
    rankIsFunction (rankHierarchyGraph hl upper) (ordinalDomainElement upper) (rankHierarchy upper) :=
  (rankIsFunction_iff hl _ _ _).mpr (zfFunctionGraph_isFunc (rankHierarchyMember upper))

theorem rankHierarchyGraph_applies_iff {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (upper : OrdinalDomain lambda) (i value : RankDomain lambda) :
    rankGraphApplies (rankHierarchyGraph hl upper) i value ↔
      i.val ∈ upper.val.toZFSet ∧ value.val = ZFSet.vonNeumann i.val.rank := by
  rw [rankGraphApplies_iff hl]
  change ZFSet.pair i.val value.val ∈ zfFunctionGraph (rankHierarchyMember upper) ↔ _
  rw [mem_zfFunctionGraph]
  constructor
  · rintro ⟨member, image⟩
    exact ⟨member, image.symm⟩
  · rintro ⟨member, image⟩
    exact ⟨member, image.symm⟩

theorem rankHierarchyGraph_at {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    {upper beta : OrdinalDomain lambda} (below : beta < upper) :
    rankGraphApplies (rankHierarchyGraph hl upper) (ordinalDomainElement beta) (rankHierarchy beta) := by
  apply (rankHierarchyGraph_applies_iff hl upper _ _).mpr
  exact ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr below, by simp only [ordinalDomainElement, rankHierarchy, Ordinal.rank_toZFSet]⟩

/-- The hierarchy recursion, expressed entirely through members of the
ambient rank domain and graph application. -/
def RankHierarchyRec {lambda : Ordinal.{u}} (graph : RankDomain lambda) : Prop :=
  ∀ i value : RankDomain lambda, rankGraphApplies graph i value →
    ∀ z : RankDomain lambda, z.val ∈ value.val ↔
      ∃ a b : RankDomain lambda, a.val ∈ i.val ∧ rankGraphApplies graph a b ∧
        ∀ w : RankDomain lambda, w.val ∈ z.val → w.val ∈ b.val

theorem rankHierarchyGraph_recursion {lambda : Ordinal.{u}} (hl : Order.IsSuccLimit lambda)
    (upper : OrdinalDomain lambda) : RankHierarchyRec (rankHierarchyGraph hl upper) := by
  intro i value applies z
  obtain ⟨member, image⟩ := (rankHierarchyGraph_applies_iff hl upper i value).mp applies
  obtain ⟨beta, below, representation⟩ := Ordinal.mem_toZFSet_iff.mp member
  let level : OrdinalDomain lambda := ⟨beta, below.trans upper.property⟩
  have same : ordinalDomainElement level = i := Subtype.ext representation
  subst i
  simp only [ordinalDomainElement, Ordinal.rank_toZFSet] at image
  rw [image]
  constructor
  · intro hz
    obtain ⟨gamma, less, subset⟩ := ZFSet.mem_vonNeumann'.mp hz
    let lower : OrdinalDomain lambda := ⟨gamma, less.trans level.property⟩
    refine ⟨ordinalDomainElement lower, rankHierarchy lower,
      Ordinal.toZFSet_mem_toZFSet_iff.mpr less, rankHierarchyGraph_at hl (less.trans below), ?_⟩
    intro w hw
    exact subset hw
  · rintro ⟨a, b, smaller, edge, subset⟩
    have bound := ZFSet.rank_lt_of_mem smaller
    have less : a.val.rank < beta := by simpa only [ordinalDomainElement, Ordinal.rank_toZFSet] using bound
    have valueEq := ((rankHierarchyGraph_applies_iff hl upper a b).mp edge).2
    apply ZFSet.mem_vonNeumann'.mpr
    refine ⟨a.val.rank, less, ?_⟩
    intro w hw
    rw [← valueEq]
    exact subset (rankMember z w hw) hw

end FullMarkedBLP
