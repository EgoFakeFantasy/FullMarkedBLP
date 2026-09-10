import FullMarkedBLP.RankHierarchyGraph

namespace FullMarkedBLP
open FirstOrder Language

def rankHierarchyRecFormula : membershipLanguage.Formula (Fin 1) :=
  .all (.all ((rankGraphAppliesAt (.inl 0) (.inr 0) (.inr 1)).imp
    (.all ((rankMemAt (.inr 2) (.inr 1)).iff
      (.ex (.ex ((rankMemAt (.inr 3) (.inr 0)) ⊓
        ((rankGraphAppliesAt (.inl 0) (.inr 3) (.inr 4)) ⊓
          .all ((rankMemAt (.inr 5) (.inr 2)).imp (rankMemAt (.inr 5) (.inr 4)))))))))))

theorem rankHierarchyRecFormula_realize {lambda : Ordinal.{u}} (graph : RankDomain lambda) :
    rankHierarchyRecFormula.Realize ![graph] ↔ RankHierarchyRec graph := by
  simp [rankHierarchyRecFormula, RankHierarchyRec, Formula.Realize, BoundedFormula.realize_all,
    BoundedFormula.realize_imp, BoundedFormula.realize_iff, BoundedFormula.realize_ex,
    BoundedFormula.realize_inf, rankMemAt_realize, rankGraphAppliesAt_realize, Fin.snoc]

theorem rankElementary_hierarchyRec_iff {lambda : Ordinal.{u}} (j : RankElementaryEmbedding lambda)
    (graph : RankDomain lambda) : RankHierarchyRec (j graph) ↔ RankHierarchyRec graph := by
  have result := j.map_formula rankHierarchyRecFormula ![graph]
  have same : j ∘ ![graph] = ![j graph] := by
    funext i
    have eq : i = 0 := Fin.eq_zero i
    subst i
    rfl
  rw [same, rankHierarchyRecFormula_realize, rankHierarchyRecFormula_realize] at result
  exact result

/-- A total set graph on an ordinal domain satisfying the hierarchy
recursion has exactly the usual V_beta values. No image identification
or definability-of-rank assumption is used in the induction. -/
theorem rankHierarchyRec_unique {lambda : Ordinal.{u}}
    {graph domain range : RankDomain lambda}
    (function : rankIsFunction graph domain range) (ordinal : ZFSet.IsOrdinal domain.val)
    (recursion : RankHierarchyRec graph) (beta : OrdinalDomain lambda) :
    ∀ value : RankDomain lambda, (ordinalDomainElement beta).val ∈ domain.val →
      rankGraphApplies graph (ordinalDomainElement beta) value → value = rankHierarchy beta := by
  apply (wellFounded_lt : WellFounded ((· < ·) : OrdinalDomain lambda → OrdinalDomain lambda → Prop)).induction beta
  intro level ih value member applies
  apply Subtype.ext
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    let z' := rankMember value z hz
    obtain ⟨a, b, smaller, edge, subset⟩ := (recursion (ordinalDomainElement level) value applies z').mp hz
    obtain ⟨gamma, less, representation⟩ := Ordinal.mem_toZFSet_iff.mp smaller
    let lower : OrdinalDomain lambda := ⟨gamma, less.trans level.property⟩
    have same : ordinalDomainElement lower = a := Subtype.ext representation
    have lowerMember : (ordinalDomainElement lower).val ∈ domain.val := by
      rw [same]
      exact ordinal.mem_trans smaller member
    have valueEq := ih lower less b lowerMember (by simpa only [same] using edge)
    apply ZFSet.mem_vonNeumann'.mpr
    refine ⟨gamma, less, ?_⟩
    intro w hw
    have included := subset (rankMember z' w hw) hw
    rw [valueEq] at included
    exact included
  · intro hz
    have zBound := (ZFSet.mem_vonNeumann.mp hz).trans level.property
    let z' : RankDomain lambda := ⟨z, zBound⟩
    obtain ⟨gamma, less, subset⟩ := ZFSet.mem_vonNeumann'.mp hz
    let lower : OrdinalDomain lambda := ⟨gamma, less.trans level.property⟩
    have smaller : (ordinalDomainElement lower).val ∈ (ordinalDomainElement level).val :=
      Ordinal.toZFSet_mem_toZFSet_iff.mpr less
    have lowerMember := ordinal.mem_trans smaller member
    obtain ⟨b, _, edge, _⟩ := function.2 (ordinalDomainElement lower) lowerMember
    have valueEq := ih lower less b lowerMember edge
    apply (recursion (ordinalDomainElement level) value applies z').mpr
    refine ⟨ordinalDomainElement lower, b, smaller, edge, ?_⟩
    intro w hw
    rw [valueEq]
    exact subset hw

end FullMarkedBLP
